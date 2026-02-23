/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Mathlib
public import Cslib.Foundations.Control.Monad.Free.Fold
public import Cslib.AlgorithmsTheory.Lean.TimeM

@[expose] public section

/-
# Query model

This file defines a simple query language modeled as a free monad over a
parametric type of query operations.

## Main definitions

- `PureCosts`  : A typeclass that every model needs to log or cost pure monadic operations
- `Model Q c` : A model type for a query type `Q : Type u → Type u` and cost type `c`
- `Prog Q α` : The type of programs of query type `Q` and return type `α`. This is a free monad
      under the hood
- `eval`, `time` : concrete execution semantics of a `Prog Q α` for a given model of `Q`


## How to set up an algorithm

This model is a lightweight framework for specifying and verifying both the correctness
and complexity of algorithms in lean. To specify an algorithm, one must:
1. Define an inductive type of queries which carries. This type must at least one index parameter
  which denotes the output type of the query. Additionally it helps to have a parameter `α` on which
  the index type depends. This way, any instance parameters of `α` can be used easily
  for the output types. The signatures of `Model.evalQuery` and `Model.Cost` are fixed.
  So you can't supply instances for the index type there.
2. Define one or more cost types `C` and instances of `PureCosts` for this cost type.
3. Define a `Model Q C` type instance
4. Write your algorithm as a monadic program in `Prog Q α`. With sufficient type anotations
  each query `q : Q` is automatically lifted into `Prog Q α`.
## Tags

query model, free monad, time complexity, Prog
-/

namespace Cslib

namespace Algorithms

/--
A model type for a query type `QType` and cost type `Cost`. It consists of
two fields, which respectively define the evaluation and cost of a query.
-/
structure Model (QType : Type u → Type u) (Cost : Type)
  [AddCommMonoid Cost] where
  /-- Evaluates a query `q : Q ι` to return a result of type `ι` -/
  evalQuery : QType ι → ι
  /-- Counts the operational cost of a query `q : Q ι` to return a result of type `Cost`.
  The cost could represent any desired complexity measure,
  including but not limited to time complexity -/
  cost : QType ι → Cost

open Cslib.Algorithms.Lean in
abbrev Model.timeQuery [AddCommMonoid Cost]
    (M : Model Q Cost) (x : Q ι) : TimeM Cost ι := do
  TimeM.tick (M.cost x); return (M.evalQuery x)

/--
A program is defined as a Free Monad over a Query type `Q` which operates on a base type `α`
which can determine the input and output types of a query.
-/
abbrev Prog Q α := FreeM Q α

/--
The evaluation function of a program `P : Prog Q α` given a model `M : Model Q α` of `Q`
-/
@[simp, grind]
def Prog.eval [AddCommMonoid Cost]
  (P : Prog Q α) (M : Model Q Cost) : α :=
  Id.run <| P.liftM fun x => pure (M.evalQuery x)

/--
The cost function of a program `P : Prog Q α` given a model `M : Model Q α` of `Q`.
The most common use case of this function is to compute time-complexity, hence the name.
-/
@[simp, grind]
def Prog.time [AddCommMonoid Cost]
  (P : Prog Q α) (M : Model Q Cost) : Cost :=
  match P with
  | .pure _ => 0
  | .liftBind op cont =>
      let t₁ := M.cost op
      let qval := M.evalQuery op
      t₁ + (time (cont qval) M)

@[grind =]
lemma Prog.time.bind_pure [AddCommMonoid Cost] (M : Model Q Cost) :
  Prog.time (op >>= FreeM.pure) M = (Prog.time op M) := by
  simp only [bind, FreeM.bind_pure]

@[grind =]
lemma Prog.time.pure_bind
  [AddCommMonoid Cost] (M : Model Q Cost) :
  Prog.time (FreeM.pure x >>= m) M = (m x).time M := by
  rfl

@[grind =]
lemma Prog.time.bind [AddCommMonoid Cost] (M : Model Q Cost)
  (op : Prog Q ι) (cont : ι → Prog Q α) :
  Prog.time (op >>= cont) M =
    (Prog.time op M) + (Prog.time (cont (Prog.eval op M)) M):= by
  simp only [FreeM.bind_eq_bind, eval]
  induction op with
  | pure a =>
      simp
  | liftBind op cont' ih =>
      specialize ih (M.evalQuery op)
      simp_all only [time, FreeM.liftBind_bind, FreeM.liftM_liftBind, LawfulMonad.pure_bind]
      rw [add_assoc]

@[simp, grind =]
lemma Prog.time.liftBind [AddCommMonoid Cost] (M : Model Q Cost)
  (op : Q ι) (cont : ι → Prog Q α) :
  Prog.time (.liftBind op cont) M =
    (Prog.time (FreeM.lift op) M) + (Prog.time (cont (M.evalQuery op)) M):= by
  simp [time, FreeM.lift_def]

section Reduction

/--
A reduction structure from query type `Q₁` to query type `Q₂`.
-/
structure Reduction (Q₁ Q₂ : Type u → Type u) where
  /-- `reduce (q : Q₁ α)` is a program `P : Prog Q₂ α` that is intended to
  implement `q` in the query type `Q₂` -/
  reduce : Q₁ α → Prog Q₂ α

/--
`Prog.reduceProg` takes a reduction structure from a query `Q₁` to `Q₂` and extends its
`reduce` function to programs on the query type `Q₁`
-/
def Prog.reduceProg (P : Prog Q₁ α) (red : Reduction Q₁ Q₂) : Prog Q₂ α :=
    P.liftM red.reduce


end Reduction

end Cslib.Algorithms
