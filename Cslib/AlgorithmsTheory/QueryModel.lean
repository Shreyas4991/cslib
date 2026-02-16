/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Mathlib
public import Cslib.Foundations.Control.Monad.Free.Effects
public import Cslib.Foundations.Control.Monad.Free.Fold
public import Batteries

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

namespace Cslib.Algorithms

class PureCosts (α : Type u) where
  pureCost : α

scoped instance : PureCosts ℕ where
  pureCost := 1

structure Model (QType : Type u → Type u) (Cost : Type) [Add Cost] [Zero Cost]
  [PureCosts Cost] where
  evalQuery : QType ι → ι
  cost : QType ι → Cost

abbrev Prog Q α := FreeM Q α

instance {Q α} : Coe (Q α) (FreeM Q α) where
  coe := FreeM.lift

@[simp, grind]
def Prog.eval [Add Cost] [Zero Cost] [PureCosts Cost]
  (P : Prog Q α) (M : Model Q Cost) : α :=
  Id.run <| P.liftM fun x => pure (M.evalQuery x)

@[simp, grind]
def Prog.time [Add Cost] [Zero Cost] [PureCosts Cost]
  (P : Prog Q α) (M : Model Q Cost) : Cost :=
  match P with
  | .pure _ => PureCosts.pureCost
  | .liftBind op cont =>
      let t₁ := M.cost op
      let qval := M.evalQuery op
      t₁ + (time (cont qval) M)

lemma Prog.time.bind_pure [iAdd : Add Cost]
  [iZero : Zero Cost] [iPC : PureCosts Cost] (M : Model Q Cost) :
  Prog.time (FreeM.bind op (fun rest => FreeM.pure x)) M = (Prog.time op M) + pureCost:= by
  unfold time
  induction op with
  | pure a =>
      simp
      sorry
  | liftBind op cont ih =>
      simp
      specialize ih (M.evalQuery op)
      simp at ih
      sorry


section Reduction

structure Reduction (Q₁ Q₂ : Type u → Type u) where
  reduce : Q₁ α → Prog Q₂ α

def Prog.reduceProg (P : Prog Q₁ α) (red : Reduction Q₁ Q₂) : Prog Q₂ α :=
    P.liftM red.reduce


end Reduction

end Cslib.Algorithms
