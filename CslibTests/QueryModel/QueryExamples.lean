/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace Cslib

namespace Algorithms

section Examples

/--
ListOps provides an example of list query type equipped with a `find` query.
The complexity of this query depends on the search algorithm used. This means
we can define two separate models for modelling situations where linear search
or binary search is used.
-/
inductive ListOps (α : Type u) : Type u → Type _ where
  | get (l : List α) (i : Fin l.length) : ListOps α α
  | find (l : List α) (elem : α) : ListOps α (ULift ℕ)
  | write (l : List α) (i : Fin l.length) (x : α) : ListOps α (List α)

/-- The typical means of evaluating a `ListOps`. -/
@[simp]
def ListOps.eval [BEq α] : ListOps α ι → ι
  | .write l i x => l.set i x
  | .find l elem => l.findIdx (· == elem)
  | .get l i => l[i]

@[simps]
def ListOps.linSearchWorstCase [DecidableEq α] : Model (ListOps α) ℕ where
  evalQuery := ListOps.eval
  cost
    | .write l _ _ => l.length
    | .find l _ =>  l.length
    | .get l _ => l.length

def ListOps.binSearchWorstCase [BEq α] : Model (ListOps α) ℕ where
  evalQuery := ListOps.eval
  cost
    | .find l _ => 1 + Nat.log 2 (l.length)
    | .write l _ _ => l.length
    | .get l _ => l.length

inductive ArrayOps (α : Type u) : Type u → Type _ where
  | get (l : Array α) (i : Fin l.size) : ArrayOps α α
  | find (l : Array α) (x : α) : ArrayOps α (ULift ℕ)
  | write (l : Array α) (i : Fin l.size) (x : α) : ArrayOps α (Array α)

/-- The typical means of evaluating a `ListOps`. -/
@[simp]
def ArrayOps.eval [BEq α] : ArrayOps α ι → ι
  | .write l i x => l.set i x
  | .find l elem => l.findIdx (· == elem)
  | .get l i => l[i]

@[simps]
def ArrayOps.binSearchWorstCase [BEq α] : Model (ArrayOps α) ℕ where
  evalQuery := ArrayOps.eval
  cost
    | .find l _ => 1 + Nat.log 2 (l.size)
    | .write _ _ _ => 1
    | .get _ _ => 1

end Examples

end Algorithms

end Cslib
