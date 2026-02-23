/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel


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
inductive ListOps (α : Type) : Type → Type  where
  | get (l : List α) (i : Fin l.length) : ListOps α α
  | find (l : List α) (elem : α) : ListOps α ℕ
  | write (l : List α) (i : Fin l.length) (x : α) : ListOps α (List α)

def ListOps.linSearchWorstCase [DecidableEq α] : Model (ListOps α) ℕ where
  evalQuery
    | .write l i x => l.set i x
    | .find l elem =>  l.findIdx (· = elem)
    | .get l i => l[i]
  cost
    | .write l i x => l.length
    | .find l elem =>  l.length
    | .get l i => l.length

def ListOps.binSearchWorstCase [BEq α] : Model (ListOps α) ℕ where
  evalQuery
    | .write l i x => l.set i x
    | .get l i => l[i]
    | .find l elem => l.findIdx (· == elem)

  cost
    | .find l _ => 1 + Nat.log 2 (l.length)
    | .write l i x => l.length
    | .get l x => l.length

inductive ArrayOps (α : Type) : Type → Type  where
  | get : (l : Array α) → (i : Fin l.size) → ArrayOps α α
  | find :  (l : Array α) → α → ArrayOps α ℕ
  | write : (l : Array α) → (i : Fin l.size) →  (x : α) → ArrayOps α (Array α)


def ArrayOps.binSearchWorstCase [BEq α] : Model (ArrayOps α) ℕ where
  evalQuery
    | .write l i x => l.set i x
    | .get l i => l[i]
    | .find l elem => l.findIdx (· == elem)

  cost
    | .find l _ => 1 + Nat.log 2 (l.size)
    | .write l i x => 1
    | .get l x => 1



end Examples

end Algorithms

end Cslib
