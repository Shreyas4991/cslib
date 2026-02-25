/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib

@[expose] public section


namespace Cslib

namespace Algorithms

open Prog

/--
A query type for searching elements in list. It supports exactly one query
`compare l val` which returns `true` if the head of the list `l` is equal to `val`
and returns `false` otherwise.
-/
inductive ListSearch (α : Type) : Type → Type  where
  | compare (a : List α) (val : α) : ListSearch α Bool


/-- A model of the `ListSearch` query type that assigns the cost as the number of queries. -/
@[simps]
def ListSearch.natCost [BEq α] : Model (ListSearch α) ℕ where
  evalQuery
    | .compare l x => some x == l.head?
  cost
    | .compare _ _ => 1

end Algorithms

end Cslib
