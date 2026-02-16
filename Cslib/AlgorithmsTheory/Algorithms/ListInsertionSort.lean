/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/
module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Algorithms.ListOrderedInsert
public import Mathlib

@[expose] public section

namespace Cslib

namespace Algorithms

open Prog

#check insertOrd
#check List.foldr

def insertionSort (l : List α) : Prog (SortOps α) (List α) :=
  match l with
  | [] => return []
  | x :: xs => do
      let rest ← insertionSort xs
      insertOrd x rest



end Algorithms

end Cslib
