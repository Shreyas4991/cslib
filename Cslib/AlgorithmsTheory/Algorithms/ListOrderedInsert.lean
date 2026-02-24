/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Models.ListComparisonSort
public import Mathlib

@[expose] public section

namespace Cslib
namespace Algorithms

open Prog

open SortOps

/--
Performs ordered insertion of `x` into a list `l` in the `SortOps` query model.
If `l` is sorted, then `x` is inserted into `l` such that the resultant list is also sorted.
-/
def insertOrd (x : α) (l : List α) : Prog (SortOps α) (List α) := do
  match l with
  | [] => insertHead x l
  | a :: as =>
      if (← cmpLE x a : Bool) then
        insertHead x (a :: as)
      else
        let res ← insertOrd x as
        insertHead a res

@[simp]
lemma insertOrd_eval [LinearOrder α] (x : α) (l : List α) :
    (insertOrd x l).eval (sortModel α) = l.orderedInsert (· ≤ ·) x := by
  induction l with
  | nil =>
    simp [insertOrd, sortModel]
  | cons head tail ih =>
    by_cases h_head : x ≤ head
    · simp [insertOrd, h_head]
    · simp [insertOrd, h_head, ih]

-- to upstream
@[simp]
lemma _root_.List.length_orderedInsert (x : α) (l : List α) [DecidableRel r] :
    (l.orderedInsert r x).length = l.length + 1 := by
  induction l <;> grind

theorem insertOrd_complexity_upper_bound [LinearOrder α] (l : List α) (x : α) :
    (insertOrd x l).time (sortModel α) ≤ ⟨l.length, l.length + 1⟩ := by
  induction l with
  | nil =>
    simp [insertOrd, sortModel]
  | cons head tail ih =>
    obtain ⟨ih_compares, ih_inserts⟩ := ih
    rw [insertOrd]
    by_cases h_head : x ≤ head
    · simp [h_head]
    · simp [h_head]
      grind

lemma insertOrd_Sorted [LinearOrder α] (l : List α) (x : α) :
    l.Pairwise (· ≤ ·) → ((insertOrd x l).eval (sortModel α)).Pairwise (· ≤ ·) := by
  rw [insertOrd_eval]
  exact List.Pairwise.orderedInsert _ _

end Algorithms

end Cslib
