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

lemma insertOrd_is_ListOrderedInsert [LinearOrder α] (x : α) (l : List α) :
    l.Pairwise (· ≤ ·) → (insertOrd x l).eval (sortModel α) = l.orderedInsert (· ≤ ·) x := by
  intro h_sorted
  induction l with
  | nil =>
      simp [insertOrd, sortModel]
  | cons head tail ih =>
      rcases List.pairwise_cons.1 h_sorted with ⟨h_head_tail, h_tail_sorted⟩
      by_cases h_head : head ≤ x
      · by_cases h_x : x ≤ head
        · have hx_head : head = x := le_antisymm h_head h_x
          have htail : tail.orderedInsert (· ≤ ·) x = x :: tail := by
            cases tail with
            | nil =>
                simp
            | cons y ys =>
                have hy : x ≤ y := by simpa [hx_head] using h_head_tail y (by simp)
                simpa using List.orderedInsert_cons_of_le (· ≤ ·) ys hy
          simp [insertOrd, sortModel, List.orderedInsert_cons, hx_head]
        · simpa [insertOrd, sortModel, List.orderedInsert_cons, h_head, h_x] using ih h_tail_sorted
      · have h_x : x ≤ head := le_of_not_ge h_head
        simp [insertOrd, sortModel, List.orderedInsert_cons, h_x]


@[simp]
lemma insertOrd_length [LinearOrder α] (x : α) (l : List α) :
    ((insertOrd x l).eval (sortModel α)).length = l.length + 1 := by
  induction l with
  | nil =>
      simp [insertOrd, sortModel]
  | cons head tail ih =>
      by_cases h_head : x <= head
      · simp [insertOrd, sortModel, h_head]
      · simp [insertOrd, sortModel, h_head]
        simpa [Prog.eval] using ih

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
  intro l_mono
  rw [insertOrd_is_ListOrderedInsert x l l_mono]
  apply List.Pairwise.orderedInsert
  assumption

end Algorithms

end Cslib
