/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser
-/
module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Algorithms.ListOrderedInsert
public import Mathlib

@[expose] public section

namespace Cslib

namespace Algorithms

open Prog

/--
The insertionSort algorithms on lists with the `SortOps` query
-/
def insertionSort (l : List α) : Prog (SortOps α) (List α) :=
  match l with
  | [] => return []
  | x :: xs => do
      let rest ← insertionSort xs
      insertOrd x rest

@[simp]
theorem insertionSort_eval [LinearOrder α] (l : List α) :
    (insertionSort l).eval (sortModel α) = l.insertionSort (· ≤ ·) := by
  induction l with simp_all [insertionSort]

theorem insertionSort_permutation [LinearOrder α] (l : List α) :
    ((insertionSort l).eval (sortModel α)).Perm l := by
    simp [insertionSort_eval, List.perm_insertionSort]

theorem insertionSort_sorted [LinearOrder α] (l : List α) :
    ((insertionSort l).eval (sortModel α)).Pairwise (· ≤ ·) := by
  simpa using List.pairwise_insertionSort _ _

lemma insertionSort_length [LinearOrder α] (l : List α) :
    ((insertionSort l).eval (sortModel α)).length = l.length := by
  simp

lemma insertionSort_time_compares [LinearOrder α] (head : α) (tail : List α) :
    ((insertionSort (head :: tail)).time (sortModel α)).compares =
      ((insertionSort tail).time (sortModel α)).compares +
        ((insertOrd head (tail.insertionSort (· ≤ ·))).time (sortModel α)).compares := by
  simp [insertionSort]

lemma insertionSort_time_inserts [LinearOrder α] (head : α) (tail : List α) :
    ((insertionSort (head :: tail)).time (sortModel α)).inserts =
      ((insertionSort tail).time (sortModel α)).inserts +
        ((insertOrd head (tail.insertionSort (· ≤ ·))).time (sortModel α)).inserts := by
  simp [insertionSort]

theorem insertionSort_complexity [LinearOrder α] (l : List α) :
    ((insertionSort l).time (sortModel α))
      ≤ ⟨l.length * (l.length + 1), (l.length + 1) * (l.length + 2)⟩ := by
  induction l with
  | nil =>
    simp [insertionSort]
  | cons head tail ih =>
    have h := insertOrd_complexity_upper_bound (tail.insertionSort (· ≤ ·)) head
    simp_all only [List.length_cons, List.length_insertionSort]
    obtain ⟨ih₁,ih₂⟩ := ih
    obtain ⟨h₁,h₂⟩ := h
    refine ⟨?_, ?_⟩
    · clear h₂
      rw [insertionSort_time_compares]
      nlinarith [ih₁, h₁]
    · clear h₁
      rw [insertionSort_time_inserts]
      nlinarith [ih₂, h₂]

end Algorithms

end Cslib
