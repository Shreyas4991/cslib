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

/-!
# Insertion sort in a list

In this file we state and prove the correctness and complexity of insertion sort in lists under
the `SortOps` model. This insertionSort evaluates identically to the upstream version of
`List.insertionSort`
--

## Main Definitions

- `insertionSort` : Insertion sort algorithm in the `SortOps` query model

## Main results

- `insertionSort_eval`: `insertionSort` evaluates identically to `List.insertionSort`.
- `insertionSort_permutation` :  `insertionSort` outputs a permutation of the input list.
- `insertionSort_sorted` : `insertionSort` outputs a sorted list.
- `insertionSort_complexity` : `insertionSort` takes at most n * (n + 1) comparisons and
  (n + 1) * (n + 2) list head-insertions.
-/

namespace Cslib

namespace Algorithms

open Prog

/-- The insertionSort algorithms on lists with the `SortOps` query. -/
def insertionSort (l : List α) : Prog (SortOps α) (List α) :=
  match l with
  | [] => return []
  | x :: xs => do
      let rest ← insertionSort xs
      insertOrd x rest

@[simp]
theorem insertionSort_eval (l : List α) (le : α → α → Prop) [DecidableRel le] :
    (insertionSort l).eval (sortModel le) = l.insertionSort le := by
  induction l with simp_all [insertionSort]

theorem insertionSort_permutation (l : List α) (le : α → α → Prop) [DecidableRel le] :
    ((insertionSort l).eval (sortModel le)).Perm l := by
    simp [insertionSort_eval, List.perm_insertionSort]

theorem insertionSort_sorted
    (l : List α) (le : α → α → Prop) [DecidableRel le] [Std.Total le] [IsTrans α le] :
    ((insertionSort l).eval (sortModel le)).Pairwise le := by
  simpa using List.pairwise_insertionSort _ _

lemma insertionSort_length (l : List α) (le : α → α → Prop) [DecidableRel le] :
    ((insertionSort l).eval (sortModel le)).length = l.length := by
  simp

lemma insertionSort_time_compares (head : α) (tail : List α) (le : α → α → Prop) [DecidableRel le] :
    ((insertionSort (head :: tail)).time (sortModel le)).compares =
      ((insertionSort tail).time (sortModel le)).compares +
        ((insertOrd head (tail.insertionSort le)).time (sortModel le)).compares := by
  simp [insertionSort]

lemma insertionSort_time_inserts (head : α) (tail : List α) (le : α → α → Prop) [DecidableRel le] :
    ((insertionSort (head :: tail)).time (sortModel le)).inserts =
      ((insertionSort tail).time (sortModel le)).inserts +
        ((insertOrd head (tail.insertionSort le)).time (sortModel le)).inserts := by
  simp [insertionSort]

theorem insertionSort_complexity (l : List α) (le : α → α → Prop) [DecidableRel le] :
    ((insertionSort l).time (sortModel le))
      ≤ ⟨l.length * (l.length + 1), (l.length + 1) * (l.length + 2)⟩ := by
  induction l with
  | nil =>
    simp [insertionSort]
  | cons head tail ih =>
    have h := insertOrd_complexity_upper_bound (tail.insertionSort le) head le
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
