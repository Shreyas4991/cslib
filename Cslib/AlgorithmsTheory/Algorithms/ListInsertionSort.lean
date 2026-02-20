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

def insertionSort (l : List α) : Prog (SortOps α) (List α) :=
  match l with
  | [] => return []
  | x :: xs => do
      let rest ← insertionSort xs
      insertOrd x rest

theorem insertionSort_sorted [LinearOrder α] (l : List α) :
  ((insertionSort l).eval (sortModel α)).Pairwise (· ≤ ·) := by
  induction l with
  | nil =>
      simp [insertionSort]
  | cons head tail ih =>
      have h := insertOrd_Sorted ((insertionSort tail).eval (sortModel α)) head ih
      simp only [eval, insertionSort, bind, FreeM.liftM_bind]
      exact h

lemma insertionSort_time_compares [LinearOrder α] (head : α) (tail : List α) :
  ((insertionSort (head :: tail)).time (sortModel α)).compares =
    ((insertionSort tail).time (sortModel α)).compares +
      ((insertOrd head ((insertionSort tail).eval (sortModel α))).time (sortModel α)).compares := by
  have h := congrArg SortOpsCost.compares
    (Prog.time.bind (M := sortModel α) (insertionSort tail) (fun rest => insertOrd head rest))
  simp only [HAdd.hAdd, Add.add] at h
  simpa [insertionSort] using h

lemma insertionSort_time_inserts [LinearOrder α] (head : α) (tail : List α) :
  ((insertionSort (head :: tail)).time (sortModel α)).inserts =
    ((insertionSort tail).time (sortModel α)).inserts +
      ((insertOrd head ((insertionSort tail).eval (sortModel α))).time (sortModel α)).inserts := by
  have h := congrArg SortOpsCost.inserts
    (Prog.time.bind (M := sortModel α) (insertionSort tail) (fun rest => insertOrd head rest))
  simp only [HAdd.hAdd, Add.add] at h
  simpa [insertionSort] using h

lemma insertionSort_length [LinearOrder α] (l : List α) :
  ((insertionSort l).eval (sortModel α)).length = l.length := by
  induction l with
  | nil =>
      simp [insertionSort]
  | cons head tail ih =>
      have h := insertOrd_length (x := head) ((insertionSort tail).eval (sortModel α))
      simp only [eval] at ih
      simpa [insertionSort, ih] using h

theorem insertionSort_complexity [LinearOrder α] (l : List α) :
  ((insertionSort l).time (sortModel α))
    ≤ ⟨l.length * (l.length + 1), (l.length + 1) * (l.length + 2)⟩ := by
  induction l with
  | nil =>
      simp only [insertionSort, FreeM.pure_eq_pure, sortModel,
        Bool.if_false_right, Bool.and_true, time.eq_1, List.length_nil, zero_add, mul_one, one_mul]
      tauto
  | cons head tail ih =>
      have h := insertOrd_complexity_upper_bound ((insertionSort tail).eval (sortModel α)) head
      simp_all only [List.length_cons, insertionSort_length]
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
