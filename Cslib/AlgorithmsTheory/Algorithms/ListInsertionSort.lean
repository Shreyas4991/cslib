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
      simp [insertionSort, Id.run]
  | cons head tail ih =>
      have h := insertOrd_Sorted ((insertionSort tail).eval (sortModel α)) head ih
      simp only [eval, Id.run, pure, pcSortOps.eq_1, sortModel, Bool.if_false_right, Bool.and_true,
        insertionSort, bind, FreeM.liftM_bind]
      exact h

lemma insertionSort_time_compares [LinearOrder α] (head : α) (tail : List α) :
  ((insertionSort (head :: tail)).time (sortModel α)).compares =
    ((insertionSort tail).time (sortModel α)).compares +
      ((insertOrd head ((insertionSort tail).eval (sortModel α))).time (sortModel α)).compares := by
  have h := congrArg SortOpsCost.compares
    (Prog.time.bind (M := sortModel α) (insertionSort tail) (fun rest => insertOrd head rest))
  simp only [HAdd.hAdd, acsSortOpsCost, pcSortOps, PureCost.pureCost,
    SortModel_add_compares] at h
  simp only [Add.add, Int.add_def, add_zero] at h
  simpa [insertionSort] using h

lemma insertionSort_time_inserts [LinearOrder α] (head : α) (tail : List α) :
  ((insertionSort (head :: tail)).time (sortModel α)).inserts =
    ((insertionSort tail).time (sortModel α)).inserts +
      ((insertOrd head ((insertionSort tail).eval (sortModel α))).time (sortModel α)).inserts := by
  have h := congrArg SortOpsCost.inserts
    (Prog.time.bind (M := sortModel α) (insertionSort tail) (fun rest => insertOrd head rest))
  simp only [HAdd.hAdd, acsSortOpsCost, pcSortOps, PureCost.pureCost,
    SortModel_add_inserts] at h
  simp only [Add.add, Int.add_def, add_zero] at h
  simpa [insertionSort] using h

lemma insertionSort_time_pure [LinearOrder α] (head : α) (tail : List α) :
  ((insertionSort (head :: tail)).time (sortModel α)).pure + 1 =
    ((insertionSort tail).time (sortModel α)).pure +
      ((insertOrd head ((insertionSort tail).eval (sortModel α))).time (sortModel α)).pure := by
  have h := congrArg SortOpsCost.pure
    (Prog.time.bind (M := sortModel α) (insertionSort tail) (fun rest => insertOrd head rest))
  simp only [HAdd.hAdd, acsSortOpsCost, pcSortOps, PureCost.pureCost,
    SortModel_add_pure] at h
  simp only [Add.add, Int.add_def] at h
  simpa [insertionSort] using h

lemma insertionSort_length [LinearOrder α] (l : List α) :
  ((insertionSort l).eval (sortModel α)).length = l.length := by
  induction l with
  | nil =>
      simp [insertionSort, Prog.eval, Id.run]
  | cons head tail ih =>
      have h := insertOrd_length (x := head) ((insertionSort tail).eval (sortModel α))
      simp [Prog.eval, Id.run] at ih
      simpa [insertionSort, Prog.eval, Id.run, bind, FreeM.liftM_bind, ih] using h

theorem insertionSort_complexity [LinearOrder α] (l : List α) :
  ((insertionSort l).time (sortModel α))
    ≤ ⟨l.length * (l.length + 1), (l.length + 1) * (l.length + 2), 1 + l.length⟩ := by
  induction l with
  | nil =>
      simp [insertionSort]
  | cons head tail ih =>
      have h := insertOrd_complexity_upper_bound ((insertionSort tail).eval (sortModel α)) head
      simp_all only [partialOrderSortOps, not_and, not_le, pcSortOps.eq_1, List.length_cons,
        Nat.cast_add, Nat.cast_one, insertionSort_length]
      obtain ⟨ih₁,ih₂,ih₃⟩ := ih
      obtain ⟨h₁,h₂,h₃⟩ := h
      refine ⟨?_, ?_, ?_⟩
      · clear h₂ h₃
        rw [insertionSort_time_compares (head := head) (tail := tail)]
        have h_nonneg : (0 : ℤ) ≤ (tail.length : ℤ) := by
          exact Int.natCast_nonneg _
        nlinarith [ih₁, h₁, h_nonneg]
      · clear h₁ h₃
        rw [insertionSort_time_inserts (head := head) (tail := tail)]
        have h_nonneg : (0 : ℤ) ≤ (tail.length : ℤ) := by
          exact Int.natCast_nonneg _
        nlinarith [ih₂, h₂, h_nonneg]
      · clear h₁ h₂
        have hp := insertionSort_time_pure (head := head) (tail := tail)
        nlinarith [ih₃, h₃, hp]


end Algorithms

end Cslib
