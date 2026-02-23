/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
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
      let cmp : Bool ← cmpLE x a
      if cmp
      then
        insertHead x (a :: as)
      else
        let res ← insertOrd x as
        insertHead a res

lemma insertOrd_is_ListOrderedInsert [LinearOrder α] :
    ∀ (x : α) (l : List α) ,
      l.Pairwise (· ≤ ·) →
        (insertOrd x l).eval (sortModel α) = l.orderedInsert (· ≤ ·) x := by
  intro x l h_sorted
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

@[simp]
lemma bind_compares {α} (x tail head) [LinearOrder α] :
    (Prog.time
        (FreeM.bind (insertOrd x tail)
          (fun res => FreeM.liftBind (insertHead head res) FreeM.pure))
        (sortModel α)).compares =
      (Prog.time (insertOrd x tail) (sortModel α)).compares := by
  have h := congrArg SortOpsCost.compares
    (Prog.time.bind (M := sortModel α)
      (op := insertOrd x tail)
      (cont := fun res => FreeM.liftBind (insertHead head res) FreeM.pure))
  simp only [time, sortModel, bind_pure_comp,
    FreeM.bind_eq_bind, FreeM.liftM_bind, FreeM.liftM_liftBind, FreeM.liftM_pure, bind_pure,
    Lean.TimeM.time_bind, HAdd.hAdd, Lean.TimeM.time_map, eval] at h
  simp_all only [time, sortModel, bind_pure_comp,
    FreeM.liftM_bind, FreeM.liftM_liftBind, FreeM.liftM_pure, bind_pure, Lean.TimeM.time_bind,
    Lean.TimeM.time_map, AddSortOps_add, add_compares, Nat.add_eq_left]
  rfl

@[simp]
lemma bind_inserts {α} (x tail head) [LinearOrder α] :
    (Prog.time
        (FreeM.bind (insertOrd x tail)
          (fun res => FreeM.liftBind (insertHead head res) FreeM.pure))
        (sortModel α)).inserts =
      (Prog.time (insertOrd x tail) (sortModel α)).inserts + 1 := by
  have h := congrArg SortOpsCost.inserts
    (Prog.time.bind (M := sortModel α)
      (op := insertOrd x tail)
      (cont := fun res => FreeM.liftBind (insertHead head res) FreeM.pure))
  simp only [sortModel, time, eval] at h
  exact h

theorem insertOrd_complexity_upper_bound [LinearOrder α] :
    ∀ (l : List α) (x : α),
      (insertOrd x l).time (sortModel α) ≤ ⟨l.length, l.length + 1⟩ := by
  intro l x
  induction l with
  | nil =>
      simp [insertOrd, sortModel]
  | cons head tail ih =>
      obtain ⟨ih_compares, ih_inserts⟩ := ih
      simp only [time, bind_pure_comp, insertOrd, FreeM.lift_def, FreeM.bind_eq_bind,
        FreeM.liftBind_bind, FreeM.pure_bind, FreeM.liftM_liftBind, bind_map_left,
        Lean.TimeM.time_bind, AddSortOps_add, List.length_cons, le_def, add_compares, add_inserts]
      split_ifs with h_head
      · constructor <;> simp_all
      · constructor
        · simp_all only [time, bind_pure_comp, Bool.not_eq_true, Lean.TimeM.time_tick,
          cost_cmpLT_compares, FreeM.liftM_bind, FreeM.liftM_liftBind, FreeM.liftM_pure, bind_pure,
          Lean.TimeM.time_bind, Lean.TimeM.time_map, AddSortOps_add, add_compares,
          cost_insertHead_compares, add_zero]
          grind
        · simp_all

lemma insertOrd_Sorted [LinearOrder α] (l : List α) (x : α) :
    l.Pairwise (· ≤ ·) → ((insertOrd x l).eval (sortModel α)).Pairwise (· ≤ ·) := by
  intro l_mono
  rw [insertOrd_is_ListOrderedInsert x l l_mono]
  apply List.Pairwise.orderedInsert
  assumption

end Algorithms

end Cslib
