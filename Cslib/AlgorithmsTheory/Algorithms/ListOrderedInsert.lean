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
A purely lean version of `insertOrd`, which is shown to be extensionally equal to
`insertOrd` when evaluated in the `SortOps` query model.
-/
def insertOrdNaive (x : α) (l : List α) [LinearOrder α] :=
  match l with
  | [] => [x]
  | a :: as => if a < x then a :: insertOrdNaive x as else x :: (a :: as)

lemma insertOrdNaive_mem [LinearOrder α]
  (x y : α) (l : List α) (hx : x ∈ insertOrdNaive y l) : x = y ∨ x ∈ l := by
  induction l with
  | nil =>
      simp only [insertOrdNaive, List.mem_cons, List.not_mem_nil, or_false] at hx
      left
      exact hx
  | cons head tail ih =>
      simp_all only [insertOrdNaive, List.mem_cons]
      split_ifs at hx with h_head
      · simp only [List.mem_cons] at hx
        obtain (hx | hx) := hx
        · tauto
        · specialize ih hx
          tauto
      · simp at hx
        assumption

lemma insertOrdNaive_length [LinearOrder α] (x : α) (l : List α) :
  (insertOrdNaive x l).length = l.length + 1 := by
  induction l with
  | nil =>
      simp [insertOrdNaive]
  | cons head tail ih =>
      by_cases h : head < x <;> simp [insertOrdNaive, h, ih]

lemma insertOrdNaive_sorted [LinearOrder α] (x : α) (l : List α) :
  l.Pairwise (· ≤ ·) → (insertOrdNaive x l).Pairwise (· ≤ ·) := by
  intro h
  induction l with
  | nil =>
      cases h with
      | nil => simp [insertOrdNaive]
  | cons head tail ih =>
      cases h with
      | cons h₁ h₂ =>
          specialize ih h₂
          simp only [insertOrdNaive]
          split_ifs with h_head
          · simp only [List.pairwise_cons, ih, and_true]
            intro a ha
            apply insertOrdNaive_mem at ha
            obtain (ha | ha) := ha
            · grind
            · grind
          · simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, h₂, and_true]
            grind

/--
Performs ordered insertion of `x` into a list `l` in the `SortOps` query model.
If `l` is sorted, then `x` is inserted into `l` such that the resultant list is also sorted.
-/
def insertOrd (x : α) (l : List α) : Prog (SortOps α) (List α) := do
  match l with
  | [] => insertHead l x
  | a :: as =>
      let cmp : Bool ← cmpLT a x
      if cmp
      then
        let res ← insertOrd x as
        insertHead res a
      else
        insertHead (a :: as) x

lemma insertOrd_is_insertOrdNaive [LinearOrder α] :
  ∀ (x : α) (l : List α) ,
    (insertOrd x l).eval (sortModel α) = insertOrdNaive x l := by
  intro x l
  induction l with
  | nil =>
      simp_all [insertOrd, insertOrdNaive, sortModel]
  | cons head tail ih =>
      simp_all only [eval, sortModel, Bool.if_false_right, Bool.and_true, insertOrd, bind,
        FreeM.lift_def, FreeM.liftBind_bind, FreeM.pure_bind, FreeM.liftM_liftBind, insertOrdNaive]
      split_ifs with h_head
      · simp only [FreeM.liftM_bind, FreeM.liftM_liftBind, FreeM.liftM_pure, bind_pure,
        bind_pure_comp, Id.run_map, List.cons.injEq, true_and]
        exact ih
      · simp_all only [decide_false, reduceCtorEq]
      · simp_all
      · simp_all

lemma insertOrd_length [LinearOrder α] (x : α) (l : List α) :
  ((insertOrd x l).eval (sortModel α)).length = l.length + 1 := by
  rw [insertOrd_is_insertOrdNaive]
  simp [insertOrdNaive_length]

lemma bind_compares {α} (x tail head) [LinearOrder α] :
  (Prog.time
      (FreeM.bind (insertOrd x tail)
        (fun res => FreeM.liftBind (insertHead res head) FreeM.pure))
      (sortModel α)).compares =
    (Prog.time (insertOrd x tail) (sortModel α)).compares := by
  have h := congrArg SortOpsCost.compares
    (Prog.time.bind (M := sortModel α)
      (op := insertOrd x tail)
      (cont := fun res => FreeM.liftBind (insertHead res head) FreeM.pure))
  simp only [FreeM.bind_eq_bind, sortModel, Bool.if_false_right,
    Bool.and_true, HAdd.hAdd, time, eval, SortModel_add_compares] at h
  simp only [Add.add] at h
  simp_all only [sortModel, Bool.if_false_right, Bool.and_true]
  rfl


lemma bind_inserts {α} (x tail head) [LinearOrder α] :
  (Prog.time
      (FreeM.bind (insertOrd x tail)
        (fun res => FreeM.liftBind (insertHead res head) FreeM.pure))
      (sortModel α)).inserts =
    (Prog.time (insertOrd x tail) (sortModel α)).inserts + 1 := by
  have h := congrArg SortOpsCost.inserts
    (Prog.time.bind (M := sortModel α)
      (op := insertOrd x tail)
      (cont := fun res => FreeM.liftBind (insertHead res head) FreeM.pure))
  simp only [HAdd.hAdd, bind, sortModel, Bool.if_false_right,
    Bool.and_true, SortModel_add_inserts, time, eval] at h
  simp only [Add.add] at h
  exact h

@[simp]
lemma cost_cmpLT_compares [LinearOrder α] : ((sortModel α).2 (cmpLT head x)).compares = 1 := by
  simp [sortModel]

@[simp]
lemma cost_cmpLT_inserts [LinearOrder α]
  : ((sortModel α).2 (cmpLT head x)).inserts = 0 := by
  simp [sortModel]

@[simp]
lemma cost_insertHead_compares [LinearOrder α]
  : ((sortModel α).2 (insertHead x l)).compares = 0 := by
  simp [sortModel]

@[simp]
lemma cost_insertHead_inserts [LinearOrder α]
  : ((sortModel α).2 (insertHead x l)).inserts = 1 := by
  simp [sortModel]

theorem insertOrd_complexity_upper_bound [LinearOrder α] :
  ∀ (l : List α) (x : α),
    (insertOrd x l).time (sortModel α) ≤ ⟨l.length, l.length + 1⟩ := by
  intro l x
  induction l with
  | nil =>
      simp [insertOrd, sortModel]
  | cons head tail ih =>
      simp_all only [insertOrd, FreeM.lift_def, FreeM.bind_eq_bind, FreeM.liftBind_bind,
        FreeM.pure_bind, time.eq_2, List.length_cons]
      obtain ⟨ih_compares, ih_inserts⟩ := ih
      split_ifs with h_head
      · simp only [HAdd.hAdd, Add.add, add, Nat.add]
        simp only [Nat.add_eq, Nat.succ_eq_add_one]
        constructor
        · clear ih_inserts
          rw [bind_compares, cost_cmpLT_compares]
          grind
        · clear ih_compares
          rw [cost_cmpLT_inserts, bind_inserts]
          grind
      · simp only [HAdd.hAdd, sortModel, Bool.if_false_right, Bool.and_true, time]
        simp only [Add.add, add, add_zero, zero_add, Nat.add_eq]
        refine ⟨?_, ?_⟩
        · grind
        · grind



lemma insertOrd_Sorted [LinearOrder α] (l : List α) (x : α) :
  l.Pairwise (· ≤ ·) → ((insertOrd x l).eval (sortModel α)).Pairwise (· ≤ ·) := by
  intro l_mono
  rw [insertOrd_is_insertOrdNaive x l]
  apply insertOrdNaive_sorted
  assumption

end Algorithms

end Cslib
