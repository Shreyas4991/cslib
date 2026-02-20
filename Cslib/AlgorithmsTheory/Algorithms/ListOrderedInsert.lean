/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
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
/-- The Model for comparison sorting natural-number registers.
-/
inductive SortOps (α : Type) : Type → Type  where
  | cmpLT (x : α) (y : α): SortOps α Bool
  | insertHead (l : List α) (x : α) : SortOps α (List α)

open SortOps

@[ext, grind]
structure SortOpsCost where
  compares : ℕ
  inserts : ℕ


@[simp, grind]
instance zeroSortOps : Zero SortOpsCost := ⟨0,0⟩


@[simp, grind]
instance partialOrderSortOps : PartialOrder SortOpsCost where
  le | ⟨c₁, i₁⟩, ⟨c₂, i₂⟩ => c₁ ≤ c₂ ∧ i₁ ≤ i₂
  le_refl := by
    intro c
    simp only [le_refl, and_self]
  le_trans a b c := by
    simp only [and_imp]
    intro ab_comps ab_inserts bc_comps bc_inserts
    refine ⟨?_, ?_⟩
    all_goals solve_by_elim [Nat.le_trans]
  le_antisymm := by
    intro ⟨a_comps, a_inserts⟩ ⟨b_comps, b_inserts⟩
    simp only [SortOpsCost.mk.injEq, and_imp]
    intro ab_comps ab_inserts ba_comps ba_inserts
    refine ⟨?_, ?_⟩
    all_goals solve_by_elim[Nat.le_antisymm]

def add : SortOpsCost → SortOpsCost → SortOpsCost
  | ⟨c₁, i₁⟩, ⟨c₂, i₂⟩ => ⟨c₁ + c₂, i₁ + i₂⟩

def nsmul : ℕ → SortOpsCost → SortOpsCost
  | n, ⟨c, i⟩ => ⟨n • c, n • i⟩


instance acsSortOpsCost : AddCommMonoid SortOpsCost where
  add := add
  add_assoc := by
    intro a b c
    simp only [HAdd.hAdd]
    simp [add, Nat.add_assoc]
  add_comm := by
    intro a b
    simp only [HAdd.hAdd]
    simp [add, Nat.add_comm]
  zero_add := by
    intro ⟨c, i⟩
    simp only [HAdd.hAdd, Add.add, add]
    simp
  add_zero := by
    intro ⟨c, i⟩
    simp only [HAdd.hAdd, add]
    simp [Add.add]

  nsmul := nsmul
  nsmul_zero := by
    intro x
    rw [nsmul, zero_nsmul, zero_nsmul]
    rfl

  nsmul_succ := by
    intro n x
    rw [nsmul, succ_nsmul, succ_nsmul]
    rfl


def sortModel (α : Type) [LinearOrder α] : Model (SortOps α) SortOpsCost where
  evalQuery q :=
    match q with
    | .cmpLT x y =>
            if x < y then
              true
            else
              false
    | .insertHead l x => x :: l
  cost q :=
    match q with
    | .cmpLT _ _ => ⟨1,0⟩
    | .insertHead _ _ => ⟨0,1⟩

@[grind =]
lemma SortModel_cmpquery_iff [LinearOrder α] (x y : α) :
  (sortModel α).evalQuery (cmpLT x y) ↔ x < y := by
  simp [sortModel]

@[grind =]
lemma SortModel_insertHeadquery_iff [LinearOrder α] (l : List α) (x : α) :
  (sortModel α).evalQuery (insertHead l x) = x :: l := by
  simp [sortModel]


lemma SortModel_addComponents (m₁ m₂ m₃ : SortOpsCost) :
  m₁ + m₂ = m₃ ↔
    m₁.compares + m₂.compares = m₃.compares ∧
      m₁.inserts + m₂.inserts = m₃.inserts := by
  simp only [HAdd.hAdd]
  aesop

@[simp]
lemma SortModel_add_compares (m₁ m₂ : SortOpsCost) :
  (Add.add m₁ m₂).compares = m₁.compares + m₂.compares := by
  cases m₁; cases m₂; rfl

@[simp]
lemma SortModel_add_inserts (m₁ m₂ : SortOpsCost) :
  (Add.add m₁ m₂).inserts = m₁.inserts + m₂.inserts := by
  cases m₁; cases m₂; rfl

lemma SortModel_leComponents (m₁ m₂ : SortOpsCost) :
  m₁ ≤ m₂ ↔
    m₁.compares ≤ m₂.compares ∧
      m₁.inserts ≤ m₂.inserts := by
  simp only [LE.le]



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
