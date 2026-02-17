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

@[ext]
structure SortOpsCost where
  compares : ℤ
  inserts : ℤ
  pure : ℤ

@[simp, grind]
instance pcSortOps : PureCost SortOpsCost where
  pureCost := ⟨0,0,1⟩

@[simp, grind]
instance zeroSortOps : Zero SortOpsCost := ⟨0,0,0⟩


@[simp]
instance partialOrderSortOps : PartialOrder SortOpsCost where
  le | ⟨c₁, i₁, p₁⟩, ⟨c₂, i₂, p₂⟩ => c₁ ≤ c₂ ∧ i₁ ≤ i₂ ∧ p₁ ≤ p₂
  le_refl := by
    intro c
    simp only [le_refl, and_self]
  le_trans a b c := by
    simp only [and_imp]
    intro ab_comps ab_inserts ab_pures bc_comps bc_inserts bc_pures
    refine ⟨?_, ?_, ?_⟩
    all_goals solve_by_elim [Int.le_trans]
  le_antisymm := by
    intro ⟨a_comps, a_inserts, a_pures⟩ ⟨b_comps, b_inserts, b_pures⟩
    simp only [SortOpsCost.mk.injEq, and_imp]
    intro ab_comps ab_inserts ab_pures ba_comps ba_inserts ba_pures
    refine ⟨?_, ?_, ?_⟩
    all_goals solve_by_elim[Int.le_antisymm]

def add : SortOpsCost → SortOpsCost → SortOpsCost
  | ⟨c₁, i₁, p₁⟩, ⟨c₂, i₂, p₂⟩ => ⟨c₁ + c₂, i₁ + i₂, p₁ + p₂⟩

def nsmul (n : ℕ) (x : SortOpsCost) : SortOpsCost :=
  match n with
  | 0 => 0
  | m + 1 => add x (nsmul m x)

instance acsSortOpsCost : AddCommSemigroup SortOpsCost where
  add := add
  add_assoc := by
    intro a b c
    simp [HAdd.hAdd]
    simp [add, Int.instAdd, Int.add_assoc]
  add_comm := by
    intro a b
    simp [HAdd.hAdd]
    simp [add, Int.instAdd, Int.add_comm]



@[simp, grind]
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
    | .cmpLT _ _ => ⟨1,0,0⟩
    | .insertHead _ _ => ⟨0,1,0⟩

lemma SortModel_cmpquery_iff [LinearOrder α] (x y : α) :
  (sortModel α).evalQuery (cmpLT x y) ↔ x < y := by
  simp [sortModel]

lemma SortModel_insertHeadquery_iff [LinearOrder α] (l : List α) (x : α) :
  (sortModel α).evalQuery (insertHead l x) = x :: l := by
  simp [sortModel]

lemma SortModel_addComponents [LinearOrder α] (m₁ m₂ m₃ : SortOpsCost) :
  m₁ + m₂ = m₃ ↔
    m₁.compares + m₂.compares = m₃.compares ∧
      m₁.inserts + m₂.inserts = m₃.inserts ∧
        m₁.pure + m₂.pure = m₃.pure := by
  simp only [HAdd.hAdd]
  simp only [Int.instAdd]
  aesop

lemma SortModel_leComponents (m₁ m₂ : SortOpsCost) :
  m₁ ≤ m₂ ↔
    m₁.compares ≤ m₂.compares ∧
      m₁.inserts ≤ m₂.inserts ∧
        m₁.pure ≤ m₂.pure := by
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
      simp_all [insertOrd, insertOrdNaive, Id.run]
  | cons head tail ih =>
      simp_all only [Prog.eval, Id.run, pure,  sortModel,
        Bool.if_false_right, Bool.and_true, insertOrd, bind, FreeM.lift_def, FreeM.liftBind_bind,
        FreeM.pure_bind, FreeM.liftM_liftBind, decide_eq_true_eq, insertOrdNaive]
      split_ifs with h_head
      · simp only [FreeM.liftM_bind, bind, FreeM.liftM_liftBind, FreeM.liftM_pure, pure,
        List.cons.injEq, true_and]
        exact ih
      · simp


lemma insertOrd_complexity_upper_bound [LinearOrder α] :
  ∀ (l : List α) (x : α),
    (insertOrd x l).time (sortModel α) ≤ ⟨l.length, l.length + 1, 1⟩ := by
  intro l x
  induction l with
  | nil => rfl
  | cons head tail ih =>
      simp_all only [partialOrderSortOps, not_and, not_le, pcSortOps, sortModel,
        Bool.if_false_right, Bool.and_true, insertOrd, bind, FreeM.lift_def, FreeM.liftBind_bind,
        FreeM.pure_bind, time.eq_2, decide_eq_true_eq, List.length_cons, Nat.cast_add, Nat.cast_one]
      split_ifs with h_head
      · obtain ⟨h₁,h₂, h₃⟩ := ih
        refine ⟨?_, ?_, ?_⟩
        · clear h₂ h₃
          conv =>
            lhs
            arg 1
            arg 2
          sorry
        · clear h₁ h₃
          sorry
        · clear h₁ h₂
          sorry
      · obtain ⟨h₁, h₂, h₃⟩ := ih
        refine ⟨?_, ?_, ?_⟩
        · clear h₂ h₃
          sorry
        · clear h₁ h₃
          sorry
        · clear h₁ h₂
          sorry

lemma insertOrd_Sorted [LinearOrder α] (l : List α) (x : α) :
  l.Pairwise (· ≤ ·) → ((insertOrd x l).eval (sortModel α)).Pairwise (· ≤ ·) := by
  intro l_mono
  rw [insertOrd_is_insertOrdNaive x l]
  apply insertOrdNaive_sorted
  assumption

end Algorithms

end Cslib
