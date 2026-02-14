/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.UpstreamLemmas
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
  compares : ℕ
  inserts : ℕ
  pure : ℕ

@[simp, grind]
instance pcSortOps : PureCosts SortOpsCost where
  pureCost := ⟨0,0,1⟩

@[simp, grind]
instance zeroSortOps : Zero SortOpsCost := ⟨0,0,0⟩

@[simp, grind]
instance addSortOps : Add SortOpsCost where
  add | ⟨c₁, i₁, p₁⟩, ⟨c₂, i₂, p₂⟩ => ⟨c₁ + c₂, i₁ + i₂, p₁ + p₂⟩

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
    all_goals solve_by_elim [Nat.le_trans]
  le_antisymm := by
    intro ⟨a_comps, a_inserts, a_pures⟩ ⟨b_comps, b_inserts, b_pures⟩
    simp only [SortOpsCost.mk.injEq, and_imp]
    intro ab_comps ab_inserts ab_pures ba_comps ba_inserts ba_pures
    refine ⟨?_, ?_, ?_⟩
    all_goals solve_by_elim[Nat.le_antisymm]


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
  simp only [HAdd.hAdd, addSortOps]
  simp only [instAddNat, Nat.add_eq]
  aesop

lemma SortModel_leComponents (m₁ m₂ : SortOpsCost) :
  m₁ ≤ m₂ ↔
    m₁.compares ≤ m₂.compares ∧
      m₁.inserts ≤ m₂.inserts ∧
        m₁.pure ≤ m₂.pure := by
  simp only [LE.le]

def insertOrdNaive (l : List α) [LinearOrder α] (x : α) :=
  match l with
  | [] => [x]
  | a :: as => if a < x then insertOrdNaive as x else x :: (a :: as)


lemma insertOrdNaive_sorted [LinearOrder α] (l : List α) (x : α) :
  Monotone l.get → Monotone (insertOrdNaive l x).get := by
  intro l_mono
  induction l with
  | nil =>
      simp_all [Monotone]
  | cons head tail ih =>
      have ltail_mono := List_Monotone_tail tail head l_mono
      specialize ih ltail_mono
      simp only [insertOrdNaive]
      split_ifs with h_head
      · grind
      · apply List_Monotone_cons at l_mono
        case x => exact x
        all_goals grind


def insertOrd (l : List α) (x : α) : Prog (SortOps α) (List α) := do
  match l with
  | [] => insertHead l x
  | a :: as =>
      let cmp : Bool ← cmpLT a x
      if cmp
      then
        insertOrd as x
      else
        insertHead (a :: as) x

lemma insertOrd_is_insertOrdNaive [LinearOrder α] :
  ∀ (l : List α) (x : α),
    (insertOrd l x).eval (sortModel α) = insertOrdNaive l x := by
  intro l x
  induction l with
  | nil =>
      simp_all [insertOrd, insertOrdNaive, Id.run]
  | cons head tail ih =>
      simp_all only [Prog.eval, Id.run, pure, addSortOps, zeroSortOps, pcSortOps, sortModel,
        Bool.if_false_right, Bool.and_true, insertOrd, bind, FreeM.lift_def, FreeM.liftBind_bind,
        FreeM.pure_bind, FreeM.liftM_liftBind, decide_eq_true_eq, insertOrdNaive]
      split_ifs with h_head
      · exact ih
      · simp


lemma insertOrd_complexity_upper_bound [LinearOrder α] :
  ∀ (l : List α) (x : α),
    (insertOrd l x).time (sortModel α) ≤ ⟨l.length, 1, 1⟩ := by
  intro l x
  induction l with
  | nil =>
      simp_all [sortModel, insertOrd, Prog.time, PureCosts.pureCost, HAdd.hAdd, addSortOps]
  | cons head tail ih =>
      simp only [insertOrd, bind, FreeM.lift_def, FreeM.liftBind_bind, FreeM.pure_bind, Prog.time,
        List.length_cons]
      by_cases h_head : head < x
      · split_ifs
        all_goals
          simp only at ih
          have h₁ : (⟨tail.length + 1, 1, 1⟩ : SortOpsCost) = ⟨1,0,0⟩ + ⟨tail.length, 1, 1⟩ := by
            simp only [HAdd.hAdd, addSortOps, SortOpsCost.mk.injEq, and_self, and_true]
            simp only [instAddNat, Nat.add_eq, Nat.add_comm]
          rw [h₁]
          rw [SortModel_leComponents] at *
          refine ⟨?_, ?_, ?_⟩
          all_goals
            clear h₁
            apply Nat.add_le_add
            · simp
            · --replace ih := ih.1
              simp [-sortModel] at ih
              grind
      · simp only [sortModel, Bool.if_false_right, Bool.and_true, decide_eq_true_eq]
        split_ifs
        · simp only [partialOrderSortOps, not_and, not_le, addSortOps, Prog.time,
          PureCosts.pureCost]
          refine ⟨?_, ?_, ?_⟩
          · simp only [HAdd.hAdd]
            simp only [instAddNat, Nat.add_eq, add_zero, le_add_iff_nonneg_left, zero_le]
          · simp only [HAdd.hAdd]
            simp only [instAddNat, Nat.add_eq, add_zero, zero_add, le_refl]
          · simp only [HAdd.hAdd, le_refl]

lemma insertOrd_Sorted [LinearOrder α] (l : List α) (x : α) :
  Monotone l.get → Monotone ((insertOrd l x).eval (sortModel α)).get := by
  intro l_mono
  rw [insertOrd_is_insertOrdNaive l x]
  induction l with
  | nil =>
      simp[Monotone]
  | cons head tail ih =>
      specialize ih (List_Monotone_tail tail head l_mono)
      simp only [insertOrdNaive]
      split_ifs with h_head
      · grind
      · intro i j hij
        simp only [h_head, List.get_eq_getElem, ↓reduceIte]
        apply List_Monotone_cons
        · grind
        · exact l_mono
        · grind
end Algorithms

end Cslib
