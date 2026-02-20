/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel

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

section SortOpsCostModel

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

end SortOpsCostModel

section NatModel

def sortModelNat (α : Type) [LinearOrder α] : Model (SortOps α) ℕ where
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
    | .cmpLT _ _ => 1
    | .insertHead _ _ => 1

@[simp]
lemma sortModelNat_eval_1 [LinearOrder α] (y x : α) :
  y ≤ x → (sortModelNat α).evalQuery (cmpLT x y) = false := by
  intro h
  simp only [sortModelNat, Bool.if_false_right, Bool.and_true, decide_eq_false_iff_not, not_lt]
  exact h

end NatModel

end Algorithms

end Cslib
