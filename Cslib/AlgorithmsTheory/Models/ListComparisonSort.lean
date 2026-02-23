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
/--
A model for comparison sorting on lists.
-/
inductive SortOps (α : Type) : Type → Type  where
  /--`cmpLE x y` is intended to return `true` if `x ≤ y` and `false` otherwise.
  The specific order relation depends on the model provided for this type-/
  | cmpLE (x : α) (y : α): SortOps α Bool
  /--`insertHead l x` is intended to return `x :: l`-/
  | insertHead (x : α) (l : List α) : SortOps α (List α)

open SortOps

section SortOpsCostModel

/--
A cost type for counting the operations of `SortOps` with separate fields for
counting calls to `cmpLT` and `insertHead`
-/
@[ext, grind]
structure SortOpsCost where
  /-- `compares` counts the number of calls to `cmpLT` -/
  compares : ℕ
  /-- `inserts` counts the number of calls to `insertHead` -/
  inserts : ℕ

@[simps, grind]
instance zeroSortOps : Zero SortOpsCost := ⟨0,0⟩

@[simps]
instance : LE SortOpsCost where
  le soc₁ soc₂ := soc₁.compares ≤ soc₂.compares ∧ soc₁.inserts ≤ soc₂.inserts

@[simps!, grind]
instance partialOrderSortOps : PartialOrder SortOpsCost where
  le_refl := by
    intro c
    simp
  le_trans a b c := by
    simp only [le_def, and_imp]
    intro ab_comps ab_inserts bc_comps bc_inserts
    refine ⟨?_, ?_⟩
    all_goals solve_by_elim [Nat.le_trans]
  le_antisymm := by
    intro ⟨a_comps, a_inserts⟩ ⟨b_comps, b_inserts⟩
    simp only [le_def, SortOpsCost.mk.injEq, and_imp]
    intro ab_comps ab_inserts ba_comps ba_inserts
    refine ⟨?_, ?_⟩
    all_goals solve_by_elim[Nat.le_antisymm]


/-- Component-wise addition operation on `SortOpsCost` -/
@[simps]
def add (soc₁ soc₂ : SortOpsCost) : SortOpsCost:=
  ⟨soc₁.compares + soc₂.compares, soc₁.inserts + soc₂.inserts⟩

/-- Component-wise scalar (natural number) multiplication operation on `SortOpsCost` -/
@[simps]
def nsmul (n : ℕ) (soc : SortOpsCost) : SortOpsCost := ⟨n • soc.compares, n • soc.inserts⟩

@[simps]
instance AddSortOps : Add SortOpsCost where
  add := add

@[simps!]
instance acsSortOpsCost : AddCommMonoid SortOpsCost where
  add_assoc a b c := by
    simp only [AddSortOps_add, add, Nat.add_assoc]
  add_comm := by
    intro a b
    simp only [AddSortOps_add, add, Nat.add_comm]
  zero_add := by
    intro ⟨c, i⟩
    simp only [AddSortOps_add, add, zeroSortOps_zero_compares, zero_add, zeroSortOps_zero_inserts]
  add_zero := by
    intro ⟨c, i⟩
    simp [add]
  nsmul := nsmul
  nsmul_zero := by
    intro x
    rw [nsmul, zero_nsmul, zero_nsmul]
    rfl
  nsmul_succ := by
    intro n x
    rw [nsmul, succ_nsmul, succ_nsmul]
    rfl


/--
A model of `SortOps` that uses `SortOpsCost` as the cost type for operations.
-/
def sortModel (α : Type) [LinearOrder α] : Model (SortOps α) SortOpsCost where
  evalQuery
    | .cmpLE x y =>
            if x ≤ y then
              true
            else
              false
    | .insertHead x l => x :: l
  cost q :=
    match q with
    | .cmpLE _ _ => ⟨1,0⟩
    | .insertHead _ _ => ⟨0,1⟩

@[grind =]
lemma SortModel_cmpquery_iff [LinearOrder α] (x y : α) :
    (sortModel α).evalQuery (cmpLE x y) ↔ x ≤ y := by
  simp [sortModel]

@[grind =]
lemma SortModel_insertHeadquery_iff [LinearOrder α] (l : List α) (x : α) :
    (sortModel α).evalQuery (insertHead x l) = x :: l := by
  simp [sortModel]


lemma SortModel_addComponents (m₁ m₂ m₃ : SortOpsCost) :
    m₁ + m₂ = m₃ ↔
      m₁.compares + m₂.compares = m₃.compares ∧
        m₁.inserts + m₂.inserts = m₃.inserts := by
  aesop

lemma SortModel_leComponents (m₁ m₂ : SortOpsCost) :
    m₁ ≤ m₂ ↔
      m₁.compares ≤ m₂.compares ∧
        m₁.inserts ≤ m₂.inserts := by
  simp only [LE.le]

end SortOpsCostModel

section NatModel

/--
A model of `SortOps` that uses `ℕ` as the type for the cost of operations. In this model,
both comparisons and insertions are counted in a single `ℕ` parameter.
-/
def sortModelNat (α : Type) [LinearOrder α] : Model (SortOps α) ℕ where
  evalQuery
    | .cmpLE x y =>
            if x ≤ y then
              true
            else
              false
    | .insertHead x l => x :: l
  cost
    | .cmpLE _ _ => 1
    | .insertHead _ _ => 1

@[simp]
lemma sortModelNat_eval_1 [LinearOrder α] (y x : α) :
    y < x → (sortModelNat α).evalQuery (cmpLE x y) = false := by
  intro h
  simp only [sortModelNat, Bool.if_false_right, Bool.and_true, decide_eq_false_iff_not, not_le]
  exact h

end NatModel

end Algorithms

end Cslib
