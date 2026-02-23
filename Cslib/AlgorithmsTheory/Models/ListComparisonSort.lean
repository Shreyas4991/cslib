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

/--
Injective mapping from a pair of ℕ to SortOpsCost
-/
def SortOpsCost.ofProd : ℕ × ℕ ↪ SortOpsCost where
  toFun pair := ⟨pair.1, pair.2⟩
  inj' := by
    unfold Function.Injective
    intro (_,_) (_, _)
    simp only [mk.injEq, Prod.mk.injEq, imp_self]

/--
Injective mapping from SortOpsCost to a pair of ℕ
-/
def SortOpsCost.toProd : SortOpsCost ↪ ℕ × ℕ  where
  toFun pair := (pair.compares, pair.inserts)
  inj' := by
    unfold Function.Injective
    intro ⟨_,_⟩ ⟨_,_⟩
    simp only [mk.injEq, Prod.mk.injEq, imp_self]

@[simps, grind]
instance zeroSortOps : Zero SortOpsCost := ⟨0,0⟩

@[simps]
instance : LE SortOpsCost where
  le soc₁ soc₂ := soc₁.compares ≤ soc₂.compares ∧ soc₁.inserts ≤ soc₂.inserts

@[simps]
instance : LT SortOpsCost where
  lt soc₁ soc₂ := soc₁ ≤ soc₂ ∧ (soc₁.compares < soc₂.compares ∨ soc₁.inserts < soc₂.inserts)

@[simps!, grind]
instance partialOrderSortOps : PartialOrder SortOpsCost := by
  apply Function.Injective.partialOrder SortOpsCost.toProd
  · exact SortOpsCost.toProd.inj'
  · simp [SortOpsCost.toProd]
  · intro x y
    simp only [SortOpsCost.toProd, Function.Embedding.coeFn_mk, Prod.mk_lt_mk, lt_def, le_def]
    refine ⟨?_, ?_⟩
    · rintro (⟨h_compares, h_inserts⟩ | ⟨h_compares, h_inserts⟩)
      all_goals grind only
    · rintro ⟨h_leq, (h | h)⟩
      all_goals grind only

@[simps]
instance AddSortOps : Add SortOpsCost where
  add (soc₁ soc₂ : SortOpsCost) :=  ⟨soc₁.compares + soc₂.compares, soc₁.inserts + soc₂.inserts⟩

@[simps]
instance SMulSortOps : SMul ℕ SortOpsCost where
  smul (n : ℕ) (soc : SortOpsCost) : SortOpsCost := ⟨n • soc.compares, n • soc.inserts⟩

instance acsSortOpsCost : AddCommMonoid SortOpsCost := by
  apply Function.Injective.addCommMonoid SortOpsCost.toProd
  · exact SortOpsCost.toProd.inj'
  · rfl
  · intro ⟨xcomp, xins⟩ ⟨ycomp, yins⟩
    rfl
  · intro x n
    rfl

/--
A model of `SortOps` that uses `SortOpsCost` as the cost type for operations.
-/
def sortModel (α : Type) [LinearOrder α] : Model (SortOps α) SortOpsCost where
  evalQuery
    | .cmpLE x y => decide (x ≤ y)
    | .insertHead x l => x :: l
  cost
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

@[simp]
lemma cost_cmpLT_compares [LinearOrder α] : ((sortModel α).2 (cmpLE head x)).compares = 1 := by
  simp [sortModel]

@[simp]
lemma cost_cmpLT_inserts [LinearOrder α] :
    ((sortModel α).2 (cmpLE head x)).inserts = 0 := by
  simp [sortModel]

@[simp]
lemma cost_insertHead_compares [LinearOrder α] :
    ((sortModel α).2 (insertHead x l)).compares = 0 := by
  simp [sortModel]

@[simp]
lemma cost_insertHead_inserts [LinearOrder α] :
    ((sortModel α).2 (insertHead x l)).inserts = 1 := by
  simp [sortModel]

end SortOpsCostModel

section NatModel

/--
A model of `SortOps` that uses `ℕ` as the type for the cost of operations. In this model,
both comparisons and insertions are counted in a single `ℕ` parameter.
-/
def sortModelNat (α : Type) [LinearOrder α] : Model (SortOps α) ℕ where
  evalQuery
    | .cmpLE x y => decide (x ≤ y)
    | .insertHead x l => x :: l
  cost
    | .cmpLE _ _ => 1
    | .insertHead _ _ => 1

@[simp]
lemma sortModelNat_eval_1 [LinearOrder α] (y x : α) :
    y < x → (sortModelNat α).evalQuery (cmpLE x y) = false := by
  intro h
  simp only [sortModelNat, decide_eq_false_iff_not, not_le]
  exact h

end NatModel

end Algorithms

end Cslib
