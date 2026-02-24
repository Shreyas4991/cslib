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
Equivalence between SortOpsCost and ℕ
-/
def SortOpsCost.Equiv : Equiv SortOpsCost (ℕ × ℕ) where
  toFun sortOps := (sortOps.compares, sortOps.inserts)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv := by
    intro _
    rfl
  right_inv := by
    intro _
    rfl

@[simps, grind]
instance : Zero SortOpsCost := ⟨0,0⟩

@[simps]
instance : LE SortOpsCost where
  le soc₁ soc₂ := soc₁.compares ≤ soc₂.compares ∧ soc₁.inserts ≤ soc₂.inserts

@[simps]
instance : LT SortOpsCost where
  lt soc₁ soc₂ := soc₁ ≤ soc₂ ∧ (soc₁.compares < soc₂.compares ∨ soc₁.inserts < soc₂.inserts)

@[grind]
instance : PartialOrder SortOpsCost := by
  apply Function.Injective.partialOrder SortOpsCost.Equiv.toEmbedding
  · exact SortOpsCost.Equiv.toEmbedding.inj'
  · rfl
  · intro x y
    simp only [lt_def, le_def]
    refine ⟨?_, ?_⟩
    · simp only [SortOpsCost.Equiv, Equiv.coe_toEmbedding, Equiv.coe_fn_mk, Prod.mk_lt_mk]
      rintro (⟨_, _⟩ | ⟨_, _⟩)
      all_goals grind
    · simp only [SortOpsCost.Equiv, Equiv.coe_toEmbedding, Equiv.coe_fn_mk, Prod.mk_lt_mk, and_imp]
      intros
      all_goals grind

@[simps]
instance : Add SortOpsCost where
  add (soc₁ soc₂ : SortOpsCost) :=  ⟨soc₁.compares + soc₂.compares, soc₁.inserts + soc₂.inserts⟩

@[simps]
instance : SMul ℕ SortOpsCost where
  smul (n : ℕ) (soc : SortOpsCost) : SortOpsCost := ⟨n • soc.compares, n • soc.inserts⟩

instance : AddCommMonoid SortOpsCost := by
  apply Function.Injective.addCommMonoid SortOpsCost.Equiv.toEmbedding
  · exact SortOpsCost.Equiv.toEmbedding.inj'
  · rfl
  · intro ⟨xcomp, xins⟩ ⟨ycomp, yins⟩
    rfl
  · intro x n
    rfl

/--
A model of `SortOps` that uses `SortOpsCost` as the cost type for operations.
-/
@[simps, grind]
def sortModel (α : Type) [LinearOrder α] : Model (SortOps α) SortOpsCost where
  evalQuery
    | .cmpLE x y => decide (x ≤ y)
    | .insertHead x l => x :: l
  cost
    | .cmpLE _ _ => ⟨1,0⟩
    | .insertHead _ _ => ⟨0,1⟩

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
lemma sortModelNat_eval_false [LinearOrder α] (y x : α) :
    y < x → (sortModelNat α).evalQuery (cmpLE x y) = false := by
  intro h
  simp only [sortModelNat, decide_eq_false_iff_not, not_le]
  exact h

end NatModel

end Algorithms

end Cslib
