/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Algorithms.QueryModel

@[expose] public section

/-!
# Merge sort in the query model

This file implements merge sort as a program in the query model defined in
`Cslib.Algorithms.QueryModel`. The algorithm uses only comparison queries.

## Main definitions

- `merge`     : merge step using `Prog` comparisons
- `split`     : split a list in two by alternating elements
- `mergeSort` : merge sort expressed in the query model

We also provide simple example evaluations of `mergeSort` and its time cost.
-/



namespace Cslib.Algorithms

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
  evalQuery
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

def insertOrd' (l : List α) [LinearOrder α] (x : α) :=
  match l with
  | [] => [x]
  | a :: as => if a < x then insertOrd' as x else x :: (a :: as)


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

lemma insertOrd_is_insertOrd' [LinearOrder α] :
  ∀ (l : List α) (x : α),
    (insertOrd l x).eval (sortModel α) = insertOrd' l x := by
  intro l x
  induction l with
  | nil =>
      simp_all [insertOrd, insertOrd', Id.run]
  | cons head tail ih =>
      simp_all only [Prog.eval, Id.run, pure, addSortOps, zeroSortOps, pcSortOps, sortModel,
        Bool.if_false_right, Bool.and_true, insertOrd, bind, FreeM.lift_def, FreeM.liftBind_bind,
        FreeM.pure_bind, FreeM.liftM_liftBind, decide_eq_true_eq, insertOrd']
      split_ifs with h_head
      · exact ih
      · simp


lemma insertOrd_complexity [LinearOrder α] :
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


lemma List_Monotone_tail [LinearOrder α] (l : List α) (x : α) :
  Monotone (x :: l).get → Monotone l.get := by
  intro h
  simp_all only [Monotone, List.length_cons, List.get_eq_getElem]
  intro i j hij
  have : i.castSucc + 1 ≤ j.castSucc + 1 := by
    simp only [Fin.coeSucc_eq_succ, Fin.succ_le_succ_iff]
    exact hij
  specialize @h (i.castSucc + 1) (j.castSucc + 1) this
  simp_all only [Fin.coeSucc_eq_succ, Fin.val_succ, List.getElem_cons_succ]

lemma List.cons_get_pred_get (l : List α) (x : α)
  (i : Fin (x :: l).length) (hi : i > ⟨0, by grind⟩) :
  (x :: l).get i = l.get (i.pred (by aesop)) := by
  grind

lemma List_Monotone_of_cons [LinearOrder α] (tail : List α) (head : α) :
  Monotone (head :: tail).get ↔ Monotone tail.get ∧ ∀ y ∈ tail, head ≤ y := by
  constructor
  · intro mono
    constructor
    · apply List_Monotone_tail at mono
      assumption
    · intro y y_tail
      obtain ⟨i,hi⟩ := List.get_of_mem y_tail
      simp only [Monotone, List.length_cons, List.get_eq_getElem] at mono
      specialize @mono 0 (i.castSucc + 1) (by simp)
      simp_all
  · intro ⟨htail_mono, h_head⟩ i j hij
    by_cases hi_eq_j : i = j
    · rw [hi_eq_j]
    · apply Std.lt_of_le_of_ne at hij
      apply hij at hi_eq_j
      have s₁ : ⟨0, by grind⟩ < j := by
        grind
      have s₂ : (head :: tail).get j ∈ tail := by
        grind
      by_cases hi_zero : i = ⟨0, by grind⟩
      · rw [hi_zero]
        simp only [List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.coe_ofNat_eq_mod,
          Nat.zero_mod, List.getElem_cons_zero, ge_iff_le]
        specialize h_head (head :: tail)[↑j] s₂
        exact h_head
      · have s₃ : i > ⟨0, by grind⟩ := by
          grind
        rw [List.cons_get_pred_get, List.cons_get_pred_get]
        · apply htail_mono
          grind
        · exact s₁
        · exact s₃





lemma List_Monotone_cons [LinearOrder α] (tail : List α) (x head : α)
  (hx : x ≤ head) (h_mono : Monotone (head :: tail).get) : Monotone (x :: head :: tail).get := by
  have s₁ : ∀ y ∈ tail, head ≤ y := by
    intro x x_in_tail
    simp_all [Monotone]
    obtain ⟨i, hi⟩ := List.get_of_mem x_in_tail
    specialize @h_mono 0 (i.castSucc + 1) (by simp)
    simp at h_mono
    simp_all
  rw [List_Monotone_of_cons]
  simp only [List.length_cons, List.mem_cons, forall_eq_or_imp]
  constructor
  · exact h_mono
  · constructor
    · grind
    · intro y y_in_tail
      specialize s₁ y y_in_tail
      grind


lemma insertOrd'_sorted [LinearOrder α] (l : List α) (x : α) :
  Monotone l.get → Monotone (insertOrd' l x).get := by
  intro l_mono
  induction l with
  | nil =>
      simp_all [Monotone]
  | cons head tail ih =>
      have ltail_mono := List_Monotone_tail tail head l_mono
      specialize ih ltail_mono
      simp only [insertOrd']
      split_ifs with h_head
      · grind
      · apply List_Monotone_cons at l_mono
        case x => exact x
        all_goals grind


lemma insertOrd_Sorted [LinearOrder α] (l : List α) (x : α) :
  Monotone l.get → Monotone ((insertOrd l x).eval (sortModel α)).get := by
  intro l_mono
  rw [insertOrd_is_insertOrd' l x]
  induction l with
  | nil =>
      simp[Monotone]
  | cons head tail ih =>
      specialize ih (List_Monotone_tail tail head l_mono)
      simp only [insertOrd']
      split_ifs with h_head
      · grind
      · intro i j hij
        simp only [h_head, List.get_eq_getElem, ↓reduceIte]
        apply List_Monotone_cons
        · grind
        · exact l_mono
        · grind



/-- Merge two sorted lists using comparisons in the query monad. -/
def mergeNaive [LinearOrder α] (x y : List α) : List α :=
  match x,y with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs', y :: ys' =>
      if x < y then
        let rest := mergeNaive xs' (y :: ys')
        x :: rest
      else
        let rest := mergeNaive (x :: xs') ys'
        y :: rest

/-- Merge two sorted lists using comparisons in the query monad. -/
@[simp, grind]
def merge (x y : List α) : Prog (SortOps α) (List α) := do
  match x,y with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs', y :: ys' => do
      let cmp : Bool ← cmpLT x y
      if cmp then
        let rest ← merge xs' (y :: ys')
        return (x :: rest)
      else
        let rest ← merge (x :: xs') ys'
        return (y :: rest)

lemma merge_is_mergeNaive [LinearOrder α] (x y : List α) :
  (merge x y).eval (sortModel α) = mergeNaive x y := by
  fun_induction mergeNaive
  · simp [merge, Id.run]
  · expose_names
    simp [Id.run]
  · expose_names
    simp only [Prog.eval, Id.run, pure, addSortOps, zeroSortOps, pcSortOps, sortModel,
      Bool.if_false_right, Bool.and_true, merge, bind, FreeM.lift_def, FreeM.liftBind_bind,
      FreeM.pure_bind, FreeM.liftM_liftBind, decide_eq_true_eq]
    simp_all only [Prog.eval, pure, addSortOps, zeroSortOps, pcSortOps, sortModel,
      Bool.if_false_right, Bool.and_true, ↓reduceIte, FreeM.liftM_bind, bind,
      FreeM.liftM_pure, List.cons.injEq, true_and, rest]
    exact ih1
  · simp only [Prog.eval, Id.run, pure, addSortOps, zeroSortOps, pcSortOps, sortModel,
    Bool.if_false_right, Bool.and_true, merge, bind, FreeM.lift_def, FreeM.liftBind_bind,
    FreeM.pure_bind, FreeM.liftM_liftBind, decide_eq_true_eq]
    rename_i rest ih1
    simp_all only [not_lt, Prog.eval, pure, addSortOps, zeroSortOps, pcSortOps, sortModel,
      Bool.if_false_right, Bool.and_true, rest]
    split
    next h_1 =>
      simp_all only [FreeM.liftM_bind, bind, FreeM.liftM_pure, pure, List.cons.injEq]
      apply And.intro
      · grind
      · grind
    next
      h_1 =>
      simp_all only [not_lt, FreeM.liftM_bind, bind, FreeM.liftM_pure, pure, List.cons.injEq,
        true_and]
      exact ih1

lemma mergeNaive_sorted_sorted [LinearOrder α] (xs ys : List α)
  (hxs_mono : Monotone xs.get) (hys_mono : Monotone ys.get) :
  Monotone (mergeNaive xs ys).get := by
  fun_induction mergeNaive
  · simp_all
  · simp_all
  · rename_i rest ih1
    expose_names
    simp_all only [List.length_cons, forall_const, rest]
    specialize ih1 (List_Monotone_tail xs' x hxs_mono)

    sorry
  · rename_i rest ih1
    expose_names
    simp_all only [not_lt, List.length_cons, forall_const, rest]
    specialize ih1 (List_Monotone_tail ys' y hys_mono)

    sorry

/-- Split a list into two lists by alternating elements. -/
def split (xs : List Nat) : List Nat × List Nat :=
  let rec go : List Nat → List Nat → List Nat → List Nat × List Nat
    | [], accL, accR => (accL.reverse, accR.reverse)
    | [x], accL, accR => ((x :: accL).reverse, accR.reverse)
    | x :: y :: xs, accL, accR => go xs (x :: accL) (y :: accR)
  go xs [] []

/-- Merge sort expressed as a program in the query model.
TODO: Working version without partial -/
partial def mergeSort : List Nat → Prog (SortOps Nat) (List Nat)
  | []      => pure []
  | [x]     => pure [x]
  | xs      =>
    let (left, right) := split xs
    do
      let sortedLeft  ← mergeSort left
      let sortedRight ← mergeSort right
      merge sortedLeft sortedRight

#eval (mergeSort [5,3,8,6,2,7,4,1]).eval (sortModel Nat)
#eval (mergeSort [5,3,8,6,2,7,4,1]).time (sortModel Nat)




end Cslib.Algorithms
