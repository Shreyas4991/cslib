/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.AlgorithmsTheory.QueryModel

@[expose] public section

/-!
# Merge sort in the query model

This file implements merge sort as a program in the query model defined in
`Cslib.Algorithms.QueryModel`. We use a two model approach to demonstrate the
wonders of reducing between models.

## Main definitions

- `merge`     : merge step using `Prog` comparisons
- `split`     : split a list in two by alternating elements
- `mergeSort` : merge sort expressed in the query model

We also provide simple example evaluations of `mergeSort` and its time cost.
-/



namespace Cslib.Algorithms


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

lemma merge_timeComplexity [LinearOrder α] (x y : List α) :
  (merge x y).time (sortModel α) = ⟨min x.length y.length , 0 ,1⟩ := by
  fun_induction merge
  · simp
  · simp
  · expose_names
    simp
    split_ifs with hxy
    · 
      done
    · done


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




/-- Split a list into two lists by alternating elements. -/
def split (xs : List Nat) : List Nat × List Nat :=
  let rec go : List Nat → List Nat → List Nat → List Nat × List Nat
    | [], accL, accR => (accL.reverse, accR.reverse)
    | [x], accL, accR => ((x :: accL).reverse, accR.reverse)
    | x :: y :: xs, accL, accR => go xs (x :: accL) (y :: accR)
  go xs [] []

-- /-- Merge sort expressed as a program in the query model.
-- TODO: Working version without partial -/
-- partial def mergeSort : List Nat → Prog (SortOps Nat) (List Nat)
--   | []      => pure []
--   | [x]     => pure [x]
--   | xs      =>
--     let (left, right) := split xs
--     do
--       let sortedLeft  ← mergeSort left
--       let sortedRight ← mergeSort right
--       merge sortedLeft sortedRight

-- #eval (mergeSort [5,3,8,6,2,7,4,1]).eval (sortModel Nat)
-- #eval (mergeSort [5,3,8,6,2,7,4,1]).time (sortModel Nat)

def mergeSort (xs : List α) : Prog (SortOps α) (List α) :=  do
  if xs.length < 2 then return xs
  else
    let half  := xs.length / 2
    let left  := xs.take half
    let right := xs.drop half
    let sortedLeft  ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight

def mergeSortNaive [LinearOrder α] (xs : List α) : List α :=
  if xs.length < 2 then xs
  else
    let sortedLeft  := mergeSortNaive (xs.take (xs.length/2))
    let sortedRight := mergeSortNaive (xs.drop (xs.length/2))
    mergeNaive sortedLeft sortedRight

lemma mergeSort_is_mergeSortNaive [LinearOrder α] (xs : List α) :
  (mergeSort xs).eval (sortModel α) = mergeSortNaive xs := by
  unfold mergeSortNaive
  induction xs.length using Nat.strong_induction_on with
  | h n ih =>
    unfold mergeSort
    split_ifs with hxs_len
    · simp [Id.run]
    · simp [Id.run]
      specialize ih (n / 2) (by grind)
      split_ifs at ih with h_ih_if
      · rw [←ih]
        unfold mergeSort
        simp_rw [←merge_is_mergeNaive]
        done
      · done
    · simp [Id.run]
      done
    · done


lemma mergeNaive_sorted_sorted [LinearOrder α] (xs ys : List α)
  (hxs_mono : Monotone xs.get) (hys_mono : Monotone ys.get) :
  Monotone (mergeNaive xs ys).get := by
  sorry

end Cslib.Algorithms
