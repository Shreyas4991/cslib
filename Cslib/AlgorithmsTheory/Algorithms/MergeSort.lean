/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Eric Wieser
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Models.ListComparisonSort
public import Cslib.AlgorithmsTheory.Lean.MergeSort.MergeSort
import all Cslib.AlgorithmsTheory.Lean.MergeSort.MergeSort
import all Init.Data.List.Sort.Basic
@[expose] public section

namespace Cslib.Algorithms

open SortOps

/-- Merge two sorted lists using comparisons in the query monad. -/
@[simp]
def merge (x y : List α) : Prog (SortOps α) (List α) := do
  match x,y with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs', y :: ys' => do
      let cmp : Bool ← cmpLE x y
      if cmp then
        let rest ← merge xs' (y :: ys')
        return (x :: rest)
      else
        let rest ← merge (x :: xs') ys'
        return (y :: rest)

lemma merge_timeComplexity (x y : List α) (le : α → α → Prop) [DecidableRel le] :
    (merge x y).time (sortModelNat le) ≤ x.length + y.length := by
  fun_induction List.merge x y (le · ·) with
  | case1 => simp
  | case2 => simp
  | case3 x xs y ys hxy ihx =>
    suffices 1 + (merge xs (y :: ys)).time (sortModelNat le) ≤ xs.length + 1 + (ys.length + 1) by
      simpa [hxy]
    grind
  | case4 x xs y ys hxy ihy =>
    suffices 1 + (merge (x :: xs) ys).time (sortModelNat le) ≤ xs.length + 1 + (ys.length + 1) by
      simpa [hxy]
    grind

@[simp]
lemma merge_eval (x y : List α) (le : α → α → Prop) [DecidableRel le] :
    (merge x y).eval (sortModelNat le) = List.merge x y (le · ·) := by
  fun_induction List.merge with
  | case1 => simp
  | case2 => simp
  | case3 x xs y ys ihx ihy => simp_all [merge]
  | case4 x xs y ys hxy ihx =>
    rw [decide_eq_true_iff] at hxy
    simp_all [merge, -not_le]

lemma merge_length (x y : List α) (le : α → α → Prop) [DecidableRel le] :
    ((merge x y).eval (sortModelNat le)).length = x.length + y.length := by
  rw [merge_eval]
  apply List.length_merge

/--
The `mergeSort` algorithm in the `SortOps` query model. It sorts the input list
according to the mergeSort algorithm.
-/
def mergeSort (xs : List α) : Prog (SortOps α) (List α) :=  do
  if xs.length < 2 then return xs
  else
    let half  := xs.length / 2
    let left  := xs.take half
    let right := xs.drop half
    let sortedLeft  ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight

/--
The vanilla-lean version of `mergeSortNaive` that is extensionally equal to `mergeSort`
-/
private def mergeSortNaive (xs : List α) (le : α → α → Prop) [DecidableRel le] : List α :=
  if xs.length < 2 then xs
  else
    let sortedLeft  := mergeSortNaive (xs.take (xs.length/2)) le
    let sortedRight := mergeSortNaive (xs.drop (xs.length/2)) le
    List.merge sortedLeft sortedRight (le · ·)

private proof_wanted mergeSortNaive_eq_mergeSort
    [LinearOrder α] (xs : List α) (le : α → α → Prop) [DecidableRel le] :
    mergeSortNaive xs le = xs.mergeSort

private lemma mergeSortNaive_Perm (xs : List α) (le : α → α → Prop) [DecidableRel le] :
  (mergeSortNaive xs le).Perm xs := by
  fun_induction mergeSortNaive
  · simp
  · expose_names
    rw [←(List.take_append_drop (x.length / 2) x)]
    grw [List.merge_perm_append, ← ih1, ← ih2]

@[simp]
private lemma mergeSort_eval (xs : List α) (le : α → α → Prop) [DecidableRel le] :
    (mergeSort xs).eval (sortModelNat le) = mergeSortNaive xs le := by
  fun_induction mergeSort with
  | case1 xs h =>
    simp [h, mergeSortNaive, Prog.eval]
  | case2 xs h n left right ihl ihr =>
    rw [mergeSortNaive, if_neg h]
    have im := merge_eval left right
    simp [ihl, ihr, merge_eval]
    rfl

private lemma mergeSortNaive_length (xs : List α) (le : α → α → Prop) [DecidableRel le] :
    (mergeSortNaive xs le).length = xs.length := by
  fun_induction mergeSortNaive with
  | case1 xs h =>
    simp
  | case2 xs h left right ihl ihr =>
    rw [List.length_merge]
    convert congr($ihl + $ihr)
    rw [← List.length_append]
    simp

lemma mergeSort_length (xs : List α) (le : α → α → Prop) [DecidableRel le] :
    ((mergeSort xs).eval (sortModelNat le)).length = xs.length := by
  rw [mergeSort_eval]
  apply mergeSortNaive_length

lemma merge_sorted_sorted
    (xs ys : List α) (le : α → α → Prop) [DecidableRel le] [Std.Total le] [IsTrans _ le]
    (hxs_mono : xs.Pairwise le) (hys_mono : ys.Pairwise le) :
    ((merge xs ys).eval (sortModelNat le)).Pairwise le := by
  rw [merge_eval]
  grind [hxs_mono.merge hys_mono]

private lemma mergeSortNaive_sorted
    (xs : List α) (le : α → α → Prop) [DecidableRel le] [Std.Total le] [IsTrans _ le] :
    (mergeSortNaive xs le).Pairwise le := by
  fun_induction mergeSortNaive with
  | case1 xs h =>
    match xs with | [] | [x] => simp
  | case2 xs h left right ihl ihr =>
    simpa using ihl.merge ihr

theorem mergeSort_sorted
    (xs : List α) (le : α → α → Prop) [DecidableRel le] [Std.Total le] [IsTrans _ le] :
    ((mergeSort xs).eval (sortModelNat le)).Pairwise le := by
  rw [mergeSort_eval]
  apply mergeSortNaive_sorted

theorem mergeSort_perm (xs : List α) (le : α → α → Prop) [DecidableRel le] :
    ((mergeSort xs).eval (sortModelNat le)).Perm xs := by
  rw [mergeSort_eval]
  apply mergeSortNaive_Perm

section TimeComplexity

open Cslib.Algorithms.Lean.TimeM

-- TODO: reuse the work in `mergeSort_time_le`?
theorem mergeSort_complexity (xs : List α) (le : α → α → Prop) [DecidableRel le] :
    (mergeSort xs).time (sortModelNat le) ≤ T (xs.length) := by
  fun_induction mergeSort
  · simp [T]
  · expose_names
    simp only [FreeM.bind_eq_bind, Prog.time_bind, mergeSort_eval]
    grw [merge_timeComplexity, ih1, ih2, mergeSortNaive_length, mergeSortNaive_length]
    set n := x.length
    have hleft_len : left.length ≤ n / 2 := by
      grind
    have hright_len : right.length ≤ (n + 1) / 2 := by
      have hright_eq : right.length = n - n / 2 := by
        simp [right, n, half, List.length_drop]
      rw [hright_eq]
      grind
    have htleft_len : T left.length ≤ T (n / 2) := T_monotone hleft_len
    have htright_len : T right.length ≤ T ((n + 1) / 2) := T_monotone hright_len
    grw [htleft_len, htright_len, hleft_len, hright_len]
    have hs := some_algebra (n - 2)
    have hsub1 : (n - 2) / 2 + 1 = n / 2 := by grind
    have hsub2 : 1 + (1 + (n - 2)) / 2 = (n + 1) / 2 := by grind
    have hsub3 : (n - 2) + 2 = n := by grind
    have hsplit : n / 2 + (n + 1) / 2 = n := by grind
    simpa [T, hsub1, hsub2, hsub3, hsplit, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using hs

end TimeComplexity

end Cslib.Algorithms
