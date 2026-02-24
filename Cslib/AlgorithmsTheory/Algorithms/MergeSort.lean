/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Models.ListComparisonSort
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

lemma merge_timeComplexity [LinearOrder α] (x y : List α) :
    (merge x y).time (sortModelNat α) ≤  x.length + y.length := by
  fun_induction merge
  · simp
  · simp
  · expose_names
    simp_all only [Prog.time, pure,
      List.length_cons, FreeM.lift_def, FreeM.bind_eq_bind, FreeM.liftBind_bind, FreeM.pure_bind,
      FreeM.liftM_liftBind, bind_assoc, Lean.TimeM.time_bind, Lean.TimeM.time_tick]
    split_ifs with hxy
    · simp_all only [FreeM.liftM_bind, FreeM.liftM_pure, bind_pure_comp, Lean.TimeM.time_map]
      simpa [sortModelNat, Lean.TimeM.pure, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using (Nat.add_le_add_left ih2 1)
    · simp_all only [Bool.not_eq_true, FreeM.liftM_bind, FreeM.liftM_pure, bind_pure_comp,
      Lean.TimeM.time_map]
      simpa [sortModelNat, Lean.TimeM.pure, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using (Nat.add_le_add_left ih1 1)

lemma merge_eval_eq_list_merge [LinearOrder α] (x y : List α) :
    (merge x y).eval (sortModelNat α) = List.merge x y := by
  fun_induction List.merge
  · simp [merge]
  · simp [merge]
  · expose_names
    simp_all [Prog.eval,  merge, sortModelNat]
  · expose_names
    simp_all only [decide_eq_true_eq, not_le, Prog.eval, merge, FreeM.lift_def, FreeM.pure_eq_pure,
      FreeM.bind_eq_bind, FreeM.liftBind_bind, FreeM.pure_bind, FreeM.liftM_liftBind,
      sortModelNat_eval_false, pure_bind, Bool.false_eq_true, ↓reduceIte, FreeM.liftM_bind,
      FreeM.liftM_pure, bind_pure_comp, Id.run_map]

lemma merge_length [LinearOrder α] (x y : List α) :
    ((merge x y).eval (sortModelNat α)).length = x.length + y.length := by
  rw [merge_eval_eq_list_merge]
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
def mergeSortNaive [LinearOrder α] (xs : List α) : List α :=
  if xs.length < 2 then xs
  else
    let sortedLeft  := mergeSortNaive (xs.take (xs.length/2))
    let sortedRight := mergeSortNaive (xs.drop (xs.length/2))
    List.merge sortedLeft sortedRight

lemma mergeSort_is_mergeSortNaive [LinearOrder α] (xs : List α) :
    (mergeSort xs).eval (sortModelNat α) = mergeSortNaive xs := by
  classical
  let P : Nat → Prop :=
    fun n => ∀ xs, xs.length = n → (mergeSort xs).eval (sortModelNat α) = mergeSortNaive xs
  have hP : P xs.length := by
    induction hlen : xs.length using  Nat.strong_induction_on generalizing xs with
    | h n ih =>
    intro xs hlen
    by_cases hlt : xs.length < 2
    · nth_rw 1 [mergeSort, mergeSortNaive]
      simp [hlt, Prog.eval]
    · have hge : 2 ≤ xs.length := by grind
      have hpos : 0 < xs.length := by grind
      set half : Nat := xs.length / 2
      set left : List α := xs.take half
      set right : List α := xs.drop half
      have hhalf_lt : half < xs.length := by grind
      have hleft_le : left.length ≤ half := by grind
      have hleft_lt_len : left.length < xs.length := by grind
      have hright_lt_len : right.length < xs.length := by grind
      have hleft : (mergeSort left).eval (sortModelNat α) = mergeSortNaive left := by grind
      have hright : (mergeSort right).eval (sortModelNat α) = mergeSortNaive right := by grind
      have hleft' :
          Id.run (FreeM.liftM (fun {ι} q => (sortModelNat α).evalQuery q)
              (mergeSort (xs.take (xs.length / 2)))) =
            mergeSortNaive (xs.take (xs.length / 2)) := by
        simpa [left, half, Prog.eval] using hleft
      have hright' :
          Id.run (FreeM.liftM (fun {ι} q => (sortModelNat α).evalQuery q)
              (mergeSort (xs.drop (xs.length / 2)))) =
            mergeSortNaive (xs.drop (xs.length / 2)) := by
        simpa [right, half, Prog.eval] using hright
      have hmerge (a b : List α) :
          Id.run (FreeM.liftM (fun {ι} q => (sortModelNat α).evalQuery q) (merge a b)) =
            List.merge a b := by
        simpa [Prog.eval] using (merge_eval_eq_list_merge (α := α) a b)
      nth_rw 1 [mergeSort, mergeSortNaive]
      simp only [hlt, if_false, Prog.eval, bind, FreeM.liftM_bind]
      set a := Id.run <| FreeM.liftM (fun {ι} q => (sortModelNat α).evalQuery q)
          (mergeSort (List.take (xs.length / 2) xs)) with ha
      set b := Id.run <| FreeM.liftM (fun {ι} q => (sortModelNat α).evalQuery q)
          (mergeSort (List.drop (xs.length / 2) xs)) with hb
      calc
        Id.run (FreeM.liftM (fun {ι} q => (sortModelNat α).evalQuery q)
            (merge
              (Id.run <| FreeM.liftM (fun {ι} q => (sortModelNat α).evalQuery q)
                (mergeSort (List.take (xs.length / 2) xs)))
              (Id.run <| FreeM.liftM (fun {ι} q => (sortModelNat α).evalQuery q)
                (mergeSort (List.drop (xs.length / 2) xs))))) =
            Id.run (FreeM.liftM (fun {ι} q => (sortModelNat α).evalQuery q) (merge a b)) := by
          simp [a, b]
        _ = List.merge a b := by apply hmerge a b
        _ = List.merge (mergeSortNaive (List.take (xs.length / 2) xs))
              (mergeSortNaive (List.drop (xs.length / 2) xs)) := by
          simp only [hleft', hright', a, b]
      rfl
  exact hP xs rfl

lemma mergeSortNaive_length [LinearOrder α] (xs : List α) :
    (mergeSortNaive xs).length = xs.length := by
  let P : Nat → Prop :=
    fun n => ∀ ys : List α, ys.length = n → (mergeSortNaive ys).length = ys.length
  have hP : P xs.length := by
    induction hlen : xs.length using  Nat.strong_induction_on generalizing xs with
    | h n ih =>
    intro ys hlen
    by_cases hlt : ys.length < 2
    · simp [mergeSortNaive, hlt]
    · have hge : 2 ≤ ys.length := le_of_not_gt hlt
      have hpos : 0 < ys.length := lt_of_lt_of_le (by decide : 0 < (2 : Nat)) hge
      have hhalf_lt : ys.length / 2 < ys.length := by grind
      have htake_lt : (ys.take (ys.length / 2)).length < ys.length := by
        simp only [List.length_take, inf_lt_right, not_le]
        grind
      have hdrop_lt : (ys.drop (ys.length / 2)).length < ys.length := by
        simp only [List.length_drop, tsub_lt_self_iff, Nat.div_pos_iff, Nat.zero_lt_succ, true_and]
        grind
      have hleft : (mergeSortNaive (ys.take (ys.length / 2))).length =
            (ys.take (ys.length / 2)).length := by grind
      have hright : (mergeSortNaive (ys.drop (ys.length / 2))).length =
            (ys.drop (ys.length / 2)).length := by grind
      have hdiv_le : ys.length / 2 ≤ ys.length := Nat.div_le_self _ _
      rw [mergeSortNaive]
      simp [hlt, List.length_merge, hleft, hright, List.length_take, List.length_drop,
        Nat.min_eq_left hdiv_le, Nat.add_sub_of_le hdiv_le]
  exact hP xs rfl

lemma mergeSort_length [LinearOrder α] (xs : List α) :
    ((mergeSort xs).eval (sortModelNat α)).length = xs.length := by
  rw [mergeSort_is_mergeSortNaive]
  apply mergeSortNaive_length

lemma merge_sorted_sorted [LinearOrder α] (xs ys : List α)
    (hxs_mono : xs.Pairwise (· ≤ ·)) (hys_mono : ys.Pairwise (· ≤ ·)) :
    ((merge xs ys).eval (sortModelNat α)).Pairwise (· ≤ ·) := by
  rw [merge_eval_eq_list_merge]
  grind [List.pairwise_merge]

lemma mergeSortNaive_sorted [LinearOrder α] (xs : List α) :
    (mergeSortNaive xs).Pairwise (· ≤ ·) := by
  let P : Nat → Prop :=
    fun n => ∀ ys : List α, ys.length = n → (mergeSortNaive ys).Pairwise (· ≤ ·)
  have hP : P xs.length := by
    refine Nat.strong_induction_on (n := xs.length) ?_
    intro n ih ys hlen
    by_cases hlt : ys.length < 2
    · cases ys with
      | nil =>
          simp [mergeSortNaive]
      | cons y ys' =>
          cases ys' with
          | nil =>
              simp [mergeSortNaive]
          | cons z zs =>
              exact (Nat.not_lt_of_ge (by simp) hlt).elim
    · have hge : 2 ≤ ys.length := le_of_not_gt hlt
      have hpos : 0 < ys.length := lt_of_lt_of_le (by decide : 0 < (2 : Nat)) hge
      have hhalf_lt : ys.length / 2 < ys.length := by grind
      have htake_lt : (ys.take (ys.length / 2)).length < ys.length := by
        simp only [List.length_take, inf_lt_right, not_le]
        grind
      have hdrop_lt : (ys.drop (ys.length / 2)).length < ys.length := by
        simp only [List.length_drop, tsub_lt_self_iff, Nat.div_pos_iff, Nat.zero_lt_succ, true_and]
        grind
      have hleft : (mergeSortNaive (ys.take (ys.length / 2))).Pairwise (· ≤ ·) := by grind
      have hright : (mergeSortNaive (ys.drop (ys.length / 2))).Pairwise (· ≤ ·) := by grind
      rw [mergeSortNaive]
      simp only [hlt, ↓reduceIte]
      grind [List.pairwise_merge]
  exact hP xs rfl

theorem mergeSort_sorted [LinearOrder α] (xs : List α) :
    ((mergeSort xs).eval (sortModelNat α)).Pairwise (· ≤ ·) := by
  rw [mergeSort_is_mergeSortNaive]
  apply mergeSortNaive_sorted

section TimeComplexity
/- I am explicitly borrowing Sorrachai's code, which can be found in
`Cslib.AlgorithmsTheory.Lean.MergeSort.MergeSort`. But the recurrence is not needed-/

open Nat (clog)

/-- Key Lemma: ⌈log2 ⌈n/2⌉⌉ ≤ ⌈log2 n⌉ - 1 for n > 1 -/
@[grind →]
lemma clog2_half_le (n : ℕ) (h : n > 1) : clog 2 ((n + 1) / 2) ≤ clog 2 n - 1 := by
  rw [Nat.clog_of_one_lt one_lt_two h]
  grind

/-- Same logic for the floor half: ⌈log2 ⌊n/2⌋⌉ ≤ ⌈log2 n⌉ - 1 -/
@[grind →]
lemma clog2_floor_half_le (n : ℕ) (h : n > 1) : clog 2 (n / 2) ≤ clog 2 n - 1 := by
  apply Nat.le_trans _ (clog2_half_le n h)
  apply Nat.clog_monotone
  grind

@[grind .]
private lemma some_algebra (n : ℕ) :
    (n / 2 + 1) * clog 2 (n / 2 + 1) + ((n + 1) / 2 + 1) * clog 2 ((n + 1) / 2 + 1) + (n + 2) ≤
    (n + 2) * clog 2 (n + 2) := by
  -- 1. Substitution: Let N = n_1 + 2 to clean up the expression
  let N := n + 2
  have hN : N ≥ 2 := by omega
  -- 2. Rewrite the terms using N
  have t1 : n / 2 + 1 = N / 2 := by omega
  have t2 : (n + 1) / 2 + 1 = (N + 1) / 2 := by omega
  have t3 : n + 1 + 1 = N := by omega
  let k := clog 2 N
  have h_bound_l : clog 2 (N / 2) ≤ k - 1 := clog2_floor_half_le N hN
  have h_bound_r : clog 2 ((N + 1) / 2) ≤ k - 1 := clog2_half_le N hN
  have h_split : N / 2 + (N + 1) / 2 = N := by omega
  grw [t1, t2, t3, h_bound_l, h_bound_r, ←Nat.add_mul, h_split]
  exact Nat.le_refl (N * (k - 1) + N)

/-- Upper bound function for merge sort time complexity: `T(n) = n * ⌈log₂ n⌉` -/
abbrev T (n : ℕ) : ℕ := n * clog 2 n

lemma T_monotone : Monotone T := by
  intro i j h_ij
  simp only [T]
  exact Nat.mul_le_mul h_ij (Nat.clog_monotone 2 h_ij)

theorem mergeSort_complexity [LinearOrder α] (xs : List α) :
    ((mergeSort xs).time (sortModelNat α)) ≤ (T (xs.length)) := by
  fun_induction mergeSort
  · simp [T]
  · expose_names
    rw [Prog.time.bind, Prog.time.bind]
    have hmerge := merge_timeComplexity
      ((mergeSort left).eval (sortModelNat α))
      ((mergeSort right).eval (sortModelNat α))
    grw [hmerge, ih1, ih2, mergeSort_length, mergeSort_length]
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
