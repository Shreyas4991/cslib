/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Models.ListComparisonSort

@[expose] public section

namespace Cslib.Algorithms

open SortOps


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

lemma mergeNaive_length [LinearOrder α] (x y : List α) :
  (mergeNaive x y).length = x.length + y.length := by
  fun_induction mergeNaive <;> try grind


/-- Merge two sorted lists using comparisons in the query monad. -/
@[simp]
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

lemma merge_bind_pure_insert_x [LinearOrder α] (x y : α) (xs ys : List α) :
  (Prog.time
      (FreeM.bind (merge xs (y :: ys)) (fun rest => FreeM.pure (x :: rest))) (sortModelNat α))
      = (merge xs (y :: ys)).time (sortModelNat α) := by
  have h := Prog.time.bind (sortModelNat α) (merge xs (y :: ys))
    (fun rest => FreeM.pure (x :: rest))
  have h' : Prog.time (FreeM.bind (merge xs (y :: ys)) (fun rest => FreeM.pure (x :: rest)))
              (sortModelNat α) + 1 = (merge xs (y :: ys)).time (sortModelNat α) + 1 := by
      simpa using h
  exact Nat.add_right_cancel h'

lemma merge_bind_pure_insert_y [LinearOrder α] (x y : α) (xs ys : List α) :
  (Prog.time
    (FreeM.bind (merge (x :: xs) ys) (fun rest => FreeM.pure (y :: rest))) (sortModelNat α))
    = (merge (x :: xs) ys).time (sortModelNat α) := by
  have h := Prog.time.bind (sortModelNat α) (merge (x :: xs) ys)
    (fun rest => FreeM.pure (y :: rest))
  have h' : Prog.time (FreeM.bind (merge (x :: xs) ys) (fun rest => FreeM.pure (y :: rest)))
              (sortModelNat α) + 1 = (merge (x :: xs) ys).time (sortModelNat α) + 1 := by
    simpa using h
  exact Nat.add_right_cancel h'

lemma merge_timeComplexity [LinearOrder α] (x y : List α) :
  (merge x y).time (sortModelNat α) ≤  x.length + y.length := by
  fun_induction merge
  · simp
  · simp
  · expose_names
    simp only [bind, FreeM.lift_def, pure, FreeM.liftBind_bind, FreeM.pure_bind, sortModelNat,
      Bool.if_false_right, Bool.and_true, Prog.time.eq_2, decide_eq_true_eq, List.length_cons]
    split_ifs with hxy
    · have hbind := merge_bind_pure_insert_x x y xs' ys'
      simp only [sortModelNat, Bool.if_false_right, Bool.and_true] at hbind
      rw [hbind]
      have hih :
          (merge xs' (y :: ys')).time (sortModelNat α) ≤
            xs'.length + (y :: ys').length := by
        simpa using ih2
      have h := Nat.add_le_add_left hih 1
      simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    · have hbind := merge_bind_pure_insert_y x y xs' ys'
      simp only [sortModelNat, Bool.if_false_right, Bool.and_true] at hbind
      rw [hbind]
      have hih :
          (merge (x :: xs') ys').time (sortModelNat α) ≤
            (x :: xs').length + ys'.length := by
        simpa using ih1
      have h := Nat.add_le_add_left hih 1
      simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h


lemma merge_is_mergeNaive [LinearOrder α] (x y : List α) :
  (merge x y).eval (sortModelNat α) = mergeNaive x y := by
  fun_induction mergeNaive
  · simp [merge]
  · simp [merge]
  · expose_names
    simp_all [Prog.eval,  merge, rest, sortModelNat]
  · expose_names
    simp_all [Prog.eval, merge, rest]

lemma merge_length [LinearOrder α] (x y : List α) :
  ((merge x y).eval (sortModelNat α)).length = x.length + y.length := by
  rw [merge_is_mergeNaive]
  apply mergeNaive_length

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
  (mergeSort xs).eval (sortModelNat α) = mergeSortNaive xs := by
  classical
  let P : Nat → Prop :=
    fun n => ∀ xs, xs.length = n → (mergeSort xs).eval (sortModelNat α) = mergeSortNaive xs
  have hP : P xs.length := by
    refine Nat.strong_induction_on (n := xs.length) ?_
    intro n ih xs hlen
    by_cases hlt : xs.length < 2
    · nth_rewrite 1 [mergeSort]
      nth_rewrite 1 [mergeSortNaive]
      simp [hlt, Prog.eval]
    · have hge : 2 ≤ xs.length := by
        exact le_of_not_gt hlt
      have hpos : 0 < xs.length := by
        exact lt_of_lt_of_le (by decide : 0 < (2 : Nat)) hge
      set half : Nat := xs.length / 2
      set left : List α := xs.take half
      set right : List α := xs.drop half
      have hhalf_lt : half < xs.length := by
        have h2 : 1 < (2 : Nat) := by decide
        simpa [half] using (Nat.div_lt_self hpos h2)
      have hleft_le : left.length ≤ half := by
        simp [left, List.length_take]
      have hleft_lt_len : left.length < xs.length :=
        lt_of_le_of_lt hleft_le hhalf_lt
      have hright_lt_len : right.length < xs.length := by
        have hhalf_pos : 0 < half := by
          have h2 : 0 < (2 : Nat) := by decide
          simpa [half] using (Nat.div_pos hge h2)
        have hsub : xs.length - half < xs.length := Nat.sub_lt hpos hhalf_pos
        simpa [right, List.length_drop, half] using hsub
      have hleft :
          (mergeSort left).eval (sortModelNat α) = mergeSortNaive left :=
        (ih left.length (by simpa [hlen] using hleft_lt_len)) left rfl
      have hright :
          (mergeSort right).eval (sortModelNat α) = mergeSortNaive right :=
        (ih right.length (by simpa [hlen] using hright_lt_len)) right rfl
      have hleft' :
          FreeM.liftM (m := Id) (fun {ι} q => (sortModelNat α).evalQuery q)
              (mergeSort (xs.take (xs.length / 2))) =
            mergeSortNaive (xs.take (xs.length / 2)) := by
        simpa [left, half, Prog.eval, Id.run] using hleft
      have hright' :
          FreeM.liftM (m := Id) (fun {ι} q => (sortModelNat α).evalQuery q)
              (mergeSort (xs.drop (xs.length / 2))) =
            mergeSortNaive (xs.drop (xs.length / 2)) := by
        simpa [right, half, Prog.eval, Id.run] using hright
      have hmerge (a b : List α) :
          FreeM.liftM (m := Id) (fun {ι} q => (sortModelNat α).evalQuery q) (merge a b) =
            mergeNaive a b := by
        simpa [Prog.eval, Id.run] using (merge_is_mergeNaive (α := α) a b)
      nth_rewrite 1 [mergeSort]
      nth_rewrite 1 [mergeSortNaive]
      simp only [hlt, if_false, Prog.eval, Id.run, bind, pure, FreeM.liftM_bind]
      set a :=
        FreeM.liftM (m := Id) (fun {ι} q => (sortModelNat α).evalQuery q)
          (mergeSort (List.take (xs.length / 2) xs))
      set b :=
        FreeM.liftM (m := Id) (fun {ι} q => (sortModelNat α).evalQuery q)
          (mergeSort (List.drop (xs.length / 2) xs))
      calc
        FreeM.liftM (m := Id) (fun {ι} q => (sortModelNat α).evalQuery q)
            (merge
              (FreeM.liftM (m := Id) (fun {ι} q => (sortModelNat α).evalQuery q)
                (mergeSort (List.take (xs.length / 2) xs)))
              (FreeM.liftM (m := Id) (fun {ι} q => (sortModelNat α).evalQuery q)
                (mergeSort (List.drop (xs.length / 2) xs)))) =
            FreeM.liftM (m := Id) (fun {ι} q => (sortModelNat α).evalQuery q) (merge a b) := by
          simp [a, b]
        _ = mergeNaive a b := hmerge a b
        _ = mergeNaive (mergeSortNaive (List.take (xs.length / 2) xs))
              (mergeSortNaive (List.drop (xs.length / 2) xs)) := by
          simp only [a, b, hleft', hright']
  exact hP xs rfl


lemma mergeSortNaive_length [LinearOrder α] (xs : List α) :
  (mergeSortNaive xs).length = xs.length := by
  let P : Nat → Prop :=
    fun n => ∀ ys : List α, ys.length = n → (mergeSortNaive ys).length = ys.length
  have hP : P xs.length := by
    refine Nat.strong_induction_on xs.length ?_
    intro n ih ys hlen
    by_cases hlt : ys.length < 2
    · simp [mergeSortNaive, hlt]
    · have hge : 2 ≤ ys.length := le_of_not_gt hlt
      have hpos : 0 < ys.length := lt_of_lt_of_le (by decide : 0 < (2 : Nat)) hge
      have hhalf_lt : ys.length / 2 < ys.length := by
        have htwo : 1 < (2 : Nat) := by decide
        simpa using Nat.div_lt_self hpos htwo
      have htake_lt : (ys.take (ys.length / 2)).length < ys.length := by
        have htake_le : (ys.take (ys.length / 2)).length ≤ ys.length / 2 := by
          simp [List.length_take]
        exact lt_of_le_of_lt htake_le hhalf_lt
      have hdrop_lt : (ys.drop (ys.length / 2)).length < ys.length := by
        have hhalf_pos : 0 < ys.length / 2 := by
          have htwo : 0 < (2 : Nat) := by decide
          simpa using Nat.div_pos hge htwo
        have hsub : ys.length - ys.length / 2 < ys.length := Nat.sub_lt hpos hhalf_pos
        simpa [List.length_drop] using hsub
      have hleft :
          (mergeSortNaive (ys.take (ys.length / 2))).length =
            (ys.take (ys.length / 2)).length := by
        exact ih (ys.take (ys.length / 2)).length
          (by simpa [hlen] using htake_lt) (ys.take (ys.length / 2)) rfl
      have hright :
          (mergeSortNaive (ys.drop (ys.length / 2))).length =
            (ys.drop (ys.length / 2)).length := by
        exact ih (ys.drop (ys.length / 2)).length
          (by simpa [hlen] using hdrop_lt) (ys.drop (ys.length / 2)) rfl
      have hdiv_le : ys.length / 2 ≤ ys.length := Nat.div_le_self _ _
      rw [mergeSortNaive]
      simp [hlt, mergeNaive_length, hleft, hright, List.length_take, List.length_drop,
        Nat.min_eq_left hdiv_le, Nat.add_sub_of_le hdiv_le]
  exact hP xs rfl

lemma mergeSort_length [LinearOrder α] (xs : List α) :
  ((mergeSort xs).eval (sortModelNat α)).length = xs.length := by
  rw [mergeSort_is_mergeSortNaive]
  apply mergeSortNaive_length


lemma mergeNaive_mem [LinearOrder α] (xs ys : List α) :
  x ∈ mergeNaive xs ys → x ∈ xs ∨ x ∈ ys := by
  fun_induction mergeNaive
  · simp
  · simp
  · expose_names
    intro h
    simp only [List.mem_cons] at h
    obtain h | h := h
    · left
      simp [h]
    · simp only [rest] at h
      specialize ih1 h
      obtain ih | ih := ih1
      · simp only [List.mem_cons]
        tauto
      · right; exact ih
  · expose_names
    intro h
    simp only [List.mem_cons, rest] at h
    obtain h | h := h
    · simp only [List.mem_cons]
      tauto
    · specialize ih1 h
      tauto

lemma mergeNaive_sorted_sorted [LinearOrder α] (xs ys : List α)
  (hxs_mono : xs.Pairwise (· ≤ ·)) (hys_mono : ys.Pairwise (· ≤ ·)) :
  (mergeNaive xs ys).Pairwise (· ≤ ·) := by
  induction xs generalizing ys with
  | nil =>
      simp_all [mergeNaive]
  | cons xhead xtail x_ih =>
      induction ys with
      | nil =>
          simp_all [mergeNaive]
      | cons yhead ytail y_ih =>
          simp only [mergeNaive]
          by_cases hxy : xhead < yhead
          · simp only [hxy, ↓reduceIte, List.pairwise_cons]
            refine ⟨?_, ?_⟩
            · intro a a_mem
              apply mergeNaive_mem at a_mem
              simp_all only [List.pairwise_cons, List.mem_cons, forall_const]
              obtain ⟨left, right⟩ := hxs_mono
              obtain ⟨left_1, right_1⟩ := hys_mono
              cases a_mem with
              | inl h => simp_all only
              | inr h_1 =>
                cases h_1 with
                | inl h =>
                  subst h
                  grind
                | inr h_2 => grind
            · simp_all
          · simp only [hxy, ↓reduceIte, List.pairwise_cons]
            refine ⟨?_, ?_⟩
            · intro a a_mem
              apply mergeNaive_mem at a_mem
              simp_all only [List.pairwise_cons, not_lt, List.mem_cons, forall_const]
              obtain ⟨left, right⟩ := hxs_mono
              obtain ⟨left_1, right_1⟩ := hys_mono
              cases a_mem with
              | inl h =>
                cases h with
                | inl h_1 =>
                  subst h_1
                  simp_all only
                | inr h_2 => grind
              | inr h_1 => simp_all only
            · simp_all


lemma merge_sorted_sorted [LinearOrder α] (xs ys : List α)
  (hxs_mono : xs.Pairwise (· ≤ ·)) (hys_mono : ys.Pairwise (· ≤ ·)) :
  ((merge xs ys).eval (sortModelNat α)).Pairwise (· ≤ ·) := by
  rw [merge_is_mergeNaive]
  apply mergeNaive_sorted_sorted
  all_goals assumption

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
      have hhalf_lt : ys.length / 2 < ys.length := by
        have htwo : 1 < (2 : Nat) := by decide
        simpa using Nat.div_lt_self hpos htwo
      have htake_lt : (ys.take (ys.length / 2)).length < ys.length := by
        have htake_le : (ys.take (ys.length / 2)).length ≤ ys.length / 2 := by
          simp [List.length_take]
        exact lt_of_le_of_lt htake_le hhalf_lt
      have hdrop_lt : (ys.drop (ys.length / 2)).length < ys.length := by
        have hhalf_pos : 0 < ys.length / 2 := by
          have htwo : 0 < (2 : Nat) := by decide
          simpa using Nat.div_pos hge htwo
        have hsub : ys.length - ys.length / 2 < ys.length := Nat.sub_lt hpos hhalf_pos
        simpa [List.length_drop] using hsub
      have hleft :
          (mergeSortNaive (ys.take (ys.length / 2))).Pairwise (· ≤ ·) := by
        exact ih (ys.take (ys.length / 2)).length
          (by simpa [hlen] using htake_lt) (ys.take (ys.length / 2)) rfl
      have hright :
          (mergeSortNaive (ys.drop (ys.length / 2))).Pairwise (· ≤ ·) := by
        exact ih (ys.drop (ys.length / 2)).length
          (by simpa [hlen] using hdrop_lt) (ys.drop (ys.length / 2)) rfl
      rw [mergeSortNaive]
      simpa [hlt] using mergeNaive_sorted_sorted
        (mergeSortNaive (ys.take (ys.length / 2)))
        (mergeSortNaive (ys.drop (ys.length / 2))) hleft hright
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
