/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.RunsIn
public import Cslib.Algorithms.Lean.Query.MergeSort.Defs
import Std.Tactic.Do
import Mathlib.Tactic.Linarith
public import Mathlib.Data.Nat.Log

open Std.Do Cslib.Query TimeT

set_option mvcgen.warning false

namespace Cslib.Query

/-- The monadic `merge` at `m := Id` agrees with `List.merge`. -/
public theorem id_run_merge (le : α → α → Bool) (xs ys : List α) :
    Id.run (merge (fun p => le p.1 p.2) xs ys) = List.merge xs ys le := by
  fun_induction merge (m := Id) (fun p => le p.1 p.2) xs ys with
  | case1 => simp [Id.run, Pure.pure]
  | case2 xs => simp [Id.run, Pure.pure, List.merge_right]
  | case3 x xs y ys ih_t ih_f =>
    simp only [Id.run] at ih_t ih_f ⊢
    simp only [Bind.bind, Pure.pure]
    rw [List.cons_merge_cons]
    split <;> simp_all

-- Unlike `id_run_merge` above, we don't prove a conformance lemma
-- `id_run_mergeSort : Id.run (mergeSort ...) = List.mergeSort ...`
-- because Lean's `module` system does not expose equational lemmas
-- (e.g. `List.mergeSort.eq_3`) to downstream modules.
-- Instead, we validate our definition via specifications:
-- `merge_perm`, `mergeSort_perm`, and `mergeSort_runsIn`.

/-- `merge` produces a permutation of `xs ++ ys`, for any non-failing monadic comparator. -/
public theorem merge_perm {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (xs ys : List α) :
    ⦃⌜True⌝⦄ merge cmp xs ys ⦃⇓result => ⌜List.Perm result (xs ++ ys)⌝⦄ := by
  fun_induction merge (m := m) cmp xs ys with
  | case1 => mvcgen
  | case2 xs =>
    mvcgen
    · mpure_intro; simp [List.append_nil]
  | case3 x xs y ys ih_t ih_f =>
    mvcgen [ih_t, ih_f, hcmp]
    · mpure_intro; exact List.Perm.cons _ ‹_›
    · mpure_intro
      exact (List.Perm.cons _ ‹_›).trans
        ((List.Perm.swap x y _).trans (List.Perm.cons x (List.perm_middle.symm)))

/-- `mergeSort` produces a permutation of its input, for any non-failing monadic comparator. -/
public theorem mergeSort_perm {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (xs : List α) :
    ⦃⌜True⌝⦄ mergeSort cmp xs ⦃⇓result => ⌜List.Perm result xs⌝⦄ := by
  fun_induction mergeSort (m := m) cmp xs with
  | case1 => mvcgen
  | case2 => mvcgen
  | case3 a b xs lr _ _ ih_left ih_right =>
    have hmerge := merge_perm cmp hcmp
    mvcgen [ih_left, ih_right, hmerge]
    · apply SPred.pure_mono
      intro h_merge
      rename_i _ _ _ h_left _ h_right _
      have hsplit := List.MergeSort.Internal.splitInTwo_fst_append_splitInTwo_snd
        ⟨a :: b :: xs, rfl⟩
      exact h_merge.trans ((h_left.append h_right).trans (.of_eq hsplit))

/-- `merge` uses at most `xs.length + ys.length` queries. -/
public theorem merge_costs (query : (α × α) → TimeM Bool) (hquery : ∀ a, Costs (query a) 1)
    (xs ys : List α) : Costs (merge query xs ys) (xs.length + ys.length) := by
  fun_induction merge (m := TimeM) query xs ys with
  | case1 => exact Costs.pure_le _ _
  | case2 xs => exact Costs.pure_le _ _
  | case3 x xs y ys ih_t ih_f =>
    apply Costs.le
    · exact Costs.bind (hquery (x, y)) fun le =>
        Costs.ite_max le (Costs.map ih_t) (Costs.map ih_f)
    · simp only [List.length_cons]; omega

/-- The key arithmetic inequality for the merge sort recurrence:
`⌈n/2⌉ * clog(⌈n/2⌉) + ⌊n/2⌋ * clog(⌊n/2⌋) + n ≤ n * clog(n)`. -/
private theorem mergeSort_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n + 1) / 2) * Nat.clog 2 ((n + 1) / 2) +
      (n / 2 * Nat.clog 2 (n / 2) + ((n + 1) / 2 + n / 2)) ≤
      n * Nat.clog 2 n := by
  -- clog n = clog ⌈n/2⌉ + 1
  have hclog := Nat.clog_of_one_lt (by omega : (1 : Nat) < 2) hn
  have hceil : Nat.clog 2 ((n + 1) / 2) + 1 ≤ Nat.clog 2 n := le_of_eq hclog.symm
  have hfloor : Nat.clog 2 (n / 2) + 1 ≤ Nat.clog 2 n :=
    (Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1).trans hceil
  have hsum : (n + 1) / 2 + n / 2 = n := by omega
  have h1 := Nat.mul_le_mul_left ((n + 1) / 2) hceil
  have h2 := Nat.mul_le_mul_left (n / 2) hfloor
  nlinarith [
    Nat.mul_succ ((n + 1) / 2) (Nat.clog 2 ((n + 1) / 2)),
    Nat.mul_succ (n / 2) (Nat.clog 2 (n / 2))]

/-- `mergeSort` uses at most `xs.length * Nat.clog 2 xs.length` queries. -/
public theorem mergeSort_runsIn :
    RunsIn (mergeSort (α := α)) (fun xs => xs.length * Nat.clog 2 xs.length) := by
  change ∀ (query : (α × α) → TimeM Bool), (∀ a, Costs (query a) 1) →
    ∀ xs, Costs (mergeSort query xs) (xs.length * Nat.clog 2 xs.length)
  intro query hquery xs
  fun_induction mergeSort (m := TimeM) query xs with
  | case1 => exact Costs.pure _
  | case2 => exact Costs.pure _
  | case3 a b xs lr _ _ ih_left ih_right =>
    have hperm := mergeSort_perm query (fun p => SPred.pure_intro trivial)
    apply Costs.le
    · exact Costs.bind_spec ih_left (hperm _) fun left h_perm_left =>
        Costs.bind_spec ih_right (hperm _) fun right h_perm_right => by
          have := merge_costs query hquery left right
          rwa [h_perm_left.length_eq, h_perm_right.length_eq] at this
    · simp only [lr.1.2, lr.2.2]
      exact mergeSort_bound _ (by simp only [List.length_cons]; omega)

end Cslib.Query
