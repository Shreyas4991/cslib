/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.RunsIn
public import Cslib.Algorithms.Lean.Query.InsertionSort.Defs
import Std.Tactic.Do
public import Mathlib.Data.List.Sort

open Std.Do Cslib.Query TimeT

set_option mvcgen.warning false

public section

namespace Cslib.Query

/-- `orderedInsert` produces a permutation of `x :: xs`, for any non-failing monadic comparator. -/
public theorem orderedInsert_perm {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (x : α) (xs : List α) :
    ⦃⌜True⌝⦄ orderedInsert cmp x xs ⦃⇓result => ⌜List.Perm result (x :: xs)⌝⦄ := by
  induction xs with
  | nil =>
    simp only [orderedInsert]
    mvcgen
  | cons y ys ih =>
    simp only [orderedInsert]
    mvcgen [ih, hcmp]
    · mpure_intro; exact (List.Perm.cons _ ‹_›).trans (List.Perm.swap _ _ _)

/-- Variant of `orderedInsert_perm` with a permutation precondition:
    if `sorted` is a permutation of `xs`,
    then `orderedInsert` produces a permutation of `x :: xs`. -/
private theorem orderedInsert_perm' {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (x : α) (xs : List α) (sorted : List α) :
    ⦃⌜List.Perm sorted xs⌝⦄ orderedInsert cmp x sorted
      ⦃⇓ result => ⌜List.Perm result (x :: xs)⌝⦄ := by
  simp only [Triple]
  apply SPred.pure_elim'
  intro hsorted
  exact Triple.entails_wp_of_post (orderedInsert_perm cmp hcmp x sorted) (by
    simp only [PostCond.entails_noThrow]
    intro result
    exact SPred.pure_mono fun hperm => hperm.trans (List.Perm.cons x hsorted))

-- To make this a complete example we should show that
-- * `orderedInsert` is sorted if the input is sorted, and
-- * `insertionSort` is sorted.
-- Both of these require us state that `cmp` is actually a reasonable ordering,
-- despite being monadic.

/-- `insertionSort` produces a permutation of its input, for any non-failing monadic comparator. -/
public theorem insertionSort_perm {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (xs : List α) :
    ⦃⌜True⌝⦄ insertionSort cmp xs ⦃⇓result => ⌜List.Perm result xs⌝⦄ := by
  induction xs with
  | nil =>
    simp only [insertionSort]
    mvcgen
  | cons x xs ih =>
    simp only [insertionSort]
    have := orderedInsert_perm' cmp hcmp x xs
    mvcgen [ih, this]

/-- `orderedInsert` uses at most `xs.length` queries. -/
public theorem orderedInsert_runsIn (x : α) :
    RunsIn (fun cmp xs => orderedInsert cmp x xs) List.length := by
  change ∀ (query : (α × α) → TimeM Bool), (∀ a, TimeT.Costs (query a) 1) →
    ∀ xs, TimeT.Costs (orderedInsert query x xs) xs.length
  intro query hquery xs
  induction xs with
  | nil =>
    simp only [orderedInsert]
    exact Costs.pure _
  | cons y ys ih =>
    dsimp only [orderedInsert]
    apply Costs.le
    · exact Costs.bind (hquery (x, y)) fun lt =>
        Costs.ite lt (Costs.pure_le _ _) (Costs.map ih)
    · simp only [List.length]; omega

/-- `insertionSort` uses at most `xs.length ^ 2` queries. -/
public theorem insertionSort_runsIn :
    RunsIn (insertionSort (α := α)) (fun xs => xs.length * xs.length) := by
  change ∀ (query : (α × α) → TimeM Bool), (∀ a, TimeT.Costs (query a) 1) →
    ∀ xs, TimeT.Costs (insertionSort query xs) (xs.length * xs.length)
  intro query hquery xs
  induction xs with
  | nil =>
    simp only [insertionSort]
    exact Costs.pure _
  | cons x xs ih =>
    dsimp only [insertionSort]
    apply Costs.le
    · exact Costs.bind_spec ih
        (insertionSort_perm query (fun p => SPred.pure_intro trivial) xs)
        fun sorted hperm => by
          have := orderedInsert_runsIn x query hquery sorted
          rwa [List.Perm.length_eq hperm] at this
    · simp only [List.length]; have := Nat.mul_succ xs.length xs.length; grind

/-- The monadic `orderedInsert` at `m := Id` agrees with `List.orderedInsert`. -/
public theorem id_run_orderedInsert (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    Id.run (orderedInsert (fun p => decide (r p.1 p.2)) x xs) = List.orderedInsert r x xs := by
  induction xs with
  | nil => simp [orderedInsert, Id.run, Pure.pure]
  | cons y ys ih =>
    simp only [Id.run] at ih
    simp only [orderedInsert, Id.run, List.orderedInsert_cons, Pure.pure, Bind.bind, ih]
    split <;> simp_all [decide_eq_true_eq]

/-- The monadic `insertionSort` at `m := Id` agrees with `List.insertionSort`. -/
public theorem id_run_insertionSort (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    Id.run (insertionSort (fun p => decide (r p.1 p.2)) xs) = List.insertionSort r xs := by
  induction xs with
  | nil => simp [insertionSort, Id.run, Pure.pure]
  | cons x xs ih =>
    simp only [Id.run] at ih
    simp only [insertionSort, Id.run, List.insertionSort_cons, Bind.bind, ih]
    exact id_run_orderedInsert r x (List.insertionSort r xs)

end Cslib.Query

end -- public section
