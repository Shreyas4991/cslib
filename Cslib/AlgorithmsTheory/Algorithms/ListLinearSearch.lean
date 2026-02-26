/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Models.ListComparisonSearch
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Set

@[expose] public section

/-!
# Linear search in a list

In this file we state and prove the correctness and complexity of linear search in lists under
the `ListSearch` model.
--

## Main Definitions

- `listLinearSearch` : Linear search algorithm in the `ListSearch` query model

## Main results

- `listLinearSearch_eval`: `insertOrd` evaluates identically to `List.contains`.
- `listLinearSearchM_time_complexity_upper_bound` : `linearSearch` takes at most `n`
  comparison operations
- `listLinearSearchM_time_complexity_lower_bound` : There exist lists on which `linearSearch` needs
  `n` comparisons
-/
namespace Cslib

namespace Algorithms

open Prog

open ListSearch in
/-- Linear Search in Lists on top of the `ListSearch` query model. -/
def listLinearSearch (l : List α) (x : α) : Prog (ListSearch α) Bool := do
  match l with
  | [] => return false
  | l :: ls =>
    let cmp : Bool ← compare (l :: ls) x
    if cmp then
      return true
    else
      listLinearSearch ls x

@[simp, grind =]
lemma listLinearSearch_eval [BEq α] (l : List α) (x : α) :
    (listLinearSearch l x).eval ListSearch.natCost = l.contains x := by
  fun_induction l.elem x with simp_all [listLinearSearch]

lemma listLinearSearchM_correct_true [BEq α] [LawfulBEq α] (l : List α)
    {x : α} (x_mem_l : x ∈ l) : (listLinearSearch l x).eval ListSearch.natCost = true := by
  simp [x_mem_l]

lemma listLinearSearchM_correct_false [BEq α] [LawfulBEq α] (l : List α)
    {x : α} (x_mem_l : x ∉ l) : (listLinearSearch l x).eval ListSearch.natCost = false := by
  simp [x_mem_l]

lemma listLinearSearchM_time_complexity_upper_bound [BEq α] (l : List α) (x : α) :
    (listLinearSearch l x).time ListSearch.natCost ≤ l.length := by
  fun_induction l.elem x with
  | case1 => simp [listLinearSearch]
  | case2 => simp_all [listLinearSearch]
  | case3 =>
    simp_all [listLinearSearch]
    grind

lemma listLinearSearchM_time_complexity_lower_bound [DecidableEq α] [Nontrivial α] :
    ∀ n, ∃ l : List α, ∃ x : α, l.length = n
      ∧ (listLinearSearch l x).time ListSearch.natCost = l.length := by
  intro n
  obtain ⟨x, y, hneq⟩ := exists_pair_ne α
  use (List.replicate n y), x
  refine ⟨?_, ?_⟩
  · simp
  · induction n with
    | zero => simp [listLinearSearch, List.replicate]
    | succ m ih =>
      simp only [List.replicate, listLinearSearch, FreeM.lift_def, FreeM.pure_eq_pure,
        FreeM.bind_eq_bind, FreeM.liftBind_bind, FreeM.pure_bind, time_liftBind,
        ListSearch.natCost_cost, ListSearch.natCost_evalQuery, List.head?_cons,
        Option.some_beq_some, beq_iff_eq, List.length_cons, List.length_replicate]
      split_ifs with hxy_eq
      · exfalso
        tauto
      · rw [ih, List.length_replicate, add_comm]


end Algorithms

end Cslib
