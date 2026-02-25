/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Models.ListComparisonSearch
public import Mathlib

@[expose] public section


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
    (listLinearSearch l x).time ListSearch.natCost ≤ 1 + l.length := by
  fun_induction l.elem x with
  | case1 => simp [listLinearSearch]
  | case2 => simp_all [listLinearSearch]
  | case3 =>
    simp_all [listLinearSearch]
    grind

-- This statement is wrong
lemma listLinearSearchM_time_complexity_lower_bound [DecidableEq α] [Nonempty α] :
    ∃ l : List α, ∃ x : α, (listLinearSearch l x).time ListSearch.natCost = l.length := by
  inhabit α
  refine ⟨[], default, ?_⟩
  simp_all [ListSearch.natCost, listLinearSearch]

end Algorithms

end Cslib
