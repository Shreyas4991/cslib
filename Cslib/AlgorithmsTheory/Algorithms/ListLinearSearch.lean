/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
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
/--
Linear Search in Lists on top of the `ListSearch` query model.
-/
def listLinearSearch (l : List α) (x : α) : Prog (ListSearch α) Bool := do
  match l with
  | [] => return false
  | l :: ls =>
      let cmp : Bool ← compare (l :: ls) x
      if cmp then
        return true
      else
        listLinearSearch ls x

lemma listLinearSearchM_correct_true [DecidableEq α] (l : List α) {x : α} (x_mem_l : x ∈ l) :
    (listLinearSearch l x).eval ListSearch.natCost = true := by
  induction l with
  | nil =>
      simp_all only [List.not_mem_nil]
  | cons head tail ih =>
      simp_all only [eval, List.mem_cons, listLinearSearch, FreeM.lift_def, FreeM.pure_eq_pure,
        FreeM.bind_eq_bind, FreeM.liftBind_bind, FreeM.pure_bind, FreeM.liftM_liftBind,
        LawfulMonad.pure_bind]
      split_ifs with h
      · obtain (x_head | xtail) := x_mem_l
        · rw [x_head] at h
          simp only [ListSearch.natCost, List.head?_cons] at h
          simp
        · specialize ih xtail
          simp
      · obtain (x_head | x_tail) := x_mem_l
        · rw [x_head] at h
          simp [ListSearch.natCost, List.head?_cons] at h
        · specialize ih x_tail
          simp_all


lemma listLinearSearchM_correct_false [DecidableEq α] (l : List α) {x : α} (x_mem_l : x ∉ l) :
    (listLinearSearch l x).eval ListSearch.natCost = false := by
  induction l with
  | nil =>
      simp_all [listLinearSearch, eval]
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at x_mem_l
      specialize ih x_mem_l.2
      simp only [eval, listLinearSearch, bind, FreeM.lift_def, FreeM.pure_eq_pure,
        FreeM.liftBind_bind, FreeM.pure_bind, FreeM.liftM_liftBind]
      split_ifs with h_eq
      · simp only [pure, ListSearch.natCost, List.head?_cons] at h_eq
        grind
      · assumption

lemma listLinearSearch_correctness [DecidableEq α] (l : List α) (x : α) :
  (listLinearSearch l x).eval ListSearch.natCost = l.contains x := by
  by_cases hlx : l.contains x
  · grind [listLinearSearchM_correct_true]
  · grind [listLinearSearchM_correct_false]

lemma listLinearSearchM_time_complexity_upper_bound [DecidableEq α] (l : List α) (x : α) :
  (listLinearSearch l x).time ListSearch.natCost ≤ 1 + l.length := by
  induction l with
  | nil =>
      simp_all [listLinearSearch, ListSearch.natCost, time]
  | cons head tail ih =>
      simp_all [listLinearSearch, ListSearch.natCost]
      split_ifs with h_head
      · simp
      · grind

lemma listLinearSearchM_time_complexity_lower_bound [DecidableEq α] [inon : Nontrivial α] :
    ∃ l : List α, ∃ x : α, (listLinearSearch l x).time ListSearch.natCost = l.length := by
  obtain ⟨x, y, x_neq_y⟩ := inon
  use [x,x,x,x,x,y], y
  simp_all [ListSearch.natCost, listLinearSearch]

end Algorithms

end Cslib
