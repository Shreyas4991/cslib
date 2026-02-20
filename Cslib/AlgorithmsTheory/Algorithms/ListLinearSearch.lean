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

lemma listLinearSearchM_correct_true [iDec : DecidableEq α] (l : List α) :
  ∀ x : α, x ∈ l → (listLinearSearch l x).eval ListSearch_Nat = true := by
  intro x x_mem_l
  induction l with
  | nil =>
      simp_all only [List.not_mem_nil]
  | cons head tail ih =>
      simp_all only [eval, List.mem_cons, listLinearSearch, FreeM.lift_def, FreeM.pure_eq_pure,
        FreeM.bind_eq_bind, FreeM.liftBind_bind, FreeM.pure_bind, FreeM.liftM_liftBind, pure_bind]
      split_ifs with h
      · obtain (x_head | xtail) := x_mem_l
        · rw [x_head] at h
          simp only [ListSearch_Nat, List.head?_cons, decide_true] at h
          simp
        · specialize ih xtail
          simp
      · obtain (x_head | x_tail) := x_mem_l
        · rw [x_head] at h
          simp [ListSearch_Nat, List.head?_cons, decide_true] at h
        · specialize ih x_tail
          simp_all
lemma listLinearSearchM_correct_false [DecidableEq α] (l : List α) :
  ∀ x : α, x ∉ l → (listLinearSearch l x).eval ListSearch_Nat = false := by
  intro x x_mem_l
  induction l with
  | nil =>
      simp_all [listLinearSearch, eval]
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at x_mem_l
      specialize ih x_mem_l.2
      simp only [listLinearSearch, bind, FreeM.lift_def, pure, FreeM.liftBind_bind, FreeM.pure_bind,
        eval, FreeM.liftM, Id.run]
      split_ifs with h_eq
      · simp [ListSearch_Nat] at h_eq
        exfalso
        exact x_mem_l.1 h_eq.symm
      · exact ih



lemma listLinearSearchM_time_complexity_upper_bound [DecidableEq α] (l : List α) :
  ∀ x : α, (listLinearSearch l x).time ListSearch_Nat ≤ 1 + l.length := by
  intro x
  induction l with
  | nil =>
      simp_all [listLinearSearch, ListSearch_Nat, time]
  | cons head tail ih =>
      simp_all [listLinearSearch, ListSearch_Nat]
      split_ifs with h_head
      · simp [time]
      · grind

lemma listLinearSearchM_time_complexity_lower_bound [DecidableEq α] [inon : Nontrivial α] :
  ∃ l : List α, ∃ x : α, (listLinearSearch l x).time ListSearch_Nat = l.length := by
  obtain ⟨x, y, x_neq_y⟩ := inon
  use [x,x,x,x,x,y], y
  simp_all [ListSearch_Nat, listLinearSearch]


end Algorithms
end Cslib
