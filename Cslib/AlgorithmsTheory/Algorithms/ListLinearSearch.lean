/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib

@[expose] public section


namespace Cslib

namespace Algorithms

open Prog

inductive ListSearch (α : Type) : Type → Type  where
  | compare (a : List α) (val : α) : ListSearch α Bool


def ListSearch_Nat [DecidableEq α] : Model (ListSearch α) ℕ where
  evalQuery q :=
    match q with
    | .compare l x => l.head? = some x
  cost q :=
    match q with
    | .compare _ _ => 1

structure CmpCount where
  cmp : ℕ
  pure : ℕ

instance : Add (CmpCount) where
  add x y := ⟨x.1 + y.1, x.2 + y.2⟩

instance : Zero (CmpCount) where
  zero := ⟨0,0⟩

instance : PureCosts (CmpCount) where
  pureCost := ⟨0,1⟩

def ListSearch_Cmp [DecidableEq α] : Model (ListSearch α) CmpCount where
  evalQuery q :=
    match q with
    | .compare l x =>  l.head? == some x
  cost q :=
    match q with
    | .compare _ _ => ⟨1,0⟩

open ListSearch in
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
      simp_all only [List.mem_cons, listLinearSearch, bind, FreeM.lift_def, pure,
        FreeM.liftBind_bind, FreeM.pure_bind, eval, FreeM.liftM, Id.run]
      split_ifs with h
      · simp
      · obtain (x_head | xtail) := x_mem_l
        · rw [x_head] at h
          simp[ListSearch_Nat] at h
        · specialize ih xtail
          exact ih

lemma listLinearSearchM_correct_false [DecidableEq α] (l : List α) :
  ∀ x : α, x ∉ l → (listLinearSearch l x).eval ListSearch_Nat = false := by
  intro x x_mem_l
  induction l with
  | nil =>
      simp_all [listLinearSearch, eval, Id.run]
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
      simp_all [listLinearSearch, ListSearch_Nat, time, PureCosts.pureCost]
  | cons head tail ih =>
      simp_all [listLinearSearch, ListSearch_Nat, time]
      split_ifs with h_head
      · simp [time, PureCosts.pureCost]
      · grind

lemma listLinearSearchM_time_complexity_lower_bound [DecidableEq α] [inon : Nontrivial α] :
  ∃ l : List α, ∃ x : α, (listLinearSearch l x).time ListSearch_Nat = 1 + l.length := by
  obtain ⟨x, y, x_neq_y⟩ := inon
  use [x,x,x,x,x,y], y
  simp_all [time, ListSearch_Nat, listLinearSearch, PureCosts.pureCost]

end Algorithms
end Cslib
