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

lemma List_Monotone_tail [LinearOrder α] (l : List α) (x : α) :
  Monotone (x :: l).get → Monotone l.get := by
  intro h
  simp_all only [Monotone, List.length_cons, List.get_eq_getElem]
  intro i j hij
  have : i.castSucc + 1 ≤ j.castSucc + 1 := by
    simp only [Fin.coeSucc_eq_succ, Fin.succ_le_succ_iff]
    exact hij
  specialize @h (i.castSucc + 1) (j.castSucc + 1) this
  simp_all only [Fin.coeSucc_eq_succ, Fin.val_succ, List.getElem_cons_succ]

lemma List.cons_get_pred_get (l : List α) (x : α)
  (i : Fin (x :: l).length) (hi : i > ⟨0, by grind⟩) :
  (x :: l).get i = l.get (i.pred (by aesop)) := by
  grind

lemma List_Monotone_of_cons [LinearOrder α] (tail : List α) (head : α) :
  Monotone (head :: tail).get ↔ Monotone tail.get ∧ ∀ y ∈ tail, head ≤ y := by
  constructor
  · intro mono
    constructor
    · apply List_Monotone_tail at mono
      assumption
    · intro y y_tail
      obtain ⟨i,hi⟩ := List.get_of_mem y_tail
      simp only [Monotone, List.length_cons, List.get_eq_getElem] at mono
      specialize @mono 0 (i.castSucc + 1) (by simp)
      simp_all
  · intro ⟨htail_mono, h_head⟩ i j hij
    by_cases hi_eq_j : i = j
    · rw [hi_eq_j]
    · apply Std.lt_of_le_of_ne at hij
      apply hij at hi_eq_j
      have s₁ : ⟨0, by grind⟩ < j := by
        grind
      have s₂ : (head :: tail).get j ∈ tail := by
        grind
      by_cases hi_zero : i = ⟨0, by grind⟩
      · rw [hi_zero]
        simp only [List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.coe_ofNat_eq_mod,
          Nat.zero_mod, List.getElem_cons_zero, ge_iff_le]
        specialize h_head (head :: tail)[↑j] s₂
        exact h_head
      · have s₃ : i > ⟨0, by grind⟩ := by
          grind
        rw [List.cons_get_pred_get, List.cons_get_pred_get]
        · apply htail_mono
          grind
        · exact s₁
        · exact s₃

lemma List_Monotone_cons [LinearOrder α] (tail : List α) (x head : α)
  (hx : x ≤ head) (h_mono : Monotone (head :: tail).get) : Monotone (x :: head :: tail).get := by
  have s₁ : ∀ y ∈ tail, head ≤ y := by
    intro x x_in_tail
    simp_all [Monotone]
    obtain ⟨i, hi⟩ := List.get_of_mem x_in_tail
    specialize @h_mono 0 (i.castSucc + 1) (by simp)
    simp at h_mono
    simp_all
  rw [List_Monotone_of_cons]
  simp only [List.length_cons, List.mem_cons, forall_eq_or_imp]
  constructor
  · exact h_mono
  · constructor
    · grind
    · intro y y_in_tail
      specialize s₁ y y_in_tail
      grind

end Algorithms

end Cslib
