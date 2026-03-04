/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib

@[expose] public section


namespace Cslib

namespace Algorithms


open Prog MeasureTheory

structure ValFunction (Cake : Type) [MeasurableSpace Cake] where
  val : FiniteMeasure Cake

structure Alloc (α Cake : Type) [MeasurableSpace Cake] where
  alloc : a → Set Cake
  allocMeasurable : ∀ a : α, Measurable (alloc a)

structure AllocInstance (α Cake : Type) [MeasurableSpace Cake] where
  allocInst : Alloc α Cake
  valFuns : α → ValFunction Cake

abbrev Alloc.IsComplete {α Cake : Type} [MeasurableSpace Cake]
  (a : Alloc α Cake) := ∀ i : Cake, ∃ agent : α, i ∈ a.alloc agent

abbrev I (x y : ℝ) : Type := {a : ℝ // x ≤ a ∧ a ≤ y}

abbrev UnitI := I 0 1

abbrev EFAgents [MeasurableSpace Cake] (a : AllocInstance α Cake) (x y : α) : Prop :=
  (a.valFuns x).val (a.allocInst.alloc x) ≥ (a.valFuns x).val (a.allocInst.alloc y)

abbrev EF [MeasurableSpace Cake] (a : AllocInstance α Cake) :=
  ∀ x y : α, EFAgents a x y

inductive RobertsonWebbQuery (α : Type) : Type → Type where
  /-- evaluates agent `i`'s value for interval `[x,y]` -/
  | eval (i : α) (x y : UnitI) : RobertsonWebbQuery α ℝ
  /-- given a starting point `x` and value `val`
      returns a `y` such that `eval i x y = val` or `y = 1` -/
  | mark (i : α) (x : UnitI) (val : ℝ) : RobertsonWebbQuery α UnitI



open Classical in
/-- This model necessarily uses classical. Watch out for hacks -/
@[simps]
noncomputable def RobertsonWebbModel {α : Type}
    (allocInst : AllocInstance α UnitI)
    : Model (RobertsonWebbQuery α) ℕ where
  evalQuery
    | .eval i x y => (allocInst.valFuns i).val (Set.Icc x y)
    | .mark i x val =>
        let proposition := ∃ y : UnitI, (allocInst.valFuns i).val (Set.Icc x y) = val
        if h : proposition then
          Exists.choose h
        else
          ⟨(1 : ℝ), by grind⟩
  cost _ := 1

lemma RobertsonWebbModel.mark_leq {a : AllocInstance α UnitI}
    (i : α) (x : UnitI) (val : ℝ)  :
      RobertsonWebbModel.evalQuery(.eval i x (RobertsonWebbModel.evalQuery (.mark i x val))) ≤ val := by sorry
end Algorithms

end Cslib
