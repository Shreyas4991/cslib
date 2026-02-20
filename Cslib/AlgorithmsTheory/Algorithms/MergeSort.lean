/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.AlgorithmsTheory.QueryModel

@[expose] public section

namespace Cslib.Algorithms

inductive SortOps (α : Type) : Type → Type  where
  | cmpLT (x : α) (y : α): SortOps α Bool
  | insertHead (l : List α) (x : α) : SortOps α (List α)

open SortOps


def sortModel (α : Type) [LinearOrder α] : Model (SortOps α) ℕ where
  evalQuery q :=
    match q with
    | .cmpLT x y =>
            if x < y then
              true
            else
              false
    | .insertHead l x => x :: l
  cost q :=
    match q with
    | .cmpLT _ _ => 1
    | .insertHead _ _ => 1

@[simp]
lemma sortModel_eval_1 [LinearOrder α] (y x : α) :
  y ≤ x → (sortModel α).evalQuery (cmpLT x y) = false := by
  intro h
  simp only [sortModel, Bool.if_false_right, Bool.and_true, decide_eq_false_iff_not, not_lt]
  exact h
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
@[simp, grind]
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
      (FreeM.bind (merge xs (y :: ys)) (fun rest => FreeM.pure (x :: rest))) (sortModel α))
      = (merge xs (y :: ys)).time (sortModel α) := by
  have h := Prog.time.bind (sortModel α) (merge xs (y :: ys)) (fun rest => FreeM.pure (x :: rest))
  have h' : Prog.time (FreeM.bind (merge xs (y :: ys)) (fun rest => FreeM.pure (x :: rest)))
              (sortModel α) + 1 = (merge xs (y :: ys)).time (sortModel α) + 1 := by
      simpa using h
  exact Nat.add_right_cancel h'

lemma merge_bind_pure_insert_y [LinearOrder α] (x y : α) (xs ys : List α) :
  (Prog.time
    (FreeM.bind (merge (x :: xs) ys) (fun rest => FreeM.pure (y :: rest))) (sortModel α))
    = (merge (x :: xs) ys).time (sortModel α) := by
  have h := Prog.time.bind (sortModel α) (merge (x :: xs) ys) (fun rest => FreeM.pure (y :: rest))
  have h' : Prog.time (FreeM.bind (merge (x :: xs) ys) (fun rest => FreeM.pure (y :: rest)))
              (sortModel α) + 1 = (merge (x :: xs) ys).time (sortModel α) + 1 := by
    simpa using h
  exact Nat.add_right_cancel h'

lemma merge_timeComplexity [LinearOrder α] (x y : List α) :
  (merge x y).time (sortModel α) ≤  x.length + y.length + 1:= by
  fun_induction merge
  · simp
  · simp
  · expose_names
    simp only [bind, FreeM.lift_def, pure, FreeM.liftBind_bind, FreeM.pure_bind, sortModel,
      Bool.if_false_right, Bool.and_true, Prog.time.eq_2, decide_eq_true_eq, List.length_cons]
    split_ifs with hxy
    · have hbind := merge_bind_pure_insert_x x y xs' ys'
      simp only [sortModel, Bool.if_false_right, Bool.and_true] at hbind
      rw [hbind]
      have hih :
          (merge xs' (y :: ys')).time (sortModel α) ≤
            xs'.length + (y :: ys').length + 1 := by
        simpa using ih2
      have h := Nat.add_le_add_left hih 1
      simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    · have hbind := merge_bind_pure_insert_y x y xs' ys'
      simp only [sortModel, Bool.if_false_right, Bool.and_true] at hbind
      rw [hbind]
      have hih :
          (merge (x :: xs') ys').time (sortModel α) ≤
            (x :: xs').length + ys'.length + 1 := by
        simpa using ih1
      have h := Nat.add_le_add_left hih 1
      simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h


lemma merge_is_mergeNaive [LinearOrder α] (x y : List α) :
  (merge x y).eval (sortModel α) = mergeNaive x y := by
  fun_induction mergeNaive
  · simp [merge]
  · simp [merge]
  · expose_names
    simp_all [Prog.eval,  merge, rest, sortModel]
  · expose_names
    simp_all [Prog.eval, merge, rest]

lemma merge_length [LinearOrder α] (x y : List α) :
  ((merge x y).eval (sortModel α)).length = x.length + y.length := by
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
  (mergeSort xs).eval (sortModel α) = mergeSortNaive xs := by
  classical
  let P : Nat → Prop :=
    fun n => ∀ xs, xs.length = n → (mergeSort xs).eval (sortModel α) = mergeSortNaive xs
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
          (mergeSort left).eval (sortModel α) = mergeSortNaive left :=
        (ih left.length (by simpa [hlen] using hleft_lt_len)) left rfl
      have hright :
          (mergeSort right).eval (sortModel α) = mergeSortNaive right :=
        (ih right.length (by simpa [hlen] using hright_lt_len)) right rfl
      have hleft' :
          FreeM.liftM (m := Id) (fun {ι} q => (sortModel α).evalQuery q)
              (mergeSort (xs.take (xs.length / 2))) =
            mergeSortNaive (xs.take (xs.length / 2)) := by
        simpa [left, half, Prog.eval, Id.run] using hleft
      have hright' :
          FreeM.liftM (m := Id) (fun {ι} q => (sortModel α).evalQuery q)
              (mergeSort (xs.drop (xs.length / 2))) =
            mergeSortNaive (xs.drop (xs.length / 2)) := by
        simpa [right, half, Prog.eval, Id.run] using hright
      have hmerge (a b : List α) :
          FreeM.liftM (m := Id) (fun {ι} q => (sortModel α).evalQuery q) (merge a b) =
            mergeNaive a b := by
        simpa [Prog.eval, Id.run] using (merge_is_mergeNaive (α := α) a b)
      nth_rewrite 1 [mergeSort]
      nth_rewrite 1 [mergeSortNaive]
      simp only [hlt, if_false, Prog.eval, Id.run, bind, pure, FreeM.liftM_bind]
      set a :=
        FreeM.liftM (m := Id) (fun {ι} q => (sortModel α).evalQuery q)
          (mergeSort (List.take (xs.length / 2) xs))
      set b :=
        FreeM.liftM (m := Id) (fun {ι} q => (sortModel α).evalQuery q)
          (mergeSort (List.drop (xs.length / 2) xs))
      calc
        FreeM.liftM (m := Id) (fun {ι} q => (sortModel α).evalQuery q)
            (merge
              (FreeM.liftM (m := Id) (fun {ι} q => (sortModel α).evalQuery q)
                (mergeSort (List.take (xs.length / 2) xs)))
              (FreeM.liftM (m := Id) (fun {ι} q => (sortModel α).evalQuery q)
                (mergeSort (List.drop (xs.length / 2) xs)))) =
            FreeM.liftM (m := Id) (fun {ι} q => (sortModel α).evalQuery q) (merge a b) := by
          simp [a, b]
        _ = mergeNaive a b := hmerge a b
        _ = mergeNaive (mergeSortNaive (List.take (xs.length / 2) xs))
              (mergeSortNaive (List.drop (xs.length / 2) xs)) := by
          simp only [a, b, hleft', hright']
  exact hP xs rfl


lemma mergeSortNaive_length [LinearOrder α] (xs : List α) :
  (mergeSortNaive xs).length = xs.length := by
  by_cases h₂ : xs.length < 2
  · unfold mergeSortNaive
    simp [h₂]
  · unfold mergeSortNaive
    simp only [h₂, ↓reduceIte]
    induction h : xs.length using Nat.strong_induction_on generalizing xs with
    | h n ih =>
        rw [mergeNaive_length]
        have h₁ := ih ((List.take (n / 2) xs)).length (by simp [List.length_take]; grind)
        have h₂ := ih ((List.drop (n / 2) xs)).length (by simp [List.length_drop]; grind)
        specialize h₁ (List.take (n / 2) xs)
        specialize h₂ (List.drop (n / 2) xs)
        by_cases hdrop : (List.drop (n / 2) xs).length < 2
        <;> by_cases htake : (List.take (n / 2) xs).length < 2
        ·
          done
        · done
        · done
        · specialize h₁ htake rfl
          done

lemma mergeSort_length [LinearOrder α] (xs : List α) :
  ((mergeSort xs).eval (sortModel α)).length = xs.length := by
  rw [mergeSort_is_mergeSortNaive]
  apply mergeSortNaive_length


lemma mergeNaive_sorted_sorted [LinearOrder α] (xs ys : List α)
  (hxs_mono : Monotone xs.get) (hys_mono : Monotone ys.get) :
  Monotone (mergeNaive xs ys).get := by
  sorry

end Cslib.Algorithms
