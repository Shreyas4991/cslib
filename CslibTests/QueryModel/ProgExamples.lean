/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel

@[expose] public section

namespace Cslib

namespace Algorithms

namespace Prog

section ProgExamples

inductive Arith (α : Type) : Type → Type where
  | add (x y : α) : Arith α α
  | mul (x y : α) : Arith α α
  | neg (x : α) : Arith α α
  | zero : Arith α α
  | one : Arith α α

def RatArithQuery_NatCost : Model (Arith ℚ) ℕ where
  evalQuery
    | .add x y => x + y
    | .mul x y => x * y
    | .neg x =>  -x
    | .zero => (0 : ℚ)
    | .one => (1 : ℚ)
  cost _ := 1

open Arith in
def ex1 : Prog (Arith ℚ) ℚ := do
  let mut x : ℚ ← @zero ℚ
  let mut y ← @one ℚ
  let z ← (add (x + y + y) y)
  let w ← @neg ℚ (←(add z y))
  add w z

/--
The array version of the sort operations
-/
inductive VecSortOps (α : Type) : Type → Type  where
  | swap : (a : Vector α n) → (i j : Fin n) → VecSortOps α (Vector α n)
  | cmp :  (a : Vector α n) → (i j : Fin n) → VecSortOps α Bool
  | write : (a : Vector α n) → (i : Fin n) → (x : α) → VecSortOps α (Vector α n)
  | read : (a : Vector α n) → (i : Fin n) → VecSortOps α α
  | push : (a : Vector α n) → (elem : α) → VecSortOps α (Vector α (n + 1))

def VecSort_WorstCase [DecidableEq α] : Model (VecSortOps α) ℕ where
  evalQuery
    | .write v i x => v.set i x
    | .cmp l i j =>  l[i] == l[j]
    | .read l i => l[i]
    | .swap l i j => l.swap i j
    | .push a elem => a.push elem
  cost
    | .write l i x => 1
    | .read l i =>  1
    | .cmp l i j => 1
    | .swap l i j => 1
    | .push a elem => 2 -- amortized over array insertion and resizing by doubling

def VecSort_CmpSwap [DecidableEq α] : Model (VecSortOps α) ℕ where
  evalQuery
    | .write v i x => v.set i x
    | .cmp l i j =>  l[i] == l[j]
    | .read l i => l[i]
    | .swap l i j => l.swap i j
    | .push a elem => a.push elem
  cost
    | .cmp l i j => 1
    | .swap l i j => 1
    | _ => 0

open VecSortOps in
def simpleExample (v : Vector ℤ n) (i k : Fin n)
  : Prog (VecSortOps ℤ) (Vector ℤ (n + 1)) :=  do
  let b : Vector ℤ n ← write v i 10
  let mut c : Vector ℤ n ← swap b i k
  let elem ← read c i
  push c elem

inductive VecSearch (α : Type) : Type → Type  where
  | compare (a : Vector α n) (i : ℕ) (val : α) : VecSearch α Bool

def VecSearch_Nat [DecidableEq α] : Model (VecSearch α) ℕ where
  evalQuery
    | .compare l i x =>  l[i]? == some x
  cost
    | .compare _ _ _ => 1

open VecSearch in
def linearSearchAux (v : Vector α n)
  (x : α) (acc : Bool) (index : ℕ) : Prog (VecSearch α) Bool := do
    if h : index ≥ n then
      return acc
    else
      let cmp_res : Bool ← compare v index x
      if cmp_res then
        return true
      else
        linearSearchAux v x false (index + 1)

open VecSearch in
def linearSearch (v : Vector α n) (x : α) : Prog (VecSearch α) Bool:=
  linearSearchAux v x false 0

end ProgExamples

end Prog

end Algorithms

end Cslib
