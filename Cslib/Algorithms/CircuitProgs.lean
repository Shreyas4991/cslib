/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Algorithms.QueryModel

@[expose] public section

namespace Cslib

namespace Algorithms

namespace Prog
inductive Formula (α : Type u) : Type u → Type u where
  | const (x : α) : Formula α α
  | add (c₁ c₂ : Formula α α) : Formula α α
  | mul (c₁ c₂ : Formula α α) : Formula α α
  | neg (c : Formula α α) : Formula α α
deriving Repr

-- def getID (c : Formula α β) : ℕ :=
--   match c with
--   | .const id _ => id
--   | .add id _ _ => id
--   | .mul id _ _ => id
--   | .neg id _ => id


structure CircuitCosts where
  depth : ℕ
  size : ℕ

instance : PureCosts CircuitCosts where
  pureCost := ⟨0,0⟩

instance : Zero CircuitCosts where
  zero := ⟨0,0⟩

instance : Add CircuitCosts where
  add x y := ⟨x.1 + y.1, x.2 + y.2⟩

def circEval (α : Type u) [Add α] [Mul α] [Neg α] (c : Formula α ι) : ι :=
  match c with
  | .const x => x
  | .add c₁ c₂ => circEval α c₁ + circEval α c₂
  | .mul c₁ c₂ => circEval α c₁ * circEval α c₂
  | .neg c => - circEval α c


def depthOf (q : Formula α β) :=
  match q with
  | .const c => 0
  | .add c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .mul c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .neg c => 1 + depthOf c

-- def uniqueIDs (q : Formula α β) (countedIDs : List ℕ) : List ℕ :=
--   match q with
--   | .const id _ =>
--       countedIDs.insert id
--   | .add id x y =>
--       let s₁ := uniqueIDs x countedIDs
--       let s₂ := uniqueIDs y s₁
--       s₂.insert id
--   | .mul id x y =>
--       let s₁ := uniqueIDs x countedIDs
--       let s₂ := uniqueIDs y s₁
--       s₂.insert id
--   | .neg id x =>
--       let s := uniqueIDs x countedIDs
--       s.insert id

def sizeOf (q : Formula α β) :=
  match q with
  | .const c => 0
  | .add c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .mul c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .neg c => 1 + depthOf c

def circModel (α : Type u) [Add α] [Mul α] [Neg α] : Model (Formula α) CircuitCosts where
  evalQuery q := circEval α q
  cost q := ⟨depthOf q, sizeOf q⟩


open Formula in
def exFormula1 : Prog (Formula Bool) Bool := do
  let x := const true
  let y := const true
  let z := add x y
  let w := mul x y
  add z w


#eval exFormula1.eval (circModel Bool)
#eval exFormula1.time (circModel Bool)

open Formula in
def exFormula2 : Prog (Formula ℚ) ℚ := do
  let x := const (1 : ℚ)
  let y := const (2 : ℚ)
  let z := add x y
  mul z z


#eval exFormula2.eval (circModel ℚ)
#eval exFormula2.time (circModel ℚ)

open Formula in
def exFormula3 : Prog (Formula ℚ) ℚ := do
  let x := const (1 : ℚ)
  let y := const (2 : ℚ)
  let z := add x y
  mul z z

#eval exFormula2.eval (circModel ℚ)
#eval exFormula2.time (circModel ℚ)

open Formula in
def exFormula4 (x y : Formula ℚ ℚ) : Prog (Formula ℚ) ℚ := do
  let z := add x y
  let w := mul x y
  mul z w

#eval (exFormula4 (.const (1 : ℚ)) (.const (21 : ℚ))).eval (circModel ℚ)
#eval (exFormula4 (.const (1 : ℚ)) (.const (21 : ℚ))).time (circModel ℚ)


open Formula in
def CircAnd (n : ℕ) (x : Fin n → Formula Bool Bool) : Formula Bool Bool :=
  match n with
  | 0 => const true
  | m + 1 =>
      let x_head := x 0
      let x_cons := CircAnd m (Fin.tail x)
      mul x_head x_cons

def execCircAnd (x : Fin n → Formula Bool Bool) : Prog (Formula Bool) Bool := do
  CircAnd n x

#eval (execCircAnd ![.const true, .const true, .const true]).eval (circModel Bool)
#eval (execCircAnd ![.const true, .const true, .const true]).time (circModel Bool)


section Circuit

-- Another query type that reduces to Circuit queries. automates identification of nodes

inductive Circuit (α : Type u) : Type u → Type u where
  | const (x : α) : Circuit α (Formula α α)
  | add (c₁ c₂ : Formula α α) : Circuit α (Formula α α)
  | mul (c₁ c₂ : Formula α α) : Circuit α (Formula α α)
  | neg (c : Formula α α) : Circuit α (Formula α α)



def circQueryEvalAux (α : Type u)
  (c : Circuit α ι) : ι :=
  match c with
  | .const x => Formula.const x
  | .add c₁ c₂ => Formula.add c₁ c₂
  | .mul c₁ c₂ => Formula.mul c₁ c₂
  | .neg c => Formula.neg c

def sizeCircQuery (c : Circuit α (Formula α β)) : CircuitCosts :=
  let c' := circQueryEvalAux α c
  ⟨depthOf c', sizeOf c'⟩

def circQueryModel (α : Type u) [Add α] [Mul α] [Neg α] : Model (Circuit α) CircuitCosts where
  evalQuery q := circQueryEvalAux α q
  cost q := match q with
    | .const x => sizeCircQuery (.const x)
    | .add c₁ c₂ => sizeCircQuery (.add c₁ c₂)
    | .mul c₁ c₂ => sizeCircQuery (.mul c₁ c₂)
    | .neg c => sizeCircQuery (.neg c)

open Circuit in
def ex5 : Prog (Circuit ℚ) (Formula ℚ ℚ) := do
  let x ← const (1 : ℚ)
  let y : Formula ℚ ℚ ← const (2 : ℚ)
  let z : Formula ℚ ℚ ← add x y
  let w : Formula ℚ ℚ ← mul z z
  return w

#eval ex5.eval (circQueryModel ℚ)
#eval ex5.time (circQueryModel ℚ)

open Circuit in
def ex6 (a b : Circuit ℚ (Formula ℚ ℚ)) : Prog (Circuit ℚ) (Formula ℚ ℚ) := do
  let x : Formula ℚ ℚ ← a
  let y : Formula ℚ ℚ ← b
  let z : Formula ℚ ℚ ← add x y
  mul z z

def ex6_circuit := (ex6 (.const 0) (.const 1)).eval (circQueryModel ℚ)
#eval sizeOf ex6_circuit
#eval (ex6 (.const 0) (.const 1)).time (circQueryModel ℚ)

end Circuit

end Prog

end Algorithms

end Cslib
