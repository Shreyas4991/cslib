/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import Cslib.Init
public import Std.Do.Triple.Basic
import Std.Tactic.Do

/-! # Query Complexity Framework

This file provides infrastructure for proving upper bounds on the number of *queries*
(comparisons, oracle calls, etc.) that an algorithm makes.

## Approach

We define a monad transformer `TickT m` that wraps `StateT` with an internal tick counter.
Each call to `tick` increments this counter by 1. The predicate `Costs prog k` asserts that
`prog` increments the counter by at most `k`, expressed as a Hoare triple:
for any initial count `c`, if `prog` starts with count `≤ c`, it finishes with count `≤ c + k`.

The `Costs` combinators (`pure`, `bind`, `bind_spec`, `ite`, `map`, `le`, etc.) form
a small algebra for composing cost bounds, mirroring the structure of monadic programs.

## Why this works

The key to soundness is that algorithms are written as **monad-generic** functions:
```
def myAlgorithm [Monad m] (query : α → m β) (input : γ) : m δ := ...
```
Because `myAlgorithm` is polymorphic in `m`, it cannot inspect or manipulate the tick counter
directly — it can only interact with it through `query`. When we specialize `m` to `TickT`
and wrap `query` with a call to `tick`, every query invocation is faithfully counted.
The monad abstraction acts as an information barrier: the algorithm cannot distinguish
the instrumented monad from any other, so it cannot game the counter.

See `Cslib.Algorithms.Lean.Query.RunsIn` for the `RunsIn` and `RunsInT` predicates that
package this specialization step, and for a discussion of the computability caveat.
-/

open Std.Do

set_option mvcgen.warning false

public section

namespace Cslib.Query

structure TickT.State where
  count : Nat

/-- A monad transformer that adds tick-counting to any monad `m`. -/
@[expose] def TickT (m : Type → Type) (α : Type) := StateT TickT.State m α

/-- The tick-counting monad, specializing `TickT` to `Id`. -/
@[expose] def TickM (α : Type) := TickT Id α

namespace TickT

/-- Wrap a `StateT TickT.State m` computation as a `TickT m` computation. -/
@[expose, inline] def mk (x : StateT State m α) : TickT m α := x

/-- Unwrap a `TickT m` computation to `StateT TickT.State m`. -/
@[expose, inline] def unfold (x : TickT m α) : StateT State m α := x

@[simp] theorem unfold_mk (x : StateT State m α) : (mk x).unfold = x := rfl
@[simp] theorem mk_unfold (x : TickT m α) : mk x.unfold = x := rfl

@[ext] theorem ext {x y : TickT m α} (h : x.unfold = y.unfold) : x = y := h

instance [Monad m] : Monad (TickT m) where
  pure a := mk (pure a)
  bind x f := mk (x.unfold >>= fun a => (f a).unfold)

instance [Monad m] [LawfulMonad m] : LawfulMonad (TickT m) :=
  inferInstanceAs (LawfulMonad (StateT State m))
instance [WP m ps] : Std.Do.WP (TickT m) (.arg State ps) :=
  inferInstanceAs (Std.Do.WP (StateT State m) _)

instance [Monad m] [WPMonad m ps] : WPMonad (TickT m) (.arg State ps) :=
  inferInstanceAs (WPMonad (StateT State m) _)

instance [Monad m] : MonadLift m (TickT m) where
  monadLift x := mk (StateT.lift x)

/-- Run a `TickT` computation, starting with tick count 0,
    returning the result and the final tick count. -/
def run [Monad m] (x : TickT m α) : m (α × Nat) := do
  let (a, s) ← x.unfold.run ⟨0⟩
  pure (a, s.count)

/-- Run a `TickT` computation, starting with tick count 0, discarding the tick count. -/
def run' [Monad m] (x : TickT m α) : m α := Prod.fst <$> x.unfold.run ⟨0⟩

/-- Increment the tick counter by 1. -/
@[expose] def tick [Monad m] : TickT m Unit :=
  mk (modify fun s => ⟨s.count + 1⟩)

@[simp] theorem tick_unfold [Monad m] :
    (tick : TickT m Unit).unfold = modify fun s => ⟨s.count + 1⟩ := rfl

/-- Instrument a pure function as a tick-counted query.
    `counted f a` increments the tick counter by 1 and returns `f a`. -/
@[expose] def counted [Monad m] (f : α → β) (a : α) : TickT m β := do tick; pure (f a)

/-- Instrument a monadic function as a tick-counted query.
    `countedM f a` increments the tick counter by 1, then runs `f a` in the base monad. -/
@[expose] def countedM [Monad m] (f : α → m β) (a : α) : TickT m β := do
  tick; MonadLift.monadLift (f a)

/-- Assertion: the tick count is at most `k`. -/
@[expose] def checkBound {n : Type → Type} {ps : PostShape} [WP n ps] (k : Nat) :
    Assertion (.arg State ps) :=
  fun s => ⌜s.count ≤ k⌝

/-- `Costs prog k` asserts that `prog` uses at most `k` ticks. -/
@[expose] def Costs {n : Type → Type} {ps : PostShape} [Monad n] [WP n ps]
    (prog : TickT n α) (k : Nat) : Prop :=
  ∀ c, ⦃checkBound (n := n) c⦄ prog ⦃⇓ _ => checkBound (n := n) (c + k)⦄

/-- Spec for `tick` with schematic postcondition.
    To satisfy any postcondition `Q` after `tick`,
    it suffices to have `Q` hold with count incremented by 1. -/
@[spec]
theorem tick_spec [Monad n] [WPMonad n ps] {Q : PostCond Unit (.arg State ps)} :
    ⦃fun s => Q.1 () ⟨s.count + 1⟩⦄ (tick : TickT n Unit) ⦃Q⦄ := by
  simp only [Triple.iff]
  unfold tick
  show _ ⊢ₛ (PredTrans.pushArg fun s => wp (pure ((), { count := s.count + 1 }) : n _)).apply Q
  simp only [PredTrans.apply_pushArg, WP.pure]; exact .rfl

/-- `tick` costs 1. -/
public theorem tick_costs [Monad n] [WPMonad n ps] : Costs (tick : TickT n Unit) 1 := by
  intro c
  mvcgen
  simp_all [checkBound]

/-- WP of `MonadLift.monadLift` through `TickT`: passes through the tick state unchanged. -/
@[simp, spec]
theorem wp_monadLift [Monad m] [WPMonad m ps] (x : m α)
    (Q : PostCond α (.arg State ps)) :
    wp⟦(MonadLift.monadLift x : TickT m α)⟧ Q = fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2) :=
  Std.Do.WP.monadLift_StateT x Q

/-- `pure` costs 0. -/
public theorem Costs.pure [Monad n] [WPMonad n ps] (a : α) :
    Costs (Pure.pure a : TickT n α) 0 := by
  intro c
  exact Triple.pure a .rfl

/-- Sequential composition: costs add. -/
public theorem Costs.bind [Monad n] [WPMonad n ps]
    {x : TickT n α} {f : α → TickT n β}
    (hx : Costs x k₁) (hf : ∀ a, Costs (f a) k₂) :
    Costs (x >>= f) (k₁ + k₂) := by
  intro c
  apply Triple.bind _ _ (hx c) (fun a => ?_)
  have := hf a (c + k₁)
  rwa [Nat.add_assoc] at this

private theorem ExceptConds.false_and_self (ps : PostShape) :
    (ExceptConds.false (ps := ps) ∧ₑ ExceptConds.false).entails ExceptConds.false := by
  induction ps with
  | pure => exact ⟨⟩ | arg _ _ ih => exact ih
  | except _ _ ih => exact ⟨fun _ => SPred.and_elim_l, ih⟩

/-- Sequential composition with specification: when the continuation's cost
    depends on a predicate established by the first computation. -/
public theorem Costs.bind_spec [Monad n] [WPMonad n ps]
    {x : TickT n α} {f : α → TickT n β} {P : α → Prop}
    (hx_cost : Costs x k₁) (hx_spec : ⦃⌜True⌝⦄ x ⦃⇓ a => ⌜P a⌝⦄)
    (hf : ∀ a, P a → Costs (f a) k₂) :
    Costs (x >>= f) (k₁ + k₂) := by
  intro c
  have hcombined := Triple.and _ (hx_cost c) hx_spec
  apply Triple.bind _ _
  · apply SPred.entails.trans
      (SPred.entails.trans (SPred.and_intro .rfl (SPred.pure_intro trivial)) hcombined)
    apply (wp x).mono
    exact ⟨fun _ => .rfl, ExceptConds.false_and_self ps⟩
  · intro a
    simp only [Triple]
    apply SPred.pure_elim_r
    intro ha
    have := hf a ha (c + k₁)
    rwa [Nat.add_assoc] at this

/-- Branching: cost of either branch. -/
public theorem Costs.ite [Monad n] [WPMonad n ps]
    {t e : TickT n α} (b : Bool) (ht : Costs t k) (he : Costs e k) :
    Costs (if b then t else e) k := by
  intro c; cases b
  · exact he c
  · exact ht c

/-- Functorial map preserves cost (postcondition is result-independent). -/
public theorem Costs.map [Monad n] [WPMonad n ps]
    {x : TickT n α} {f : α → β} (h : Costs x k) :
    Costs (f <$> x) k := by
  intro c; simp only [Triple, WP.map]; exact h c

/-- Lifting from the base monad costs nothing, provided the computation doesn't throw. -/
public theorem Costs.monadLift [Monad n] [WPMonad n ps] (a : n α)
    (ha : ∀ (P : Prop), ⦃⌜P⌝⦄ a ⦃⇓ _ => ⌜P⌝⦄) :
    Costs (MonadLift.monadLift a : TickT n α) 0 := by
  intro c
  apply SPred.entails.trans _ (Spec.monadLift_StateT a _)
  simp only [checkBound, Nat.add_zero]
  intro s
  exact ha (s.count ≤ c)

/-- Weakening: increase the bound. -/
public theorem Costs.le [Monad n] [WPMonad n ps]
    {prog : TickT n α} (h : Costs prog k) (hle : k ≤ k') :
    Costs prog k' := by
  intro c
  exact Triple.entails_wp_of_post (h c) (by
    simp only [PostCond.entails_noThrow]
    intro _
    intro s
    exact SPred.pure_mono (fun hs => Nat.le_trans hs (Nat.add_le_add_left hle c)))

/-- `pure` costs at most `k`, for any `k`. -/
public theorem Costs.pure_le [Monad n] [WPMonad n ps] (a : α) (k : Nat) :
    Costs (Pure.pure a : TickT n α) k :=
  Costs.le (Costs.pure a) (Nat.zero_le k)

/-- Branching with different costs: bounded by `max`. -/
public theorem Costs.ite_max [Monad n] [WPMonad n ps]
    {t e : TickT n α} (b : Bool) (ht : Costs t kt) (he : Costs e ke) :
    Costs (if b then t else e) (max kt ke) :=
  Costs.ite b (Costs.le ht (Nat.le_max_left kt ke)) (Costs.le he (Nat.le_max_right kt ke))

/-- `counted f a` costs 1. -/
public theorem counted_costs [Monad n] [WPMonad n ps] (f : α → β) (a : α) :
    Costs (counted (m := n) f a) 1 :=
  Costs.bind tick_costs (fun _ => Costs.pure (f a))

/-- `countedM f a` costs 1, provided the underlying computation preserves propositions. -/
public theorem countedM_costs [Monad n] [WPMonad n ps] (f : α → n β) (a : α)
    (hf : ∀ (P : Prop), ⦃⌜P⌝⦄ f a ⦃⇓ _ => ⌜P⌝⦄) :
    Costs (countedM (m := n) f a) 1 :=
  Costs.bind tick_costs (fun _ => Costs.monadLift (f a) hf)

end TickT

instance : Monad TickM := inferInstanceAs (Monad (TickT Id))
instance : LawfulMonad TickM := inferInstanceAs (LawfulMonad (TickT Id))
instance : Std.Do.WP TickM (.arg TickT.State .pure) :=
  inferInstanceAs (Std.Do.WP (TickT Id) _)
instance : WPMonad TickM (.arg TickT.State .pure) :=
  inferInstanceAs (WPMonad (TickT Id) _)

end Cslib.Query

end -- public section
