/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.RunsIn
import Std.Tactic.Do

/-! # Monadic Map-Sum Demo

A minimal demonstration of `RunsInT` with a non-trivial base monad.

`mapSum f xs` applies the monadic function `f` to each element of `xs`
and accumulates the results into a `StateM Int` counter.

Since `f` is called exactly once per element, `mapSum` runs in `xs.length` queries.
This is expressed via `RunsInT (n := StateM Int)`, which instruments the query with tick-counting
while preserving the `StateM Int` layer used for accumulation.
-/

open Std.Do Cslib.Query

set_option mvcgen.warning false

public section

namespace Cslib.Query

/-- Apply a monadic function to each element of a list and accumulate the results in `StateM Int`.
    The function `f` is the query whose invocations we measure. -/
@[expose] def mapSum [Monad m] [MonadLiftT (StateM Int) m]
    (f : Int → m Int) : List Int → m Unit
  | [] => pure ()
  | x :: xs => do
    let y ← f x
    (modify (· + y) : StateM Int Unit)
    mapSum f xs

/-- `mapSum` calls the function exactly once per element. -/
public theorem mapSum_runsInT :
    RunsInT (n := StateM Int) mapSum (fun xs => xs.length) := by
  intro query hquery xs
  induction xs with
  | nil => exact TickT.Costs.pure ()
  | cons x xs ih =>
    simp only [List.length]; rw [Nat.add_comm]
    have ih : TickT.Costs (mapSum query xs) xs.length := ih
    exact TickT.Costs.bind (hquery x) (fun y => by
      have := TickT.Costs.bind
        (TickT.Costs.monadLift (modify (· + y) : StateM Int Unit) (fun P => by mvcgen))
        (fun _ => ih)
      rwa [Nat.zero_add] at this)

/-- `mapSum` with a pure function accumulates `(xs.map f).sum`. -/
-- This is not the right theorem. I want here `f : Int → m Int`,
-- with a condition that it doesn't change the value of `getThe Int`
-- (which should be possible to express via `[MonadLiftT (StateM Int) m]`).
-- But I can't work out how to express this!
-- I want something that asserts that even when we instrument `f` to count ticks,
-- we still get the right answer.
public theorem mapSum_spec (f : Int → Int) (xs : List Int) :
    ∀ c, ⦃fun n => ⌜n = c⌝⦄
      mapSum (m := StateM Int) (fun a => pure (f a)) xs
    ⦃⇓ _ => fun n => ⌜n = c + (xs.map f).sum⌝⦄ := by
  induction xs with
  | nil =>
    intro c; simp only [mapSum]; mvcgen; simp_all
  | cons x xs ih =>
    intro c; dsimp only [mapSum]; mvcgen [ih]
    simp only [List.map_cons, List.sum_cons]; grind

/-- `mapSum` with a tick-instrumented pure function still accumulates `(xs.map f).sum`. -/
public theorem mapSum_spec_tick (f : Int → Int) (xs : List Int) :
    ∀ c, ⦃fun _ => fun n => ⌜n = c⌝⦄
      mapSum (m := TickT (StateM Int)) (TickT.counted f) xs
    ⦃⇓ _ => fun _ => fun n => ⌜n = c + (xs.map f).sum⌝⦄ := by
  induction xs with
  | nil =>
    intro c; simp only [mapSum]; mvcgen; simp_all
  | cons x xs ih =>
    intro c; dsimp only [mapSum, TickT.counted]; mvcgen [ih]
    simp only [TickT.wp_monadLift, Std.Do.WP.modifyGet_StateT]
    rename_i ts n hn
    subst hn
    simp only [List.map_cons, List.sum_cons, ← Int.add_assoc]
    exact ih (n + f x) _ _ rfl

end Cslib.Query

end -- public section
