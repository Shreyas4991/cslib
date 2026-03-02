/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Basic

/-! # RunsIn: Query Complexity Bounds via Monad Parametricity

`RunsIn f bound` (and its generalization `RunsInT`) assert that a monad-generic algorithm `f`
makes at most `bound x` queries on input `x`.

## The parametricity argument

An algorithm like
```
def insertionSort [Monad m] (cmp : α × α → m Bool) : List α → m (List α) := ...
```
is written generically over the monad `m`. To measure its query complexity, we specialize
`m` to `TickM` (or `TickT n` for algorithms with additional effects) and provide a
`cmp` implementation that calls `tick` once per invocation.

Because `insertionSort` is parametric in `m`, it **cannot observe the tick instrumentation**.
It must call `cmp` the same number of times regardless of which monad it runs in.
Therefore any upper bound proved via `TickM` is a true bound on query count in all monads.

`RunsInT` handles algorithms that use a base monad `n` for their own effects
(e.g., `StateM` for accumulation). The function must be generic over monads extending `n`
via `MonadLiftT`, and we specialize to `TickT n` which layers tick-counting on top of `n`.
The same parametricity argument applies: the algorithm cannot distinguish `TickT n` from
any other monad that lifts `n`.

## Computability caveat

The parametricity argument is only valid for **computable** algorithms. A `noncomputable`
definition could use `Classical.choice` to inspect `m` or the query function and subvert
the instrumentation. Since Lean's type theory does not enforce parametricity, the soundness
guarantee is informal: `RunsIn` and `RunsInT` theorems should only be proved about computable
algorithms. This framework is designed for proving upper bounds on query complexity, not lower
bounds.
-/

open Std.Do Cslib.Query

public section

namespace Cslib.Query

/-- `RunsInT n f bound` asserts that when the monad-generic function `f`
    is specialized to `TickT n`, with any query that calls `tick` at most once per invocation,
    the total number of ticks is bounded by `bound x`.

    The function `f` is generic over monads that extend `n` via `MonadLift`,
    ensuring it cannot observe the tick instrumentation. -/
@[expose] def RunsInT {n : Type → Type} {ps : PostShape} [Monad n] [WP n ps]
    (f : ∀ {m : Type → Type} [Monad m] [MonadLiftT n m], (α → m β) → γ → m δ)
    (bound : γ → Nat) : Prop :=
  ∀ (query : α → TickT n β), (∀ a, TickT.Costs (query a) 1) →
    ∀ x, TickT.Costs (f query x) (bound x)

/-- `RunsIn f bound` asserts that when the monad-generic function `f` is specialized to `TickM`,
    with any query that calls `tick` at most once per invocation,
    the total number of ticks is bounded by `bound x`. -/
@[expose] def RunsIn
    (f : ∀ {m : Type → Type} [Monad m], (α → m β) → γ → m δ)
    (bound : γ → Nat) : Prop :=
  ∀ (query : α → TickM β), (∀ a, TickT.Costs (query a) 1) →
    ∀ x, TickT.Costs (f query x) (bound x)

end Cslib.Query

end -- public section
