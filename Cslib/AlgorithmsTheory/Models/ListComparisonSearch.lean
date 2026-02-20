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

end Algorithms

end Cslib
