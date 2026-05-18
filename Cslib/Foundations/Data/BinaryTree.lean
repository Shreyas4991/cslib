/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

module

public import Mathlib.Data.Tree.Basic
public import Mathlib.Data.Tree.Traversable
public import Mathlib.Control.Fold.Traversable
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Tree

In this file we extend the `Tree` data structure from mathlib with basic operations.
-/

@[expose] public section

namespace Cslib

namespace Tree

open Cslib


/-- Number of nodes on the search path for `q` in `t`. Zero on the empty
tree; on a node this counts the root plus (if `q ≠ k`) the search path
length in the appropriate subtree. -/
def search_path_len [LinearOrder α] (t : Tree α) (q : α) : ℕ :=
  match t with
  | .nil => 0
  | .node key l r =>
    if q < key then
      1 + search_path_len l q
    else if key < q then
      1 + search_path_len r q
    else
      1

/--
Remark:
This implementation is not really a "contain function",
because a binary tree could have q >/< key while being in
the left/right subtree of key respectively.
If `contains t q` is true, then `q` is in `t`; but
the converse need not necessarily hold true. The
converse is true for a binary search tree.
-/
def containsBST [LinearOrder α] (t : Tree α) (q : α) : Prop :=
  match t with
  | .nil => False
  | .node key l r =>
    if q < key then
      containsBST l q
    else if key < q then
      containsBST r q
    else
      True


/-! ### Rotations and Mirroring -/
section Transformations

def rotateRight : Tree α → Tree α
  | .node y (.node x a b) c => .node x a (.node y b c)
  | t => t

def rotateLeft : Tree α → Tree α
  | .node x a (.node y b c) => .node y (.node x a b) c
  | t => t

/-- Mirror a binary tree: swap every left and right subtree. -/
def mirror : Tree α → Tree α
  | .nil => .nil
  | .node k l r => .node k (mirror r) (mirror l)

@[simp] lemma mirror_empty : (.nil : Tree α).mirror = .nil := rfl

@[simp] lemma mirror_node (k : α) (l : Tree α) (r : Tree α) :
    (Tree.node k l r).mirror = .node k r.mirror l.mirror := rfl


@[simp] lemma mirror_mirror (t : Tree α) : t.mirror.mirror = t := by
  induction t <;> simp_all

@[simp] lemma size_mirror (t : Tree α) : t.mirror.numNodes = t.numNodes := by
  induction t <;> simp_all [Tree.numNodes]; omega

@[simp] lemma mirror_rotateRight (t : Tree α) :
    (rotateRight t).mirror = rotateLeft t.mirror := by
  cases t
  · rfl
  · rename_i _ l _
    cases l <;> rfl

@[simp] lemma mirror_rotateLeft (t : Tree α) :
    (rotateLeft t).mirror = rotateRight t.mirror := by
  cases t; · rfl
  rename_i _ _ r
  cases r <;> rfl

@[simp] theorem size_rotateRight (t : Tree α) :
    (rotateRight t).numNodes = t.numNodes := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight]; omega

@[simp] theorem size_rotateLeft (t : Tree α) :
    (rotateLeft t).numNodes = t.numNodes := by
  have h := size_rotateRight t.mirror
  simp only [← mirror_rotateLeft, size_mirror] at h; exact h

end Transformations


/-! ### Contains Characterizations -/
section ContainsLemmas

@[simp] lemma not_contains_empty [LinearOrder α] (q : α) :
    ¬ (Tree.nil : Tree α).containsBST q := nofun

@[simp] lemma contains_node_lt [LinearOrder α] {l : Tree α} {k q : α}
    {r : Tree α} (h : q < k) :
    (Tree.node k l r).containsBST q ↔ l.containsBST q := by
  simp [containsBST, h]

@[simp] lemma contains_node_gt [LinearOrder α] {l : Tree α} {k q : α}
    {r : Tree α} (h : k < q) :
    (Tree.node k l r).containsBST q ↔ r.containsBST q := by
  simp [containsBST, h, not_lt_of_gt h]

@[simp] lemma contains_node_not_eq_not_lt [LinearOrder α]
    {l : Tree α} {k q : α} {r : Tree α}
    (h1 : ¬ q = k) (h2 : ¬ q < k) :
    (Tree.node k l r).containsBST q ↔ r.containsBST q := by
  have hgt : k < q := lt_of_le_of_ne (Std.not_lt.mp h2) (Ne.symm (Ne.intro h1))
  simp [containsBST, hgt, not_lt_of_gt hgt]

end ContainsLemmas


/-! ### Tree Invariants and BST Properties -/
section Invariants


def contains (t : Tree β) (p : β) : Prop :=
  match t with
  | .nil => False
  | .node k l r => p = k ∨ Tree.contains l p ∨ Tree.contains r p

instance : Membership β (Tree β) where
  mem := Tree.contains

def IsBST [LinearOrder α] (t : Tree α) : Prop :=
  Traversable.foldl

end Invariants


/-! ### Accessor Lemmas for ForallTree -/
section ForallTreeAccessors

@[simp] lemma ForallTree.left_sub {p : α → Prop} {l : Tree α} {k : α} {r : Tree α}
    (h : ForallTree p (.node l k r)) : ForallTree p l := by
  cases h with | node _ _ _ hl _ _ => exact hl

@[simp] lemma ForallTree.root {p : α → Prop} {l : Tree α} {k : α} {r : Tree α}
    (h : ForallTree p (.node l k r)) : p k := by
  cases h with | node _ _ _ _ hk _ => exact hk

@[simp] lemma ForallTree.right_sub {p : α → Prop} {l : Tree α} {k : α} {r : Tree α}
    (h : ForallTree p (.node l k r)) : ForallTree p r := by
  cases h with | node _ _ _ _ _ hr => exact hr

end ForallTreeAccessors


/-! ### Accessor Lemmas for IsBST -/
section IsBSTAccessors

@[simp] lemma IsBST.forallTree_left [LinearOrder α] {l : Tree α} {k : α} {r : Tree α}
    (h : IsBST (.node l k r)) : ForallTree (· < k) l := by
  cases h with | node _ _ _ hl _ _ _ => exact hl

@[simp] lemma IsBST.forallTree_right [LinearOrder α] {l : Tree α} {k : α} {r : Tree α}
    (h : IsBST (.node l k r)) : ForallTree (k < ·) r := by
  cases h with | node _ _ _ _ hr _ _ => exact hr

@[simp] lemma IsBST.left_bst [LinearOrder α] {l : Tree α} {k : α} {r : Tree α}
    (h : IsBST (.node l k r)) : IsBST l := by
  cases h with | node _ _ _ _ _ hl _ => exact hl

@[simp] lemma IsBST.right_bst [LinearOrder α] {l : Tree α} {k : α} {r : Tree α}
    (h : IsBST (.node l k r)) : IsBST r := by
  cases h with | node _ _ _ _ _ _ hr => exact hr

end IsBSTAccessors


end Tree

end Cslib
