import Mathlib.Tactic.Linarith
import Std.Tactic.Basic

import Splay.Assoc
import Splay.Tactics

inductive STree (α : Type u) where
  | leaf
  | node (left : STree α) (key : Nat) (value : α) (right : STree α)

-- TODO doc
@[simp]
def STree.splay (tree : STree α) (key : Nat) : STree α :=
  match tree with
  | leaf => leaf
  | node l k v r =>
    if key = k then tree
    else if key < k then
      match l with
      | leaf => tree -- not found
      | node ll lk lv lr =>
        if key = lk then node ll lk lv (node lr k v r) -- 1: zig
        else if key < lk then
          match ll.splay key with
          | leaf => node ll lk lv (node lr k v r) -- not found
          | node lll llk llv llr => -- 2: zig-zig
            node lll llk llv (node llr lk lv (node lr k v r))
        else -- key > lk
          match lr.splay key with
          | leaf => node ll lk lv (node lr k v r) -- not found
          | node lrl lrk lrv lrr => -- 3: zig-zag
            node (node ll lk lv lrl) lrk lrv (node lrr k v r)
    else -- key > k
      match r with
      | leaf => tree -- not found
      | node rl rk rv rr =>
        if key = rk then node (node l k v rl) rk rv rr -- 1: zag
        else if key < rk then
          match rl.splay key with
          | leaf => node (node l k v rl) rk rv rr -- not found
          | node rll rlk rlv rlr => -- 3: zag-zig
            node (node l k v rll) rlk rlv (node rlr rk rv rr)
        else -- key > rk
          match rr.splay key with
          | leaf => node (node l k v rl) rk rv rr -- not found
          | node rrl rrk rrv rrr => -- 2: zag-zag
            node (node (node l k v rl) rk rv rrl) rrk rrv rrr

-- TODO doc
@[simp]
def STree.bound' (tree : STree α) (key : Nat) : Bool :=
  match tree with
  | leaf => false
  | node l k _ r =>
    if key = k then true
    else if key < k then l.bound' key
    else r.bound' key

-- TODO doc
-- implementing this in terms of splay is possible but it makes it hard to prove
-- things about it
@[simp]
def STree.bound (tree : STree α) (key : Nat) : Bool :=
  match tree.splay key with
  | leaf => false
  | node _ k _ _ => key = k

-- TODO doc
-- lookup for normal BSTs
@[simp]
def STree.lookup_aux (tree : STree α) (key : Nat) : Option α :=
  match tree with
  | leaf => none
  | node l k v r =>
    if key = k then some v
    else if key < k then l.lookup_aux key
    else r.lookup_aux key

-- TODO doc
-- easier to prove things this way
@[simp]
def STree.lookup' (tree : STree α) (key : Nat) : Option α × STree α :=
  (tree.lookup_aux key, tree.splay key)

@[simp]
def STree.lookup? (tree : STree α) (key : Nat) : Option α × STree α :=
  match tree.splay key with
  | leaf => (none, leaf)
  | node l k v r =>
    if key = k then (some v, node l k v r) else
      (none, node l k v r)

-- TODO doc
-- insert for normal bst
@[simp]
def STree.ins (tree : STree α) (key : Nat) (val : α) : STree α :=
  match tree with
  | leaf => node leaf key val leaf
  | node l k v r =>
    if key = k then node l key val r
    else if key < k then node (l.ins key val) k v r
    else node l k v (r.ins key val)

@[simp]
def STree.insert (tree : STree α) (key : Nat) (val : α) : STree α :=
  splay (tree.ins key val) key

@[simp]
def STree.elements (tree : STree α) : Assoc α :=
  match tree with
  | leaf => []
  | node l k v r => l.elements ++ [(k, v)] ++ r.elements

namespace Tests
open STree
-- A < x < B < y < C < z < D
def A := node leaf 0 "A" leaf
def x := 1
def B := node leaf 2 "B" leaf
def y := 3
def C := node leaf 4 "C" leaf
def z := 5
def D := node leaf 6 "D" leaf

--    (1)           (2)
--     y             x
--    / \           / \
--   x   C   <->   A   y
--  / \               / \
-- A   B             B   C
def T1 := node (node A x "x" B) y "y" C
def T2 := node A x "x" (node B y "y" C)
theorem splay_zig : T1.splay x = T2 := by rfl
theorem splay_zag : T2.splay y = T1 := by rfl

--      (3)           (4)
--       z             x
--      / \           / \
--     y   D         A   y
--    / \      <->      / \    (A < x < B < y < C < z < D)
--   x   C             B   z
--  / \                   / \
-- A   B                 C   D
def T3 := node (node (node A x "x" B) y "y" C) z "z" D
def T4 := node A x "x" (node B y "y" (node C z "z" D))
theorem splay_zig_zig : T3.splay x = T4 := by rfl
theorem splay_zag_zag : T4.splay z = T3 := by rfl

--       (5)              (6)              (7)
--        z                y                x
--       / \              / \              / \
--      x   D            /   \            A   z   (A < x < B < y < C < z < D)
--     / \         ->   x     z    <-        / \
--    A   y            / \   / \            y   D
--       / \          A   B C   D          / \
--      B   C                             B   C
def T5 := node (node A x "x" (node B y "y" C)) z "z" D
def T6 := node (node A x "x" B) y "y" (node C z "z" D)
def T7 := node A x "x" (node (node B y "y" C) z "z" D)
  
theorem splay_zig_zag : splay T5 y = T6 := by rfl

theorem splay_zag_zig : splay T7 y = T6 := by rfl
end Tests

theorem STree.inductionOn
  {motive : STree α -> Sort u}
  (base : motive leaf)
  (ind_te : ∀ k v, motive (node leaf k v leaf))
  (ind_tl : ∀ k v ll lk lv lr,
    motive ll -> motive lr ->
    motive (node (node ll lk lv lr) k v leaf))
  (ind_tr : ∀ k v rl rk rv rr,
    motive rl -> motive rr ->
    motive (node leaf k v (node rl rk rv rr)))
  (ind : ∀ k v ll lk lv lr rl rk rv rr,
    motive ll -> motive lr ->
    motive rl -> motive rr ->
    motive (node (node ll lk lv lr) k v (node rl rk rv rr)))
  : ∀ t, motive t :=
  builder
where
  builder (t : STree α) :=
    match t with
    | leaf => base
    | node leaf k v leaf => ind_te k v
    | node (node ll lk lv lr) k v leaf =>
      ind_tl k v ll lk lv lr (builder ll) (builder lr)
    | node leaf k v (node rl rk rv rr) =>
      ind_tr k v rl rk rv rr (builder rl) (builder rr)
    | node (node ll lk lv lr) k v (node rl rk rv rr) =>
      ind k v ll lk lv lr rl rk rv rr (builder ll) (builder lr) (builder rl) (builder rr)

theorem splay_bound_equiv (tree : STree α) (key : Nat)
  : tree.bound key = tree.bound' key := by
  induction tree using STree.inductionOn with
  | base => rfl
  | ind_te k v =>
    simp
    by_cases (key = k) <;> simp [*]
  | ind_tl k v ll lk lv lr ihll ihlr =>
    simp
    by_cases' (key = k) h1
    by_cases' (key < k) h2
    by_cases' (key = lk) h3
    by_cases' (key < lk) h4
    rw [<-ihll]
    simp
    match STree.splay ll key with
    | .leaf => simp; linarith
    | .node _ _ _ _ => simp
    rw [<-ihlr]
    simp
    match STree.splay lr key with
    | .leaf => simp; assumption
    | .node _ _ _ _ => simp
  | ind_tr k v rl rk rv rr ihrl ihrr =>
    simp
    by_cases' (key = k) h1
    by_cases' (key < k) h2
    by_cases' (key = rk) h3
    by_cases' (key < rk) h4
    rw [<-ihrl]
    simp
    match STree.splay rl key with
    | .leaf => simp; linarith
    | .node _ _ _ _ => simp
    rw [<-ihrr]
    simp
    match STree.splay rr key with
    | .leaf => simp; assumption
    | .node _ _ _ _ => simp
  | ind k v ll lk lv lr rl rk rv rr ihll ihlr ihrl ihrr =>
    simp
    by_cases' (key = k) h1
    by_cases' (key < k) h2
    . by_cases' (key = lk) h3
      by_cases' (key < lk) h4
      rw [<-ihll]
      simp
      match STree.splay ll key with
      | .leaf => simp; linarith
      | .node _ _ _ _ => simp
      rw [<-ihlr]
      simp
      match STree.splay lr key with
      | .leaf => simp; assumption
      | .node _ _ _ _ => simp
    . by_cases' (key = rk) h3
      by_cases' (key < rk) h4
      rw [<-ihrl]
      simp
      match STree.splay rl key with
      | .leaf => simp; linarith
      | .node _ _ _ _ => simp
      rw [<-ihrr]
      simp
      match STree.splay rr key with
      | .leaf => simp; assumption
      | .node _ _ _ _ => simp    

-- NOTE: revert is a tactic

theorem splay_lookup_equiv (tree : STree α) (key : Nat)
  : (tree.lookup? key).1 = (tree.lookup' key).1 := by
  induction tree using STree.inductionOn with
  | base => rfl
  | ind_te k v => simp; by_cases' (key = k) h
  | ind_tl k v ll lk lv lr ihll ihlr =>
    simp at *
    by_cases' (key = k) h1
    by_cases' (key < k) h2
    by_cases' (key = lk) h3
    by_cases' (key < lk) h4
    . rw [<-ihll]
      match ll.splay key with
      | .leaf => simp [*]
      | .node _ k' _ _ =>
        simp
        by_cases' (key = k') h5
    . rw [<-ihlr]
      match lr.splay key with
      | .leaf => simp [*]
      | .node _ k' _ _ =>
        simp
        by_cases' (key = k') h5
  | ind_tr k v rl rk rv rr ihrl ihrr =>
    simp at *
    by_cases' (key = k) h1
    by_cases' (key < k) h2
    by_cases' (key = rk) h3
    by_cases' (key < rk) h4
    . rw [<-ihrl]
      match rl.splay key with
      | .leaf => simp [*]
      | .node _ k' _ _ =>
        simp
        by_cases' (key = k') h5
    . rw [<-ihrr]
      match rr.splay key with
      | .leaf => simp [*]
      | .node _ k' _ _ =>
        simp
        by_cases' (key = k') h5
  | ind k v ll lk lv lr rl rk rv rr ihll ihlr ihrl ihrr =>
    simp at *
    by_cases' (key = k) h1
    by_cases' (key < k) h2
    . by_cases' (key = lk) h3
      by_cases' (key < lk) h4
      . rw [<-ihll]
        match ll.splay key with
        | .leaf => simp [*]
        | .node _ k' _ _ =>
        simp
        by_cases' (key = k') h5
      . rw [<-ihlr]
        match lr.splay key with
        | .leaf => simp [*]
        | .node _ k' _ _ =>
        simp
        by_cases' (key = k') h5
    . by_cases' (key = rk) h3
      by_cases' (key < rk) h4
      . rw [<-ihrl]
        match rl.splay key with
        | .leaf => simp [*]
        | .node _ k' _ _ =>
          simp
          by_cases' (key = k') h5
      . rw [<-ihrr]
        match rr.splay key with
        | .leaf => simp [*]
        | .node _ k' _ _ =>
          simp
          by_cases' (key = k') h5

theorem splay_empty_helper (l r : STree α) (k key : Nat) (v : α) :
  STree.splay (.node l k v r) key ≠ STree.leaf := by
  cases l <;> cases r <;> simp [STree.splay] <;> by_cases' (key = k) h <;> by_cases' (key < k) h1
  . rename_i tl tk tv tr
    by_cases' (key = tk) h2
    by_cases' (key < tk) h3
    case pos =>
      match STree.splay tl key with
      | .leaf => simp
      | .node _ _ _ _ => simp
    case neg =>
      match STree.splay tr key with
      | .leaf => simp
      | .node _ _ _ _ => simp
  . rename_i tl tk tv tr
    by_cases' (key = tk) h2
    by_cases' (key < tk) h3
    case pos =>
      match STree.splay tl key with
      | .leaf => simp
      | .node _ _ _ _ => simp
    case neg =>
      match STree.splay tr key with
      | .leaf => simp
      | .node _ _ _ _ => simp
  all_goals (rename_i ll lk lv lr rl rk rv rr)
  . by_cases' (key = lk) h2
    by_cases' (key < lk) h3
    match STree.splay ll key with
    | .leaf => simp
    | .node _ _ _ _ => simp
    match STree.splay lr key with
    | .leaf => simp
    | .node _ _ _ _ => simp
  . by_cases' (key = rk) h2
    by_cases' (key < rk) h3
    match STree.splay rl key with
    | .leaf => simp
    | .node _ _ _ _ => simp
    match STree.splay rr key with
    | .leaf => simp
    | .node _ _ _ _ => simp

theorem splay_empty (t : STree α) (key : Nat) :
  t = STree.leaf <-> t.splay key = STree.leaf := by
  constructor
  . intro h
    rw [h]
    rfl
  . cases t with
    | leaf => simp
    | node l k v r =>
      intro h
      exfalso
      apply (splay_empty_helper l r k key v h)
