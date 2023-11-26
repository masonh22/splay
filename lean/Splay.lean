import Mathlib.Tactic.Linarith

def hello := "splay"

inductive STree (α : Type u) where
  | leaf
  | node (left : STree α) (key : Nat) (value : α) (right : STree α)

-- TODO doc
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
def STree.bound (tree : STree α) (key : Nat) : Bool :=
  match tree with
  | leaf => false
  | node l k _ r =>
    if key = k then true
    else if key < k then l.bound key
    else r.bound key

-- TODO doc
-- implementing this in terms of splay is possible but it makes it hard to prove
-- things about it
def STree.bound' (tree : STree α) (key : Nat) : Bool :=
  match tree.splay key with
  | leaf => false
  | node _ k _ _ => key = k

-- TODO doc
-- lookup for normal BSTs
def STree.lookup_aux (tree : STree α) (d : α) (key : Nat) : α :=
  match tree with
  | leaf => d
  | node l k v r =>
    if key = k then v
    else if key < k then l.lookup_aux d key
    else r.lookup_aux d key

-- TODO doc
-- easier to prove things this way
def STree.lookup (tree : STree α) (d : α) (key : Nat) : α × STree α :=
  (tree.lookup_aux d key, tree.splay key)

def STree.lookup' (tree : STree α) (d : α) (key : Nat) : α × STree α :=
  match tree.splay key with
  | leaf => (d, leaf)
  | node l k v r =>
    if key = k then (v, node l k v r) else
      (d, node l k v r)

-- TODO doc
-- insert for normal bst
def STree.ins (tree : STree α) (key : Nat) (val : α) : STree α :=
  match tree with
  | leaf => node leaf key val leaf
  | node l k v r =>
    if key = k then node l key val r
    else if key < k then node (l.ins key val) k v r
    else node l k v (r.ins key val)

def STree.insert (tree : STree α) (key : Nat) (val : α) : STree α :=
  splay (tree.ins key val) key

def STree.elements (tree : STree α) : List (Nat × α) :=
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

---- TODO section the bst invariant ----

-- TODO doc
inductive ForallTree (p : Nat -> α -> Prop) : STree α -> Prop
  | leaf : ForallTree p .leaf
  | node :
    ForallTree p left ->
    p key value ->
    ForallTree p right ->
    ForallTree p (.node left key value right)

-- TODO doc
inductive BST : STree α -> Prop
  | leaf : BST .leaf
  | node :
    ForallTree (fun k _ => k < key) left ->
    ForallTree (fun k _ => k > key) right ->
    BST left -> BST right ->
    BST (.node left key value right)

theorem ForallTree_imp (p q : Nat -> α -> Prop) (t : STree α) :
  ForallTree p t ->
  (∀ key val, p key val -> q key val) ->
  ForallTree q t := by
  induction t with
  | leaf =>
    intro _ _
    constructor
  | node l k v r ihl ihr =>
    intro hf himp
    cases hf with
    | node hl hkv hr =>
      constructor <;> (first | apply ihl | apply himp | apply ihr) <;> assumption

theorem ForallTree_greater (t : STree α) (k k0 : Nat) :
  ForallTree (fun k' _ => k' > k) t ->
  k > k0 ->
  ForallTree (fun k' _ => k' > k0) t := by
  intro h1 h2
  apply ForallTree_imp (fun k' _ => k' > k) (fun k' _ => k' > k0)
  . assumption
  . intro key _ h3
    linarith

theorem ForallTree_less (t : STree α) (k k0 : Nat) :
  ForallTree (fun k' _ => k' < k) t ->
  k < k0 ->
  ForallTree (fun k' _ => k' < k0) t := by
  intro h1 h2
  apply ForallTree_imp (fun k' _ => k' < k) (fun k' _ => k' < k0)
  . assumption
  . intro key _ h3
    linarith

