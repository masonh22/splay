import Mathlib.Tactic.Linarith

local macro "have_eq " lhs:term:max rhs:term:max : tactic =>
  `(tactic|
    (have h : $lhs = $rhs :=
       -- TODO: replace with linarith
       by simp_arith at *; apply Nat.le_antisymm <;> assumption
     try subst $lhs))

local macro "by_cases' " e:term:max h:Lean.binderIdent : tactic =>
  `(tactic| by_cases $e <;> rename_i $h <;> simp [*])

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
def STree.lookup (tree : STree α) (key : Nat) : Option α × STree α :=
  match tree.splay key with
  | leaf => (none, leaf)
  | node l k v r =>
    if key = k then (some v, node l k v r) else
      (none, node l k v r)

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

---- TODO section the bst invariant, proving insert_BST ----

-- TODO doc
inductive ForallTree (p : Nat -> α -> Prop) : STree α -> Prop
  | leaf : ForallTree p .leaf
  | node : ∀ l k v r,
    ForallTree p l ->
    p k v ->
    ForallTree p r ->
    ForallTree p (.node l k v r)

-- TODO doc
inductive BST {α : Type u} : STree α -> Prop
  | leaf : BST .leaf
  | node : ∀ l k v r,
    ForallTree (fun k' _ => k' < k) l ->
    ForallTree (fun k' _ => k' > k) r ->
    BST l -> BST r ->
    BST (.node l k v r)

inductive splayBST {α : Type u} : STree α -> Prop
  | leaf : splayBST .leaf
  | node_e : ∀ k v, splayBST (.node .leaf k v .leaf)
  | node_l : ∀ k v ll lk lv lr,
    ForallTree (fun k' _ => k' < lk) ll ->
    ForallTree (fun k' _ => k' > lk) lr ->
    ForallTree (fun k' _ => k' < k) (.node ll lk lv lr) ->
    splayBST ll -> splayBST lr ->
    splayBST (.node (.node ll lk lv lr) k v .leaf)
  | node_r : ∀ k v rl rk rv rr,
    ForallTree (fun k _ => k < rk) rl ->
    ForallTree (fun k _ => k > rk) rr ->
    ForallTree (fun k' _ => k' > k) (.node rl rk rv rr) ->
    splayBST rl -> splayBST rr ->
    splayBST (.node .leaf k v (.node rl rk rv rr))
  | node_rl : ∀ k v ll lk lv lr rl rk rv rr,
    ForallTree (fun k _ => k < lk) ll ->
    ForallTree (fun k _ => k > lk) lr ->
    ForallTree (fun k _ => k < rk) rl ->
    ForallTree (fun k _ => k > rk) rr ->
    ForallTree (fun k' _ => k' < k) (.node ll lk lv lr) ->
    ForallTree (fun k' _ => k' > k) (.node rl rk rv rr) ->
    splayBST ll -> splayBST lr ->
    splayBST rl -> splayBST rr ->
    splayBST (.node (.node ll lk lv lr) k v (.node rl rk rv rr))

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

theorem splayBST_equiv (tree : STree α) : BST tree <-> splayBST tree := by
  constructor
  . intro h
    induction tree using STree.inductionOn with
    | base => constructor
    | ind_te k v =>
      apply splayBST.node_e
    | ind_tl k v ll lk lv lr ihll ihlr =>
      cases h with -- todo want a tactic to deal with breaking up bst and foralltree
      | node _ _ _ _ hfl _ hbstl _ =>
        cases hbstl with
        | node _ _ _ _ _ _ hbstll hbstlr =>
          cases hfl with
          | node _ _ _ _ hfll hineq hflr =>
            apply splayBST.node_l <;> try simp [*]
            constructor <;> assumption
    | ind_tr k v rl rk rv rr ihrl ihrr =>
      cases h with
      | node _ _ _ _ _ hfr _ hbstr =>
        cases hbstr with
        | node _ _ _ _ _ _ hbstrl hbstrr =>
          cases hfr with
          | node _ _ _ _ hfrl hineq hfrr =>
            apply splayBST.node_r <;> try simp [*]
            constructor <;> assumption
    | ind k v ll lk lv lr rl rk rv rr ihll ihlr ihrl ihrr =>
      cases h with
      | node _ _ _ _ hfl hfr hbstl hbstr =>
        cases hfl with
        | node _ _ _ _ hfll hlk hflr =>
          cases hfr with
          | node _ _ _ _ hfrl hrk hfrr =>
            cases hbstl with
            | node _ _ _ _ _ _ hbstll hbstlr =>
              cases hbstr with
              | node _ _ _ _ _ _ hbstrl hbstrr =>
                apply splayBST.node_rl <;> (try simp [*]) <;> constructor <;> assumption
  . intro h
    induction h with
    | leaf => constructor
    | node_e k v =>
      constructor <;> constructor
    | node_l k v ll lk lv lr hfll hflr hfl _ _ ihll ihlr =>
      cases hfl with
      | node _ _ _ _ hfll2 hlk hflr2 =>
      constructor <;> constructor <;> assumption
    | node_r k v rl rk rv rr hfrl hfrr hfr _ _ ihll ihrr =>
      cases hfr with
      | node _ _ _ _ hfrl2 hrk hfrr2 =>
        constructor <;> constructor <;> assumption
    | node_rl k v ll lk lv lr rl rk rv rr hfll hflr hfrl hfrr hfl hfr _ _ _ _ ihll ihlr ihrl ihrr =>
      cases hfl with
      | node _ _ _ _ hfll2 hlk hflr2 =>
        cases hfr with
        | node _ _ _ _ hfrl2 hrk hfrr2 =>
          constructor <;> constructor <;> assumption

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

theorem lookup_equiv (tree : STree α) (key : Nat)
  : (tree.lookup key).1 = (tree.lookup' key).1 := by
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

theorem ins_Forall (t : STree α) (key : Nat) (val : α) (p : Nat -> α -> Prop)
  : ForallTree p t ->
    p key val ->
    ForallTree p (t.ins key val) := by
  induction t with
  | leaf =>
    intros
    simp [STree.ins]
    constructor <;> assumption
  | node l k v r ihl ihr =>
    intro h hp
    simp [STree.ins]
    cases h with
    | node _ _ _ _ hfl hp2 hfr =>
      by_cases' (key = k) heq
      . rw [<-heq]
        constructor <;> assumption
      . by_cases' (key < k) hlt
        . constructor <;> simp [*]
        . constructor <;> simp [*]

theorem ins_BST (t : STree α) (key : Nat) (val : α)
  : BST t -> BST (t.ins key val) := by
  intro hbst
  induction hbst with
  | leaf => constructor <;> constructor
  | node l k v r hfl hfr hbstl hbstr ihl ihr =>
    simp [STree.ins]
    by_cases' (key = k) heq
    . constructor <;> simp [*]
    . by_cases' (key < k) hlt
      . constructor <;> try assumption
        apply ins_Forall <;> assumption
      . constructor <;> try assumption
        apply ins_Forall <;> try assumption
        sorry -- linarith can't do this????????

theorem splay_Forall (t : STree α) (key : Nat) (p : Nat -> α -> Prop)
  : ForallTree p t -> ForallTree p (t.splay key) := by
  induction t using STree.inductionOn with
  | base => intro h; simp; assumption
  | ind_te k v => intro h; simp; assumption
  | ind_tl k v ll lk lv lr ihll ihlr =>
    intro h
    simp
    by_cases' (key = k) heq
    by_cases' (key < k) hlt
    cases h with
    | node _ _ _ _ hfl hp =>
      cases hfl with
      | node _ _ _ _ hfll hpl hflr =>
        by_cases' (key = lk) heqlk
        . constructor <;> try assumption
          constructor <;> assumption
        . by_cases' (key < lk) hltlk
          . sorry -- TODO need to destruct but keep equation
          . sorry -- TODO need to destruct but keep equation
  | ind_tr k v rl rk rv rr ihrl ihrr =>
    intro h
    simp
    by_cases' (key = k) heq
    by_cases' (key < k) hlt
    cases h with
    | node _ _ _ _ _ hp hfr =>
      cases hfr with
      | node _ _ _ _ hfrl hpr hfrr =>
        by_cases' (key = rk) heqrk
        . constructor <;> try assumption
          constructor <;> assumption
        . by_cases' (key < rk) hltrk
          . sorry -- TODO need to destruct but keep equation
          . sorry -- TODO need to destruct but keep equation
  | ind k v ll lk lv lr rl rk rv rr ihll ihlr ihrl ihrr =>
    intro h
    simp
    by_cases' (key = k) heq
    cases h with
    | node _ _ _ _ hfl hp hfr =>
      by_cases' (key < k) hlt
      . cases hfl with
        | node _ _ _ _ hfll hpl hflr =>
          by_cases' (key = lk) heqlk
          . constructor <;> try assumption
            constructor <;> assumption
          . by_cases' (key < lk) hltlk
            . sorry -- TODO need to destruct but keep equation
            . sorry -- TODO need to destruct but keep equation
      . cases hfr with
        | node _ _ _ _ hfrl hpr hfrr =>
          by_cases' (key = rk) heqrk
          . constructor <;> try assumption
            constructor <;> assumption
          . by_cases' (key < rk) hltrk
            . sorry -- TODO need to destruct but keep equation
            . sorry -- TODO need to destruct but keep equation

theorem splay_splayBST (t : STree α) (key : Nat)
  : splayBST t -> splayBST (t.splay key) := by
  intro h
  induction h with
  | leaf => simp; apply splayBST.leaf
  | node_e k v => simp; apply splayBST.node_e
  | node_l k v ll lk lv lr hfll hflr hfl hsbstll hsbstlr ihll ihlr =>
    simp
    by_cases' (key = k) heq
    case pos =>
      apply splayBST.node_l <;> simp [*]
    case neg =>
      by_cases' (key < k) hlt
      case pos =>
        cases hfl with
        | node _ _ _ _ hfll2 hlk hflr2 => 
          by_cases' (key = lk) hlkeq
          . rw [<-splayBST_equiv]
            constructor
            . assumption
            . constructor <;> try assumption
              constructor
            . rw [splayBST_equiv]; assumption
            . constructor
              assumption
              constructor
              rw [splayBST_equiv]; assumption
              constructor
          . by_cases' (key < lk) hlklt
            . match ll.splay key with
              | .leaf =>
                simp
                rw [<-splayBST_equiv]
                constructor
                assumption
                constructor
                assumption
                assumption
                constructor
                rw [splayBST_equiv]; assumption
                constructor
                assumption
                constructor
                rw [splayBST_equiv]; assumption
                constructor
              | .node lll llk llv llr =>
                simp
                rw [<-splayBST_equiv]
                constructor
                -- TODO lost info here: ll.splay key = .node lll llk llv llr
                sorry
                sorry
                sorry
                constructor
                sorry
                constructor
                assumption
                assumption
                constructor
                sorry
                constructor
                assumption
                constructor
                rw [splayBST_equiv]; assumption
                constructor
            . sorry -- gonna lose information unless I can destruct and keep the equality
      case neg =>
        apply splayBST.node_l <;> assumption
  | node_r k v rl rk rv rr hfrl hfrr hfr hsbstrl hsbstrr ihrl ihrr => sorry
  | node_rl k v ll lk lv lr rl rk rv rr hfll hflr hfrl hfrr hfl hfr hsbstll hsbstlr hbstrl hbstrr ihll ihlr ihrl ihrr => sorry

theorem splay_BST (t : STree α) (key : Nat)
  : BST t -> BST (t.splay key) := by
  intro h
  rw [splayBST_equiv] at *
  apply splay_splayBST
  assumption

theorem insert_BST (t : STree α) (key : Nat) (val : α)
  : BST t -> BST (t.insert key val) := by
  intro h
  unfold STree.insert
  apply splay_BST
  apply ins_BST
  assumption

------- TODO section doc; model verification -------

------- TODO section doc; algebraic spec -------

