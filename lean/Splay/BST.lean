import Mathlib.Tactic.Linarith

import Splay.STree
import Splay.Tactics

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
