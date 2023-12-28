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

theorem obvious_arith (a b : Nat) : ¬ a = b -> ¬ a < b -> a > b := by
  intro h1 h2
  have h3 : a ≥ b := by linarith
  by_cases' (b < a) h4
  apply h1
  linarith

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
        apply ins_Forall
        assumption
        apply obvious_arith <;> assumption

-- TODO where to put?
inductive Forall {α : Type u} (p : α -> Prop) : List α -> Prop
  | nil : Forall p .nil
  | cons --(e : α) (l : List α)
    : p e ->
      Forall p l ->
      Forall p (e :: l)

theorem Forall_app {α : Type} (p : α -> Prop) (l1 l2 : List α)
  : Forall p l1 ∧ Forall p l2 <-> Forall p (l1 ++ l2) := by
  apply Iff.intro
  case mp =>
    induction l1 with
    | nil => simp
    | cons e l1 ihl1 =>
      intros h
      cases h
      rename_i hfl1 hfl2
      cases hfl1
      rename_i hpe hfl1
      constructor
      apply hpe
      apply ihl1
      apply And.intro <;> assumption
  case mpr =>
    induction l1 with
    | nil =>
      simp
      intro h
      apply And.intro
      constructor
      apply h
    | cons e l1 ih =>
      intro h
      cases h
      rename_i hpe hfl
      have ihl : Forall p l1 ∧ Forall p l2 := by
        apply ih
        apply hfl
      cases ihl
      rename_i ihl1 ihl2
      apply And.intro
      constructor <;> assumption
      assumption

def curry (f : α -> β -> γ) (x : α × β) :=
  match x with | (a, b) => f a b

theorem Forall_relate {α : Type} (p : Nat -> α -> Prop) (t : STree α)
  : ForallTree p t <-> Forall (curry p) t.elements := by
  apply Iff.intro
  case mp =>
    intro h
    induction h with
    | leaf => simp; constructor
    | node l k v r hfl hp hfr ihl ihr =>
      simp
      rw [<-Forall_app]
      apply And.intro
      assumption
      constructor <;> assumption
  case mpr =>
    intro h
    induction t with
    | leaf => constructor
    | node l k v r ihl ihr =>
      simp at h
      rw [<-Forall_app] at h
      cases h
      rename_i hl hr
      cases hr
      rename_i hp hr
      constructor <;> try simp [*]
      apply hp

theorem Forall_imp {α : Type} (p : α -> Prop) (q : α -> Prop) (l : List α)
  : Forall p l ->
    (∀ a, p a -> q a) ->
    Forall q l := by
  induction l with
  | nil =>
    intros
    constructor
  | cons e t ih =>
    intros h1 h2
    cases h1
    rename_i hpe h1
    constructor
    apply h2
    apply hpe
    apply ih
    apply h1
    apply h2
