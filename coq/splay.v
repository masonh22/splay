(* Source (1) https://www.cs.cornell.edu/courses/cs3110/2011sp/Recitations/rec25-splay/splay.htm *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.

Definition geb (n m : nat) := m <=? n.
Hint Unfold geb : core.
Infix ">=?" := geb (at level 70) : nat_scope.

Definition gtb (n m : nat) := m <? n.
Hint Unfold gtb : core.
Infix ">?" := gtb (at level 70) : nat_scope.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Lemma gtb_reflect : forall x y, reflect (x > y) (x >? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma geb_reflect : forall x y, reflect (x >= y) (x >=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect gtb_reflect geb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in
  let e := fresh "e" in
  evar (e: Prop);
  assert (H: reflect e X); subst e;
  [ auto with bdestruct
  | destruct H as [H|H];
    [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  | |- context [ if ?X >=? ?Y then _ else _ ] => bdestruct (X >=? Y)
  | |- context [ if ?X >? ?Y then _ else _ ] => bdestruct (X >? Y)
  end.

Ltac bdall :=
  repeat (simpl; bdestruct_guard; try lia; auto).

Ltac inv H := inversion H; clear H; subst.

(** * Splay Trees *)

Definition key := nat.

(** [tree] is defined exactly as it is in SearchTree.v *)
Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.
Arguments T {V}.

(** [empty_tree] contains no bindings. *)
Definition empty_tree {V : Type} : tree V := E.

(** [value d t] is the value at the root of the [t], or is
    the default value d if [t] is empty. *)
(* TODO unused *)
Definition value {V : Type} (d : V) (t : tree V) :=
  match t with
  | E => d
  | T _ _ v _ => v
  end.

(** [splay t k] is a BST node [n'] where [n'] contains
    all the elements that [n] does, and if an element
    keyed by [k] is in under [n], the value of node
    [n'] is that element.
    Requires: [t] is a BST. (1) *)
Fixpoint splay {V : Type} (t : tree V) (x : key) :=
  match t with
  | E => E
  | T l k v r =>
  if x =? k then t
  else if x <? k then
         (match l with
          | E => t (* not found *)
          | T ll lk lv lr =>
              if x =? lk then T ll lk lv (T lr k v r) (* 1: zig *)
              else if x <? lk then
                     (match splay ll x with
                      | E => T ll lk lv (T lr k v r) (* not found*)
                      | T lll llk llv llr => (* 2: zig-zig *)
                          T lll llk llv (T llr lk lv (T lr k v r))
                      end)
                   else (* greater than *)
                     (match splay lr x with
                      | E => T ll lk lv (T lr k v r) (* not found *)
                      | T lrl lrk lrv lrr => (* 3: zig-zag *)
                          T (T ll lk lv lrl) lrk lrv (T lrr k v r)
                      end)
          end)
       else (* greater than *)
         (match r with
          | E => t (* not found *)
          | T rl rk rv rr =>
              if x =? rk then T (T l k v rl) rk rv rr (* 1: zag *)
              else if x <? rk then
                     (match splay rl x with
                      | E => T (T l k v rl) rk rv rr (* not found*)
                      | T rll rlk rlv rlr => (* 3: zag-zig *)
                          T (T l k v rll) rlk rlv (T rlr rk rv rr)
                      end)
                   else (* greater than *)
                     (match splay rr x with
                      | E => T (T l k v rl) rk rv rr (* not found*)
                      | T rrl rrk rrv rrr => (* 2: zag-zag *)
                          T (T (T l k v rl) rk rv rrl) rrk rrv rrr
                      end)
          end)
  end.

(** [bound k t] is whether [k] is bound in [t]. *)
Fixpoint bound {V : Type} (x : key) (t : tree V) : bool :=
  match t with
  | E => false
  | T l k _ r =>
      if x =? k then true
      else if x <? k then bound x l
           else bound x r
  end.

(* implementing this in terms of splay makes it hard to prove things
   about it *)
Definition bound' {V : Type} (x : key) (t : tree V) : bool :=
  match splay t x with
  | E => false
  | T _ k _ _ => x =? k
  end.

(* this is lookup for normal BSTs *)
Fixpoint lookup_aux {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l k v r =>
      if x =? k then v
      else if x <? k then lookup_aux d x l
           else lookup_aux d x r
  end.

(** [lookup d k t] is a tuple [(v, t')], where [v] is the
    value bound to [k] in [t] and [t'] is the "splayed" tree. *)
(* its easier to prove things about it when implemented like this *)
Definition lookup {V : Type} (d : V) (x : key) (t : tree V) : V * tree V :=
  (lookup_aux d x t, splay t x).

(* this is insert for normal BSTs *)
Fixpoint ins {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l k v' r =>
      if x =? k then T l k v r
      else if x <? k then T (ins x v l) k v' r
           else T l k v' (ins x v r)
  end.

(** [insert k v t] is the map containing all the bindings of [t]
    along with a binding of [k] to [v]. *)
Definition insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  splay (ins x v t) x.

(* from SearchTree.v *)
Fixpoint elements {V : Type} (t : tree V) : list (key * V) :=
  match t with
  | E => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  end.

(** [size t] is the number of bindings in [t]. *)
Fixpoint size {V : Type} (t : tree V) : nat :=
  match t with
  | E => 0
  | T l _ _ r => S (size l + size r)
  end.

Module Tests.
  Open Scope string_scope.

  (* A < x < B < y < C < z < D *)
  Definition A := T E 0 "A" E.
  Definition x := 1.
  Definition B := T E 2 "B" E.
  Definition y := 3.
  Definition C := T E 4 "C" E.
  Definition z := 5.
  Definition D := T E 6 "D" E.

  (*    (1)           (2)
   *     y             x
   *    / \           / \
   *   x   C   <->   A   y
   *  / \               / \
   * A   B             B   C
   *)
  Definition T1 := T (T A x "x" B) y "y" C.
  Definition T2 := T A x "x" (T B y "y" C).

  Example splay_zig : splay T1 x = T2.
  Proof. reflexivity. Qed.

  Example splay_zag : splay T2 y = T1.
  Proof. reflexivity. Qed.

  (*      (3)           (4)
   *       z             x
   *      / \           / \
   *     y   D         A   y
   *    / \      <->      / \    (A < x < B < y < C < z < D)
   *   x   C             B   z
   *  / \                   / \
   * A   B                 C   D
   *)
  Definition T3 := T (T (T A x "x" B) y "y" C) z "z" D.
  Definition T4 := T A x "x" (T B y "y" (T C z "z" D)).

  Example splay_zig_zig : splay T3 x = T4.
  Proof. reflexivity. Qed.

  Example splay_zag_zag : splay T4 z = T3.
  Proof. reflexivity. Qed.

  (*       (5)              (6)              (7)
   *        z                y                x
   *       / \              / \              / \
   *      x   D            /   \            A   z   (A < x < B < y < C < z < D)
   *     / \         ->   x     z    <-        / \
   *    A   y            / \   / \            y   D
   *       / \          A   B C   D          / \
   *      B   C                             B   C
   *)
  Definition T5 := T (T A x "x" (T B y "y" C)) z "z" D.
  Definition T6 := T (T A x "x" B) y "y" (T C z "z" D).
  Definition T7 := T A x "x" (T (T B y "y" C) z "z" D).

  Example splay_zig_zag : splay T5 y = T6.
  Proof. reflexivity. Qed.

  Example splay_zag_zig : splay T7 y = T6.
  Proof. reflexivity. Qed.

  Example splay_not_found :
    splay T7 100 = T (T (T A x "x" (T B y "y" C)) z "z" E) 6 "D" E.
  Proof. reflexivity. Qed.

  Definition T8 := insert 3 "c" (insert 1 "a" (insert 2 "b" empty_tree)).

  Example insert_test : T8 = T (T (T E 1 "a" E) 2 "b" E) 3 "c" E.
  Proof. reflexivity. Qed.

  Example empty_size_0 : size (@empty_tree nat) = 0.
  Proof. reflexivity. Qed.

  Example insert_size : size T8 = 3.
  Proof. reflexivity. Qed.

  Example bound_test_1 : bound y T6 = true.
  Proof. reflexivity. Qed.

  Example bound_test_2 : bound x T6 = true.
  Proof. reflexivity. Qed.

  Example bound_test_3 : bound z T6 = true.
  Proof. reflexivity. Qed.

  Example bound_test_4 : bound 100 T6 = false.
  Proof. reflexivity. Qed.

End Tests.

(** * The BST Invariant *)

(* from Redblack.v *)
Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

(* from Redblack.v *)
Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

Hint Constructors BST : core.

(* from Redblack.v *)
Lemma ForallT_imp : forall (V : Type) (P Q : key -> V -> Prop) (t : tree V),
    ForallT P t ->
    (forall k v, P k v -> Q k v) ->
    ForallT Q t.
Proof.
  induction t; intros.
  - auto.
  - inv H. destruct H2. repeat split; auto.
Qed.

(* from Redblack.v *)
Lemma ForallT_greater : forall (V : Type) (t : tree V) (k k0 : key),
    ForallT (fun k' _ => k' > k) t ->
    k > k0 ->
    ForallT (fun k' _ => k' > k0) t.
Proof.
  intros. eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.

(* from Redblack.v *)
Lemma ForallT_less : forall (V : Type) (t : tree V) (k k0 : key),
    ForallT (fun k' _ => k' < k) t ->
    k < k0 ->
    ForallT (fun k' _ => k' < k0) t.
Proof.
  intros. eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.

(* A helpful tactic to use when proving things about the splay function *)
Ltac splay :=
  repeat
      match goal with
      | |- BST (match ?t with E => _ | T _ _ _ _ => _ end) =>
          destruct t eqn:?; auto
      | |- BST (if ?x then _ else _) => bdall
      | |- BST (T _ _ _ _) => constructor; auto
      | |- ForallT _ (T _ _ _ _) => repeat split
      | H: BST (T _ _ _ _) |- _ => inv H
      | H: ForallT _ (T _ _ _ _) |- _ => destruct H as [? [? ?]]
      end.

(* A new inductive principle is necessary for proofs involving splay *)
Definition splay_tree_ind_type : Prop :=
  forall (V : Type) (P : tree V -> Prop),
    P E ->
    (forall (k : key) (v : V), P (T E k v E)) ->
    (forall (k lk : key) (v lv : V) (ll lr : tree V),
        P ll -> P lr ->
        P (T (T ll lk lv lr) k v E)) ->
    (forall (k rk : key) (v rv : V) (rl rr : tree V),
        P rl -> P rr ->
        P (T E k v (T rl rk rv rr))) ->
    (forall (k lk rk : key) (v lv rv : V) (ll lr rl rr : tree V),
        P ll -> P lr -> P rl -> P rr ->
        P (T (T ll lk lv lr) k v (T rl rk rv rr))) ->
    forall t : tree V, P t.

Definition splay_tree_ind : splay_tree_ind_type :=
  fun V P base_e base_1 ind_l ind_r ind =>
    fix build t :=
    match t with
    | E => base_e
    | T E k v E => base_1 k v
    | T (T ll lk lv lr) k v E =>
        ind_l k lk v lv ll lr
              (build ll) (build lr)
    | T E k v (T rl rk rv rr) =>
        ind_r k rk v rv rl rr
              (build rl) (build rr)
    | T (T ll lk lv lr) k v (T rl rk rv rr) =>
        ind k lk rk v lv rv ll lr rl rr
            (build ll) (build lr) (build rl) (build rr)
    end.

Lemma splay_not_E : forall (V : Type) (t l r : tree V) (k k' : key) (v : V),
    t = T l k' v r -> splay (T l k' v r) k <> E.
Proof.
  intros; destruct t; try discriminate.
  inv H. simpl. bdall; try discriminate;
    repeat
      match goal with
      | |- match ?t with E => _ | T _ _ _ _ => _ end <> _ =>
          destruct t; try discriminate
      | |- (if ?x then _ else _) <> _ => bdall; try discriminate
      end.
Qed.

Lemma splay_empty : forall (V : Type) (k : key) (t : tree V),
    t = E <-> splay t k = E.
Proof.
  split; intros.
  - subst. reflexivity.
  - destruct t.
    + reflexivity.
    + apply splay_not_E with (t:=T t1 k0 v t2) in H; tauto.
Qed.

Lemma ins_not_E : forall (V : Type) (t : tree V) (k : key) (v : V),
    ins k v t <> E.
Proof.
  intros. destruct t; simpl.
  - discriminate.
  - bdestruct (k =? k0); try discriminate.
    bdestruct (k <? k0); discriminate.
Qed.

Lemma insert_not_E : forall (V : Type) (t : tree V) (k : key) (v : V),
    insert k v t <> E.
Proof.
  intros. unfold insert. destruct (ins k v t) eqn:EQins.
  - apply ins_not_E in EQins. destruct EQins.
  - eapply splay_not_E. reflexivity.
Qed.

Inductive InBST {V : Type} : key -> V -> tree V -> Prop :=
| in_root : forall (l : tree V) (k : key) (v : V) (r : tree V),
    InBST k v (T l k v r)
| in_left : forall (l : tree V) (k : key) (v v' : V) (r : tree V) (k' : key),
    k' < k ->
    InBST k' v' l ->
    InBST k' v' (T l k v r)
| in_right : forall (l : tree V) (k : key) (v v' : V) (r : tree V) (k' : key),
    k' > k ->
    InBST k' v' r ->
    InBST k' v' (T l k v r).

Hint Constructors InBST : core.

Lemma lookup_if_in :
  forall (V : Type) (t : tree V) (k : key) (d v : V),
    InBST k v t -> lookup_aux d k t = v.
Proof.
  intros. induction H; simpl; bdall.
Qed.

(** ForallT related things. Not related to splay at all, but used
    in some later proofs. *)
Lemma ForallT_forall :
  forall (V : Type) (t : tree V) (k : key) (v : V) (P : key -> V -> Prop),
    ForallT P t -> InBST k v t -> P k v.
Proof.
  induction t.
  - intros. inv H0.
  - intros. inv H0.
    + inv H. apply H0.
    + inv H. inv H1. apply IHt1; auto.
    + inv H. inv H1. apply IHt2; auto.
Qed.

Lemma forall_lt :
  forall (V : Type) (t : tree V) (k k' : key) (v : V),
    ForallT (fun y _ => y < k') t -> InBST k v t -> k < k'.
Proof.
  intros.
  assert (HA: forall P, P = (fun (y : key) _ => y < k') -> P k v).
  { intros. eapply ForallT_forall. rewrite <- H1 in H. apply H.
    apply H0. }
  specialize HA with (P := (fun (y : key) _ => y < k')).
  assert (Hb: (fun (y : key) (_ : V) => y < k') = (fun (y : key) (_ : V) => y < k'))
    by reflexivity.
  apply HA in Hb. assumption.
Qed.

Lemma forall_gt :
  forall (V : Type) (t : tree V) (k k' : key) (v : V),
    ForallT (fun y _ => y > k') t -> InBST k v t -> k > k'.
Proof.
  intros.
  assert (HA: forall P, P = (fun (y : key) _ => y > k') -> P k v).
  { intros. eapply ForallT_forall. rewrite <- H1 in H. apply H.
    apply H0. }
  specialize HA with (P := (fun (y : key) _ => y > k')).
  assert (Hb: (fun (y : key) (_ : V) => y > k') = (fun (y : key) (_ : V) => y > k'))
    by reflexivity.
  apply HA in Hb. assumption.
Qed.

Lemma in_lt_gt :
  forall (V : Type) (l r : tree V) (k k' : key) (v v' : V),
    BST (T l k v r) ->
    (InBST k' v' l -> k' < k) /\ (InBST k' v' r -> k' > k).
Proof.
  intros. inv H.
  split; intros.
  - apply forall_lt with (V:=V) (t:=l) (v:=v'); assumption.
  - apply forall_gt with (V:=V) (t:=r) (v:=v'); assumption.
Qed.
(** [] *)

(** * Proving insert_BST *)
Lemma in_bst_lr :
  forall (V : Type) (l r : tree V) (k : key) (v : V),
    BST (T l k v r) ->
    (forall (k': key) (v' : V), InBST k' v' l -> InBST k' v' (T l k v r)) /\
      (forall (k': key) (v' : V), InBST k' v' r -> InBST k' v' (T l k v r)).
Proof.
  intros. split; intros.
  - assert (Hlt: k' < k).
    { eapply in_lt_gt with (k':=k'); eauto. }
    apply in_left; assumption.
  - assert (Hgt: k' > k).
    { eapply in_lt_gt with (k':=k'); eauto. }
    apply in_right; assumption.
Qed.

(* This could be automated better. The inductive cases are essentially
   copy/pasted. *)
Lemma splay_in :
  forall (V : Type) (t l' r' : tree V) (k0 k' : key) (v' : V),
    BST t ->
    splay t k0 = T l' k' v' r' ->
    InBST k' v' t.
Proof.
  intros V.
  change (forall (t' : tree V), (fun t => forall l' r' k0 k' v',
                                BST t ->
                                splay t k0 = T l' k' v' r' ->
                                InBST k' v' t) t').
  apply splay_tree_ind.
  - (* t = E *)
    simpl. discriminate.
  - (* t = T E k v E *)
    simpl. intros. bdestruct (k0 =? k).
    + inv H0. apply in_root.
    + bdestruct (k0 <? k); inv H0; apply in_root.
  - (* t = T (T ll lk lv lr) k v E *)
    intros. simpl in H2. bdestruct (k0 =? k); try (inv H2; apply in_root).
    bdestruct (k0 <? k).
    + (* k0 < k *)
      bdestruct (k0 =? lk). inv H2. auto.
      bdestruct (k0 <? lk).
      * destruct (splay ll k0) as [| lll llk llv llr] eqn:HS.
        -- apply splay_empty in HS. inv H2. splay. auto.
        -- inv H1.
           assert (Hin1: InBST llk llv ll).
           { apply (H lll llr k0 llk llv). inv H13. assumption. apply HS. }
           assert (Hin2: InBST k' v' (T ll lk lv lr)).
           { inv H2. apply in_left; try assumption.
             eapply in_lt_gt with (k':=k'); eauto. }
           apply in_left; try assumption.
           eapply in_lt_gt with (k':=k') (v:=v); eauto.
      * (* k0 > lk *)
        destruct (splay lr k0) as [| lrl lrk lrv lrr] eqn:HS.
        -- apply splay_empty in HS. inv H2. splay. auto.
        -- inv H1. assert (Hin1: InBST lrk lrv lr).
           { apply (H0 lrl lrr k0 lrk lrv). splay. auto. apply HS. }
           assert (Hin2: InBST k' v' (T ll lk lv lr)).
           { inv H2. apply in_right; try assumption.
             eapply in_lt_gt with (k':=k'); eauto. }
           apply in_left; try assumption.
           eapply in_lt_gt with (k':=k') (v:=v); eauto.
    + (* k0 > k *)
      inv H2. auto.
  - (* t = T E k v (T rl rk rv rr) *)
    intros. simpl in H2. bdestruct (k0 =? k); try (inv H2; apply in_root).
    bdestruct (k0 <? k).
    + (* k0 < k *)
      inv H2. auto.
    + (* k0 > k *)
      bdestruct (k0 =? rk). inv H2. apply in_right; try lia; auto.
      bdestruct (k0 <? rk).
      * (* k0 < rk *)
        destruct (splay rl k0) as [| rll rlk rlv rlr] eqn:HS.
        -- apply splay_empty in HS. inv H2. splay. auto.
        -- inv H1. assert (Hin1: InBST rlk rlv rl).
           { eapply H. inv H14. assumption. apply HS. }
           assert (Hin2: InBST k' v' (T rl rk rv rr)).
           { inv H2. apply in_left; try assumption.
             eapply in_lt_gt with (k':=k'); eauto. }
           apply in_right; try assumption.
           eapply in_lt_gt with (k':=k') (v:=v); eauto.
      * (* k0 > rk *)
        destruct (splay rr k0) as [| rrl rrk rrv rrr] eqn:HS.
        -- apply splay_empty in HS. inv H2. splay. auto.
        -- inv H1. assert (Hin1: InBST rrk rrv rr).
           { eapply H0. splay. auto. apply HS. }
           assert (Hin2: InBST k' v' (T rl rk rv rr)).
           { inv H2. apply in_right; try assumption.
             eapply in_lt_gt with (k':=k'); eauto. }
           apply in_right; try assumption.
           eapply in_lt_gt with (k':=k') (v:=v); eauto.
  - (* t = T (T ll lk lv lr) k v (T rl rk rv rr) *)
    intros. simpl in H4. bdestruct (k0 =? k); try (inv H4; apply in_root).
    bdestruct (k0 <? k).
    + (* k0 < k *)
      bdestruct (k0 =? lk). inv H4. auto.
      bdestruct (k0 <? lk).
      * (* k0 < lk *)
        destruct (splay ll k0) as [| lll llk llv llr] eqn:HS.
        -- apply splay_empty in HS. inv H4. splay. auto.
        -- inv H3. assert (Hin1: InBST llk llv ll).
           { eapply H. inv H15. assumption. apply HS. }
           assert (Hin2: InBST k' v' (T ll lk lv lr)).
           { inv H4. apply in_left; try assumption.
             eapply in_lt_gt with (k':=k'); eauto. }
           apply in_left; try assumption.
           eapply in_lt_gt with (k':=k') (v:=v); eauto.
      * (* k0 > lk *)
        destruct (splay lr k0) as [| lrl lrk lrv lrr] eqn:HS.
        -- apply splay_empty in HS. inv H4. splay. auto.
        -- inv H3. assert (Hin1: InBST lrk lrv lr).
           { eapply H0. splay. auto. apply HS. }
           assert (Hin2: InBST k' v' (T ll lk lv lr)).
           { inv H4. apply in_right; try assumption.
             eapply in_lt_gt with (k':=k'); eauto. }
           apply in_left; try assumption.
           eapply in_lt_gt with (k':=k') (v:=v); eauto.
    + (* k0 > k *)
      bdestruct (k0 =? rk). inv H4. apply in_right; try lia; auto.
      bdestruct (k0 <? rk).
      * (* k0 < rk *)
        destruct (splay rl k0) as [| rll rlk rlv rlr] eqn:HS.
        -- apply splay_empty in HS. inv H4. splay. auto.
        -- inv H3. assert (Hin1: InBST rlk rlv rl).
           { eapply H1. inv H16. assumption. apply HS. }
           assert (Hin2: InBST k' v' (T rl rk rv rr)).
           { inv H4. apply in_left; try assumption.
             eapply in_lt_gt with (k':=k'); eauto. }
           apply in_right; try assumption.
           eapply in_lt_gt with (k':=k') (v:=v); eauto.
      * (* k0 > rk *)
        destruct (splay rr k0) as [| rrl rrk rrv rrr] eqn:HS.
        -- apply splay_empty in HS. inv H4. splay. auto.
        -- inv H3. assert (Hin1: InBST rrk rrv rr).
           { eapply H2. splay. auto. apply HS. }
           assert (Hin2: InBST k' v' (T rl rk rv rr)).
           { inv H4. apply in_right; try assumption.
             eapply in_lt_gt with (k':=k'); eauto. }
           apply in_right; try assumption.
           eapply in_lt_gt with (k':=k') (v:=v); eauto.
Qed.

Lemma ForallT_splay :
  forall (V : Type) (k : key) (t : tree V) (P : key -> V -> Prop),
    ForallT P t -> ForallT P (splay t k).
Proof.
  intros V k0.
  change (forall t' : tree V, (fun t => forall P : key -> V -> Prop,
                              ForallT P t -> ForallT P (splay t k0)) t').
  apply splay_tree_ind; intros; auto; simpl; bdall;
    try (splay; auto; reflexivity);
    match goal with
    | |- ForallT ?P (match splay ?l ?k with E => _ | T _ _ _ _ => _ end) =>
        destruct (splay l k) as [| ls ks vs rs] eqn:HS;
        [ splay; auto |
          assert (IH: ForallT P (T ls ks vs rs)) by
          (try (apply H; splay; auto); try (apply H0; splay; auto);
           try (apply H1; splay; auto); try (apply H2; splay; auto));
          splay; auto ]
    end.
Qed.

Lemma ForallT_splay_rev :
    forall (V : Type) (k : key) (t : tree V) (P : key -> V -> Prop),
    ForallT P (splay t k) -> ForallT P t.
Proof.
  intros V k0.
  change (forall t' : tree V, (fun t => forall P : key -> V -> Prop,
                              ForallT P (splay t k0) -> ForallT P t) t').
  apply splay_tree_ind; auto;
    [ intros k v P; simpl; bdall
    | intros k lk v lv ll lr IHll IHlr P
    | intros k rk v rv rl rr IHrl IHrr P
    | intros k lk rk v lv rv ll lr rl rr IHll IHlr IHrl IHrr P ];
    simpl; bdall; intros; splay;
    repeat
        (match goal with
         | H : ForallT ?P (match splay ?l k0 with E => _ | T _ _ _ _ => _ end) |- _ =>
             destruct (splay l k0) eqn:HS; splay; auto
         | |- _ /\ _ => split; auto
         | IH : forall P : key -> V -> Prop, _ -> ForallT P ?l |- ForallT ?P ?l =>
             apply IH; splay; auto
         end).
Qed.

(* This could be automated better. The inductive cases are essentially
   copy/pasted. *)
Lemma splay_BST : forall (V : Type) (k : key) (t : tree V),
    BST t -> BST (splay t k).
Proof.
  intros V k0.
  change (forall (t' : tree V), (fun t => BST t -> BST (splay t k0)) t').
  apply splay_tree_ind.
  - (* t = E *)
    auto.
  - (* t = T E k v E *)
    intros. inv H. simpl. bdall.
  - (* t = T (T ll lk lv lr) k v E *)
    intros. simpl. bdestruct (k0 =? k).
    (* k0 = k *)
    apply H1.
    bdestruct (k0 <? k).
    + (* k0 < k *)
      bdestruct (k0 =? lk).
      (* k0 = lk *)
      splay; auto.
      bdestruct (k0 <? lk).
      * (* k0 < lk *)
        destruct (splay ll k0) as [| ls ks vs rs] eqn:HS.
        splay; auto; lia.
        assert (HBST: BST ll) by (splay; auto).
        assert (IH: BST (T ls ks vs rs)) by auto.
        assert (Hin1: InBST ks vs ll) by (apply splay_in in HS; auto).
        assert (Hin2: InBST ks vs ll) by (apply splay_in in HS; auto).
        assert (Hin3: InBST ks vs ll) by (apply splay_in in HS; auto).
        assert (Himp1: InBST ks vs ll -> InBST ks vs (T ll lk lv lr)).
        { eapply in_bst_lr. splay; auto. }
        assert (Himp2: InBST ks vs (T ll lk lv lr) -> InBST ks vs (T (T ll lk lv lr) k v E)).
        { eapply in_bst_lr. assumption. }
        apply Himp1 in Hin2. apply Himp1 in Hin3. apply Himp2 in Hin3.
        clear Himp1. clear Himp2.
        assert (Hlt1: lk < k) by (splay; assumption).
        assert (Hlt2: ks < lk).
        { eapply in_lt_gt with (k':=ks) (v':=vs). inv H1. apply H12.
          assumption. }
        assert (Hforall: ForallT (fun (y : key) (_ : V) => y < lk) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        splay; auto. lia. eapply ForallT_greater; eauto.
      * (* k0 > lk *)
        destruct (splay lr k0) as [| ls ks vs rs] eqn:HS.
        splay; auto; lia.
        assert (HBST: BST lr) by (splay; auto).
        assert (IH: BST (T ls ks vs rs)) by auto.
        assert (Hin1: InBST ks vs lr) by (apply splay_in in HS; auto).
        assert (Himp1: InBST ks vs lr -> InBST ks vs (T ll lk lv lr)).
        { eapply in_bst_lr. splay; auto. }
        assert (Himp2: InBST ks vs (T ll lk lv lr) -> InBST ks vs (T (T ll lk lv lr) k v E)).
        { eapply in_bst_lr. assumption. }
        assert (Hin2: InBST ks vs lr) by (apply splay_in in HS; auto).
        assert (Hin3: InBST ks vs lr) by (apply splay_in in HS; auto).
        apply Himp1 in Hin2. apply Himp1 in Hin3. apply Himp2 in Hin3.
        clear Himp1. clear Himp2.
        assert (Hlt1: lk < k) by (splay; assumption).
        assert (Hlt2: ks > lk).
        { eapply in_lt_gt with (k':=ks) (v':=vs). inv H1. apply H12.
          assumption. }
        assert (Hlt3: ks < k).
        { eapply in_lt_gt with (k':=ks) (v':=vs). apply H1.
          assumption. }
        assert (Hforall1: ForallT (fun (y : key) (_ : V) => y > lk) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        assert (Hforall2: ForallT (fun (y : key) (_ : V) => y < k) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        splay; auto. eapply ForallT_less; eauto.
    + (* k0 > k *)
      assumption.
  - (* t = T E k v (T rl rk rv rr) *)
    intros. simpl. bdestruct (k0 =? k).
    (* k0 = k *)
    apply H1.
    bdestruct (k0 <? k).
    + (* k0 < k *)
      assumption.
    + (* k0 > k *)
      bdestruct (k0 =? rk).
      (* k0 = rk *)
      splay; auto.
      bdestruct (k0 <? rk).
      * (* k0 < rk *)
        destruct (splay rl k0) as [| ls ks vs rs] eqn:HS.
        splay; auto; lia.
        assert (HBST: BST rl) by (splay; auto).
        assert (IH: BST (T ls ks vs rs)) by auto.
        assert (Hin1: InBST ks vs rl) by (apply splay_in in HS; auto).
        assert (Himp1: InBST ks vs rl -> InBST ks vs (T rl rk rv rr)).
        { eapply in_bst_lr. splay; auto. }
        assert (Himp2: InBST ks vs (T rl rk rv rr) -> InBST ks vs (T E k v (T rl rk rv rr))).
        { eapply in_bst_lr. assumption. }
        assert (Hin2: InBST ks vs rl) by (apply splay_in in HS; auto).
        assert (Hin3: InBST ks vs rl) by (apply splay_in in HS; auto).
        apply Himp1 in Hin2. apply Himp1 in Hin3. apply Himp2 in Hin3.
        clear Himp1. clear Himp2.
        assert (Hlt1: rk > k) by (splay; assumption).
        assert (Hlt2: ks < rk).
        { eapply in_lt_gt with (k':=ks) (v':=vs). inv H1. apply H13.
          assumption. }
        assert (Hlt3: ks > k).
        { eapply in_lt_gt with (k':=ks) (v':=vs). apply H1.
          assumption. }
        assert (Hforall1: ForallT (fun (y : key) (_ : V) => y < rk) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        assert (Hforall2: ForallT (fun (y : key) (_ : V) => y > k) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        splay; auto. eapply ForallT_greater; eauto.
      * (* k0 > rk *)
        destruct (splay rr k0) as [| ls ks vs rs] eqn:HS.
        splay; auto; lia.
        assert (HBST: BST rr) by (splay; auto).
        assert (IH: BST (T ls ks vs rs)) by auto.
        assert (Hin1: InBST ks vs rr) by (apply splay_in in HS; auto).
        assert (Himp1: InBST ks vs rr -> InBST ks vs (T rl rk rv rr)).
        { eapply in_bst_lr. splay; auto. }
        assert (Himp2: InBST ks vs (T rl rk rv rr) -> InBST ks vs (T E k v (T rl rk rv rr))).
        { eapply in_bst_lr. assumption. }
        assert (Hin2: InBST ks vs rr) by (apply splay_in in HS; auto).
        assert (Hin3: InBST ks vs rr) by (apply splay_in in HS; auto).
        apply Himp1 in Hin2. apply Himp1 in Hin3. apply Himp2 in Hin3.
        clear Himp1. clear Himp2.
        assert (Hlt1: rk > k) by (splay; assumption).
        assert (Hlt2: ks > rk).
        { eapply in_lt_gt with (k':=ks) (v':=vs). inv H1. apply H13.
          assumption. }
        assert (Hforall: ForallT (fun (y : key) (_ : V) => y > rk) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        splay; auto. lia. eapply ForallT_less; eauto.
  - (* t = T (T ll lk lv lr) k v (T rl rk rv rr) *)
    intros. simpl. bdestruct (k0 =? k).
    (* k0 = k *)
    apply H3.
    bdestruct (k0 <? k).
    + (* k0 < k *)
      bdestruct (k0 =? lk).
      (* k0 = lk *)
      splay; auto; try (eapply ForallT_greater; eauto); lia.
      bdestruct (k0 <? lk).
      * (* k0 < lk *)
        destruct (splay ll k0) as [| ls ks vs rs] eqn:HS.
        splay; auto; try (eapply ForallT_greater; eauto); lia.
        assert (HBST: BST ll) by (splay; auto).
        assert (IH: BST (T ls ks vs rs)) by auto.
        assert (Hin1: InBST ks vs ll) by (apply splay_in in HS; auto).
        assert (Himp1: InBST ks vs ll -> InBST ks vs (T ll lk lv lr)).
        { eapply in_bst_lr. splay; auto. }
        assert (Himp2: InBST ks vs (T ll lk lv lr) ->
                       InBST ks  vs(T (T ll lk lv lr) k v (T rl rk rv rr))).
        { eapply in_bst_lr. assumption. }
        assert (Hin2: InBST ks vs ll) by (apply splay_in in HS; auto).
        assert (Hin3: InBST ks vs ll) by (apply splay_in in HS; auto).
        apply Himp1 in Hin2. apply Himp1 in Hin3. apply Himp2 in Hin3.
        clear Himp1. clear Himp2.
        assert (Hlt1: lk < k) by (splay; assumption).
        assert (Hlt2: ks < lk).
        { eapply in_lt_gt with (k':=ks) (v':=vs). inv H3. apply H14.
          assumption. }
        assert (Hforall: ForallT (fun (y : key) (_ : V) => y < lk) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        splay; auto; try (eapply ForallT_greater; eauto); lia.
      * (* k0 > lk *)
        destruct (splay lr k0) as [| ls ks vs rs] eqn:HS.
        splay; auto; try (eapply ForallT_greater; eauto); lia.
        assert (HBST: BST lr) by (splay; auto).
        assert (IH: BST (T ls ks vs rs)) by auto.
        assert (Hin1: InBST ks vs lr) by (apply splay_in in HS; auto).
        assert (Himp1: InBST ks vs lr -> InBST ks vs (T ll lk lv lr)).
        { eapply in_bst_lr. splay; auto. }
        assert (Himp2: InBST ks vs (T ll lk lv lr) ->
                       InBST ks vs (T (T ll lk lv lr) k v (T rl rk rv rr))).
        { eapply in_bst_lr. assumption. }
        assert (Hin2: InBST ks vs lr) by (apply splay_in in HS; auto).
        assert (Hin3: InBST ks vs lr) by (apply splay_in in HS; auto).
        apply Himp1 in Hin2. apply Himp1 in Hin3. apply Himp2 in Hin3.
        clear Himp1. clear Himp2.
        assert (Hlt1: lk < k) by (splay; assumption).
        assert (Hlt2: ks > lk).
        { eapply in_lt_gt with (k':=ks) (v':=vs). inv H3. apply H14.
          assumption. }
        assert (Hlt3: ks < k).
        { eapply in_lt_gt with (k':=ks) (v':=vs). apply H3.
          assumption. }
        assert (Hforall1: ForallT (fun (y : key) (_ : V) => y > lk) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        assert (Hforall2: ForallT (fun (y : key) (_ : V) => y < k) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        splay; auto; try (eapply ForallT_greater; eauto); try lia.
        eapply ForallT_less; eauto.
    + (* k0 > k *)
      bdestruct (k0 =? rk).
      (* k0 = rk *)
      splay; auto; try (eapply ForallT_less; eauto); lia.
      bdestruct (k0 <? rk).
      * (* k0 < rk *)
        destruct (splay rl k0) as [| ls ks vs rs] eqn:HS.
        splay; auto; try (eapply ForallT_less; eauto); lia.
        assert (HBST: BST rl) by (splay; auto).
        assert (IH: BST (T ls ks vs rs)) by auto.
        assert (Hin1: InBST ks vs rl) by (apply splay_in in HS; auto).
        assert (Himp1: InBST ks vs rl -> InBST ks vs (T rl rk rv rr)).
        { eapply in_bst_lr. splay; auto. }
        assert (Himp2: InBST ks vs (T rl rk rv rr) ->
                       InBST ks vs (T (T ll lk lv lr) k v (T rl rk rv rr))).
        { eapply in_bst_lr. assumption. }
        assert (Hin2: InBST ks vs rl) by (apply splay_in in HS; auto).
        assert (Hin3: InBST ks vs rl) by (apply splay_in in HS; auto).
        apply Himp1 in Hin2. apply Himp1 in Hin3. apply Himp2 in Hin3.
        clear Himp1. clear Himp2.
        assert (Hlt1: rk > k) by (splay; assumption).
        assert (Hlt2: ks < rk).
        { eapply in_lt_gt with (k':=ks) (v':=vs). inv H3. apply H15.
          assumption. }
        assert (Hlt3: ks > k).
        { eapply in_lt_gt with (k':=ks) (v':=vs). apply H3.
          assumption. }
        assert (Hforall1: ForallT (fun (y : key) (_ : V) => y < rk) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        assert (Hforall2: ForallT (fun (y : key) (_ : V) => y > k) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        splay; auto; try (eapply ForallT_less; eauto); try lia.
        eapply ForallT_greater; eauto.
      * (* k0 > rk *)
        destruct (splay rr k0) as [| ls ks vs rs] eqn:HS.
        splay; auto; try (eapply ForallT_less; eauto); lia.
        assert (HBST: BST rr) by (splay; auto).
        assert (IH: BST (T ls ks vs rs)) by auto.
        assert (Hin1: InBST ks vs rr) by (apply splay_in in HS; auto).
        assert (Himp1: InBST ks vs rr -> InBST ks vs (T rl rk rv rr)).
        { eapply in_bst_lr. splay; auto. }
        assert (Himp2: InBST ks vs (T rl rk rv rr) ->
                       InBST ks vs (T (T ll lk lv lr) k v (T rl rk rv rr))).
        { eapply in_bst_lr. assumption. }
        assert (Hin2: InBST ks vs rr) by (apply splay_in in HS; auto).
        assert (Hin3: InBST ks vs rr) by (apply splay_in in HS; auto).
        apply Himp1 in Hin2. apply Himp1 in Hin3. apply Himp2 in Hin3.
        clear Himp1. clear Himp2.
        assert (Hlt1: rk > k) by (splay; assumption).
        assert (Hlt2: ks > rk).
        { eapply in_lt_gt with (k':=ks) (v':=vs). inv H3. apply H15.
          assumption. }
        assert (Hforall: ForallT (fun (y : key) (_ : V) => y > rk) (T ls ks vs rs)).
        { rewrite <- HS. eapply ForallT_splay. splay; assumption. }
        splay; auto; try (eapply ForallT_less; eauto); lia.
Qed.

(* Lemma from SearchTree.v *)
Lemma ForallT_ins : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (ins k v t).
Proof.
  induction t as [| l IHl k' v' r IHr]; intros; simpl; auto.
  bdestruct (k =? k').
  - simpl in *. destruct H as [H2 [H3 H4]]. subst. auto.
  - bdestruct (k <? k'); simpl in *; destruct H as [H3 [H4 H5]]; auto.
Qed.

(* Lemma from SearchTree.v *)
Lemma ins_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (ins k v t).
Proof.
  intros. induction H as [| l k' v' r H1 H2 Hl IHl Hr IHr]; simpl.
  - apply BST_T; simpl; auto.
  - bdestruct (k =? k'); subst; auto. bdestruct (k <? k').
    + apply BST_T; simpl; auto. apply ForallT_ins; auto.
    + apply BST_T; simpl; auto. apply ForallT_ins; auto; lia.
Qed.

(* Main theorem. *)
Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insert k v t).
Proof.
  intros. unfold insert. apply (ins_BST V k v) in H.
  apply (splay_BST V k) in H. apply H.
Qed.
(** [] *)

(** * Verification *)

(** Algebraic specification of elements *)

Lemma app_assoc_middle : forall (X : Type) (l1 l2 l3 l4 : list X),
    l1 ++ (l2 ++ l3) ++ l4 = l1 ++ l2 ++ l3 ++ l4.
Proof.
  intros.
  assert (l2 ++ l3 ++ l4 = (l2 ++ l3) ++ l4) by (apply app_assoc).
  rewrite <- H. reflexivity.
Qed.

Theorem elements_splay : forall (V : Type) (t : tree V) (k : key),
    BST t -> elements t = elements (splay t k).
Proof.
  intros V.
  change (forall t' : tree V, (fun t => forall k : key, BST t -> elements t = elements (splay t k)) t').
  apply splay_tree_ind; try reflexivity; intros; simpl; bdall; simpl;
  repeat (match goal with
          | |- (_ ++ _ :: _) ++ _ = _ ++ _ :: _ ++ _ =>
              rewrite <- app_assoc; reflexivity
          | |- _ = elements match splay ?l ?k with E => _ | T _ _ _ _ => _ end =>
              destruct (splay l k) eqn:HS; simpl
          | HS: splay ?l ?k = _,
              IH: forall k : key, BST ?l -> elements ?l = elements (splay ?l k)
                             |- _ =>
              assert (HR: elements l = elements (splay l k)) by
              (splay; apply IH; auto);
              rewrite HS in HR; rewrite HR; simpl;
              repeat (rewrite <- app_assoc); try reflexivity
          | |- _ ++ (_ :: _ ++ _ :: _) ++ _ = _ ++ (_ :: _) ++ _ :: _ ++ _ =>
              rewrite app_comm_cons; apply app_assoc_middle
          end);
    repeat (rewrite <- app_assoc); repeat (rewrite <- app_comm_cons);
    reflexivity.
Qed.

Lemma elements_empty : forall (V : Type),
    @elements V empty_tree = [].
Proof.
  intros. reflexivity.
Qed.

Fixpoint kvs_insert {V : Type} (k : key) (v : V) (kvs : list (key * V)) :=
  match kvs with
  | [] => [(k, v)]
  | (k', v') :: kvs' =>
      if k <? k' then (k, v) :: kvs
      else if k >? k' then (k', v') :: kvs_insert k v kvs'
           else (k, v) :: kvs'
  end.

Lemma kvs_ins_gt : forall (V : Type) (k : key) (v : V) (kvs1 kvs2 : list (key * V)),
    Forall (fun '(k', v') => k' > k) kvs2 ->
    kvs_insert k v (kvs1 ++ kvs2) = (kvs_insert k v kvs1) ++ kvs2.
Proof.
  intros. induction kvs1 as [| [k0 v0] kvs1'].
  - simpl. destruct kvs2 as [| [k0 v0] kvs2'].
    + reflexivity.
    + simpl. inv H. bdall.
  - simpl. bdall. rewrite IHkvs1'. reflexivity.
Qed.

Lemma kvs_ins_lt : forall (V : Type) (k : key) (v : V) (kvs1 kvs2 : list (key * V)),
    Forall (fun '(k', v') => k' < k) kvs1 ->
    kvs_insert k v (kvs1 ++ kvs2) = kvs1 ++ kvs_insert k v kvs2.
Proof.
  intros. induction kvs1 as [| [k0 v0] kvs1'].
  - reflexivity.
  - inv H. simpl. bdall. rewrite IHkvs1'. reflexivity.
    apply H3.
Qed.

Definition curry {V : Type} (f: (key * V) -> Prop) := fun k v => f (k, v).

Lemma elements_forall : forall (V : Type) (t : tree V) (P : (key * V) -> Prop),
    ForallT (curry P) t <-> Forall P (elements t).
Proof.
  intros. induction t; split; intros; simpl; auto; inv IHt1; inv IHt2.
  - inv H. inv H5. apply Forall_app. split; auto.
  - simpl in H. apply Forall_app in H. inv H. inv H5. split; auto.
Qed.

Lemma kvs_ins_elements : forall (V : Type) (t : tree V),
    BST t ->
    forall (k : key) (v : V),
      elements (ins k v t) = kvs_insert k v (elements t).
Proof.
  intros V t H. induction H; intros; simpl.
  - reflexivity.
  - bdall; simpl.
    + subst. rewrite kvs_ins_lt.
      * simpl. bdall; reflexivity.
      * apply elements_forall. apply H.
    + rewrite kvs_ins_gt.
      * rewrite IHBST1. reflexivity.
      * constructor. lia. apply elements_forall. unfold curry. eapply ForallT_imp; eauto.
        simpl. intros. lia.
    + rewrite kvs_ins_lt.
      * simpl. bdall. rewrite IHBST2. reflexivity.
      * apply elements_forall. eapply ForallT_imp; eauto.
        simpl. intros. unfold curry. lia.
Qed.

Lemma kvs_insert_elements : forall (V : Type) (t : tree V),
    BST t ->
    forall (k : key) (v : V),
      elements (insert k v t) = kvs_insert k v (elements t).
Proof.
  intros. unfold insert. rewrite <- elements_splay; try (apply ins_BST; auto).
  apply kvs_ins_elements. assumption.
Qed.

(** Model-based Specification (partial maps) *)

From Coq Require Import Logic.FunctionalExtensionality.

(* from Maps.v *)
Definition total_map (V : Type) : Type := key -> V.

Definition t_empty {V : Type} (v : V) : total_map V :=
  (fun _ => v).

Definition t_update {V : Type}
           (m : total_map V) (k : key) (v : V) : total_map V :=
  fun k' => if k =? k' then v else m k'.

Definition partial_map (V : Type) := total_map (option V).

Definition empty {V : Type} : partial_map V :=
  t_empty None.

Definition update {V : Type}
           (m : partial_map V) (k : key) (v : V) : partial_map V :=
  t_update m k (Some v).

Lemma apply_empty : forall V k, @empty V k = None.
Proof.
  intros. reflexivity.
Qed.

Lemma update_eq : forall V (m : partial_map V) k v,
    (update m k v) k = Some v.
Proof.
  intros. unfold update. unfold t_update.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem update_neq : forall (V : Type) v k1 k2
                       (m : partial_map V),
    k1 <> k2 ->
    (update m k2 v) k1 = m k1.
Proof.
  intros. unfold update. unfold t_update. bdestruct (k2 =? k1).
  lia. reflexivity.
Qed.

Lemma update_shadow : forall V (m : partial_map V) v1 v2 k,
    update (update m k v1) k v2 = update m k v2.
Proof.
  intros. unfold update. unfold t_update.
  apply functional_extensionality. intros. bdall.
Qed.

Theorem update_same : forall V k v (m : partial_map V),
    m k = Some v ->
    update m k v = m.
Proof.
  intros. apply functional_extensionality. intros.
  unfold update. unfold t_update. bdall. subst.
  rewrite H. reflexivity.
Qed.

Theorem update_permute : forall (V : Type) k1 k2 v1 v2
                           (m : partial_map V),
    k1 <> k2 ->
    update (update m k2 v2) k1 v1 = update (update m k1 v1) k2 v2.
Proof.
  intros. unfold update. unfold t_update.
  apply functional_extensionality. intros. bdall.
Qed.
(* end from Maps.v*)

(* from SearchTree.v *)
Fixpoint map_of_list {V : Type} (el : list (key * V)) : partial_map V :=
  match el with
  | [] => empty
  | (k, v) :: el' => update (map_of_list el') k v
  end.

Definition Abs {V : Type} (t : tree V) : partial_map V :=
  map_of_list (elements t).

Definition find {V : Type} (d : V) (k : key) (m : partial_map V) : V :=
  match m k with
  | Some v => v
  | None => d
  end.

Definition map_bound {V : Type} (k : key) (m : partial_map V) : bool :=
  match m k with
  | Some _ => true
  | None => false
  end.
(* end from SearchTree.v *)

Lemma forall_not_in : forall (V : Type) (k : key) (l : list (key * V)),
    Forall (fun '(k', _) => k' <> k) l ->
    map_of_list l k = None.
Proof.
  intros. induction l as [| [x y] l].
  - reflexivity.
  - simpl. inv H. rewrite update_neq; try lia. apply IHl; auto.
Qed.

Lemma lookup_prop_1 : forall (V : Type) (k : key) (l1 l2 : list (key * V)),
    Forall (fun '(k', _) => k' <> k) l1 ->
    map_of_list (l1 ++ l2) k = map_of_list l2 k.
Proof.
  intros. induction l1 as [| [x y] l1].
  - reflexivity.
  - simpl. inv H. rewrite update_neq; try lia.
    apply IHl1; auto.
Qed.

Lemma lookup_prop_2 : forall (V : Type) (k : key) (l1 l2 : list (key * V)),
    Forall (fun '(k', _) => k' <> k) l2 ->
    map_of_list (l1 ++ l2) k = map_of_list l1 k.
Proof.
  intros. induction l1 as [| [x y] l1].
  - simpl. apply forall_not_in; auto.
  - simpl. bdestruct (x =? k).
    + subst. repeat rewrite update_eq. reflexivity.
    + repeat (rewrite update_neq; try lia). apply IHl1.
Qed.

Lemma in_fst : forall (X Y : Type) (lst : list (X * Y)) (x : X) (y : Y),
    In (x, y) lst -> In x (map fst lst).
Proof.
  induction lst; intros; inv H.
  - left. reflexivity.
  - simpl. apply IHlst in H0. right. apply H0.
Qed.

Lemma in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key) (v : V),
    NoDup (map fst el) ->
    In (k,v) el -> (map_of_list el) k = Some v.
Proof.
  induction el; intros; simpl; inv H0.
  - apply update_eq.
  - destruct a as [k0 v0]. simpl in H. bdestruct (k0 =? k).
    + subst. inversion H. exfalso. apply H3. eapply in_fst. apply H1.
    + inv H. rewrite update_neq; auto.
Qed.

Lemma not_in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key),
    ~ In k (map fst el) -> (map_of_list el) k = None.
Proof.
  induction el; intros.
  - reflexivity.
  - destruct a as [k0 v0]. simpl. bdestruct (k0 =? k).
    + subst. exfalso. apply H. constructor. reflexivity.
    + rewrite update_neq; auto. apply IHel. unfold not.
      intros. apply H. simpl. right. apply H1.
Qed.

Lemma empty_relate : forall (V : Type),
    @Abs V empty_tree = empty.
Proof.
  reflexivity.
Qed.

Theorem splay_relate : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    Abs t = Abs (splay t k).
Proof.
  intros. unfold Abs. rewrite <- elements_splay.
  - reflexivity.
  - apply H.
Qed.

Lemma map_bound_or : forall (V : Type) (k : key) (l1 l2 : list (key * V)),
    map_bound k (map_of_list (l1 ++ l2)) = map_bound k (map_of_list l1) || map_bound k (map_of_list l2).
Proof.
  intros. induction l1 as [| [k' v'] l1'].
  - reflexivity.
  - simpl. bdestruct (k =? k').
    + subst. unfold map_bound. repeat rewrite update_eq. reflexivity.
    + unfold map_bound. repeat rewrite update_neq; try lia. apply IHl1'.
Qed.

Lemma bound_neq : forall (V : Type) (k : key) (lst : list (key * V)),
    Forall (fun '(k', _) => k' <> k) lst ->
    map_of_list lst k = None.
Proof.
  intros. induction lst as [| [k0 v0] lst'].
  - reflexivity.
  - simpl. inv H. rewrite update_neq; auto.
Qed.

Ltac forall_impl :=
  try (constructor; try lia); apply elements_forall;
  unfold curry; eapply ForallT_imp; eauto;
  simpl; intros; lia.

Theorem bound_relate : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    map_bound k (Abs t) = bound k t.
Proof.
  intros. induction H.
  - reflexivity.
  - unfold Abs. unfold map_bound. simpl. bdall.
    + subst. rewrite lookup_prop_1; try forall_impl.
      simpl. rewrite update_eq. reflexivity.
    + rewrite lookup_prop_2; try forall_impl.
      rewrite <- IHBST1. reflexivity.
    + rewrite lookup_prop_1; try forall_impl.
      rewrite <- IHBST2. simpl. rewrite update_neq; try lia. reflexivity.
Qed.

Lemma lookup_aux_relate : forall (V : Type) (t : tree V) (d : V) (k : key),
    BST t -> find d k (Abs t) = lookup_aux d k t.
Proof.
  intros. induction H.
  - reflexivity.
  - unfold Abs. unfold find. simpl. bdall.
    + subst. rewrite lookup_prop_1; try forall_impl.
      simpl. rewrite update_eq. reflexivity.
    + rewrite lookup_prop_2; try forall_impl.
      rewrite <- IHBST1. reflexivity.
    + rewrite lookup_prop_1; try forall_impl.
      simpl. rewrite update_neq; try lia.
      rewrite <- IHBST2. reflexivity.
Qed.

Theorem lookup_relate : forall (V : Type) (t : tree V) (d : V) (k : key),
    BST t -> find d k (Abs t) = fst (lookup d k t).
Proof.
  intros. unfold lookup. simpl. apply lookup_aux_relate. apply H.
Qed.

Theorem insert_relate : forall (V : Type) (t : tree V) (k : key) (v : V),
  BST t -> Abs (insert k v t) = update (Abs t) k v.
Proof.
    unfold Abs.
    intros.
    rewrite kvs_insert_elements; auto.
    remember (elements t) as l.
    clear -l.
    induction l as [| [x y] l].
    + reflexivity.
    + simpl. bdall.
      * simpl. rewrite IHl. rewrite update_permute; try lia. reflexivity.
      * assert (Heq: x = k) by lia. subst. rewrite update_shadow.
        simpl. reflexivity.
Qed.

Theorem elements_relate : forall (V : Type) (t : tree V),
  BST t ->
  map_of_list (elements t) = Abs t.
Proof.
  unfold Abs. intros. reflexivity.
Qed.

(** Algebraic specification:
    1. [lookup d k empty_tree = (d, empty_tree)]
    2. [lookup d k (insert k v t) = v]
    3. [lookup d k' (insert k v t) = lookup k' t    if k <> k'] *)

(* useful tactic *)
Ltac exists_tree :=
  match goal with
  | |- exists _ _ _, T ?l _ ?v ?r = T _ _ _ _ => exists l; exists v; exists r; reflexivity
  | |- exists _ _, T ?l _ _ ?r = T _ _ _ _ => exists l; exists r; reflexivity
  end.

(* useful lemma *)
Lemma lookup_aux_splay :
  forall (V :  Type) (t : tree V) (k k0 : key) (d : V),
    BST t ->
    lookup_aux d k t = lookup_aux d k (splay t k0).
Proof.
  intros V.
  change (forall t' : tree V,
             (fun t => forall k' k0 d,
                  BST t -> lookup_aux d k' t = lookup_aux d k' (splay t k0)) t').
  apply splay_tree_ind; intros; splay.
  - (* t = E *)
    reflexivity.
  - (* t = T E k v E *)
    simpl. bdall.
  - (* t = T (T ll lk lv lr) k v E *)
    simpl. bdestruct (k0 =? k). reflexivity.
    bdestruct (k0 <? k).
    + (* k0 < k *)
      bdestruct (k0 =? lk). simpl. bdall.
      bdestruct (k0 <? lk).
      * (* k0 < lk *)
        destruct (splay ll k0) as [| lll llk llv llr] eqn:HS.
        bdall.
        assert (Hin: InBST llk llv ll) by (eapply splay_in; eauto).
        assert (Hlt1: llk < lk) by (apply forall_lt with (t:=ll) (v:=llv); auto).
        assert (Hlt2 : llk < k) by lia.
        bdestruct (k' =? k).
        -- (* k' = k *)
          simpl. bdall.
        -- bdestruct (k' <? k).
           ++ (* k' < k *)
             bdestruct (k' =? lk).
             (* k' = lk *)
             simpl. bdall.
             bdestruct (k' <? lk).
             ** (* k' < lk *)
               specialize H with (k':=k') (k0:=k0) (d:=d).
               rewrite HS in H. rewrite H.
               simpl. bdall. assumption.
             ** (* k' > lk *)
               simpl. bdall.
           ++ (* k' > k *)
             simpl. bdall.
      * (* k0 > lk *)
        destruct (splay lr k0) as [| lrl lrk lrv lrr] eqn:HS.
        bdall.
        assert (Hin: InBST lrk lrv lr) by (eapply splay_in; eauto).
        assert (Hgt1: lrk > lk) by (apply forall_gt with (t:=lr) (v:=lrv); auto).
        assert (Hlt1 : lrk < k) by (apply forall_lt with (t:=lr) (v:=lrv); auto).
        bdestruct (k' =? k).
        -- (* k' = k *)
          simpl. bdall.
        -- bdestruct (k' <? k).
           ++ (* k' < k *)
             bdestruct (k' =? lk).
             (* k' = lk *)
             simpl. bdall.
             bdestruct (k' <? lk).
             ** (* k' < lk *)
               simpl. bdall.
             ** (* k' > lk *)
               specialize H0 with (k':=k') (k0:=k0) (d:=d).
               rewrite HS in H0. rewrite H0.
               simpl. bdall. assumption.
           ++ (* k' > k *)
             simpl. bdall.
    + (* k0 > k *)
      simpl. bdall.
  - (* t = T E k v (T rl rk rv rr) *)
    simpl. bdestruct (k0 =? k). reflexivity.
    bdestruct (k0 <? k).
    + (* k0 < k *)
      simpl. bdall.
    + (* k0 > k *)
      bdestruct (k0 =? rk). simpl. bdall.
      bdestruct (k0 <? rk).
      * (* k0 < rk *)
        destruct (splay rl k0) as [| rll rlk rlv rlr] eqn:HS.
        bdall.
        assert (Hin: InBST rlk rlv rl) by (eapply splay_in; eauto).
        assert (Hlt1: rlk < rk) by (apply forall_lt with (t:=rl) (v:=rlv); auto).
        assert (Hgt1: rlk > k) by (apply forall_gt with (t:=rl) (v:=rlv); auto).
        bdestruct (k' =? k).
        -- (* k' = k *)
          simpl. bdall.
        -- bdestruct (k' <? k).
           ++ (* k' < k *)
             simpl. bdall.
           ++ (* k' > k *)
             bdestruct (k' =? rk).
             simpl. bdall.
             bdestruct (k' <? rk).
             ** (* k' < rk *)
               specialize H with (k':=k') (k0:=k0) (d:=d).
               rewrite HS in H. rewrite H.
               simpl. bdall. assumption.
             ** (* k' > rk *)
               simpl. bdall.
      * (* k0 > rk *)
        destruct (splay rr k0) as [| rrl rrk rrv rrr] eqn:HS.
        bdall.
        assert (Hin: InBST rrk rrv rr) by (eapply splay_in; eauto).
        assert (Hgt1: rrk > rk) by (apply forall_gt with (t:=rr) (v:=rrv); auto).
        assert (Hgt2 : rrk > k) by lia.
        bdestruct (k' =? k).
        -- (* k' = k *)
          simpl. bdall.
        -- bdestruct (k' <? k).
           ++ (* k' < k *)
             simpl. bdall.
           ++ (* k' > k *)
             bdestruct (k' =? rk).
             (* k' = lk *)
             simpl. bdall.
             bdestruct (k' <? rk).
             ** (* k' < rk *)
               simpl. bdall.
             ** (* k' > rk *)
               specialize H0 with (k':=k') (k0:=k0) (d:=d).
               rewrite HS in H0. rewrite H0.
               simpl. bdall. assumption.
  - (* t = T (T ll lk lv lr) k v (T rl rk rv rr) *)
    simpl. bdestruct (k0 =? k). reflexivity.
    bdestruct (k0 <? k).
    + (* k0 < k *)
      bdestruct (k0 =? lk). simpl. bdall.
      bdestruct (k0 <? lk).
      * (* k0 < lk *)
        destruct (splay ll k0) as [| lll llk llv llr] eqn:HS.
        bdall.
        assert (Hin: InBST llk llv ll) by (eapply splay_in; eauto).
        assert (Hlt1: llk < lk) by (apply forall_lt with (t:=ll) (v:=llv); auto).
        assert (Hlt2 : llk < k) by lia.
        bdestruct (k' =? k).
        -- (* k' = k *)
          simpl. bdall.
        -- bdestruct (k' <? k).
           ++ (* k' < k *)
             bdestruct (k' =? lk).
             (* k' = lk *)
             simpl. bdall.
             bdestruct (k' <? lk).
             ** (* k' < lk *)
               specialize H with (k':=k') (k0:=k0) (d:=d).
               rewrite HS in H. rewrite H.
               simpl. bdall. assumption.
             ** (* k' > lk *)
               simpl. bdall.
           ++ (* k' > k *)
             simpl. bdall.
      * (* k0 > lk *)
        destruct (splay lr k0) as [| lrl lrk lrv lrr] eqn:HS.
        bdall.
        assert (Hin: InBST lrk lrv lr) by (eapply splay_in; eauto).
        assert (Hgt2: lrk > lk) by (apply forall_gt with (t:=lr) (v:=lrv); auto).
        assert (Hlt3 : lrk < k) by (apply forall_lt with (t:=lr) (v:=lrv); auto).
        bdestruct (k' =? k).
        -- (* k' = k *)
          simpl. bdall.
        -- bdestruct (k' <? k).
           ++ (* k' < k *)
             bdestruct (k' =? lk).
             (* k' = lk *)
             simpl. bdall.
             bdestruct (k' <? lk).
             ** (* k' < lk *)
               simpl. bdall.
             ** (* k' > lk *)
               specialize H0 with (k':=k') (k0:=k0) (d:=d).
               rewrite HS in H0. rewrite H0.
               simpl. bdall. assumption.
           ++ (* k' > k *)
             simpl. bdall.
    + (* k0 > k *)
      bdestruct (k0 =? rk). simpl. bdall.
      bdestruct (k0 <? rk).
      * (* k0 < rk *)
        destruct (splay rl k0) as [| rll rlk rlv rlr] eqn:HS.
        bdall.
        assert (Hin: InBST rlk rlv rl) by (eapply splay_in; eauto).
        assert (Hlt2: rlk < rk) by (apply forall_lt with (t:=rl) (v:=rlv); auto).
        assert (Hgt2: rlk > k) by (apply forall_gt with (t:=rl) (v:=rlv); auto).
        bdestruct (k' =? k).
        -- (* k' = k *)
          simpl. bdall.
        -- bdestruct (k' <? k).
           ++ (* k' < k *)
             simpl. bdall.
           ++ (* k' > k *)
             bdestruct (k' =? rk).
             simpl. bdall.
             bdestruct (k' <? rk).
             ** (* k' < rk *)
               specialize H1 with (k':=k') (k0:=k0) (d:=d).
               rewrite HS in H1. rewrite H1.
               simpl. bdall. assumption.
             ** (* k' > rk *)
               simpl. bdall.
      * (* k0 > rk *)
        destruct (splay rr k0) as [| rrl rrk rrv rrr] eqn:HS.
        bdall.
        assert (Hin: InBST rrk rrv rr) by (eapply splay_in; eauto).
        assert (Hgt2: rrk > rk) by (apply forall_gt with (t:=rr) (v:=rrv); auto).
        assert (Hgt3 : rrk > k) by lia.
        bdestruct (k' =? k).
        -- (* k' = k *)
          simpl. bdall.
        -- bdestruct (k' <? k).
           ++ (* k' < k *)
             simpl. bdall.
           ++ (* k' > k *)
             bdestruct (k' =? rk).
             (* k' = lk *)
             simpl. bdall.
             bdestruct (k' <? rk).
             ** (* k' < rk *)
               simpl. bdall.
             ** (* k' > rk *)
               specialize H2 with (k':=k') (k0:=k0) (d:=d).
               rewrite HS in H2. rewrite H2.
               simpl. bdall. assumption.
Qed.

(** 1 *)

Theorem lookup_empty : forall (V : Type) (k : key) (d : V),
    lookup d k empty_tree = (d, empty_tree).
Proof. auto. Qed.

(** 2 *)

Lemma ins_splay : forall (V : Type) (t : tree V) (k : key) (v : V),
  BST t -> exists l r, splay (ins k v t) k = T l k v r.
Proof.
  intros V.
  change (forall t' : tree V,
             (fun t => forall k v,
                  BST t -> exists l r, splay (ins k v t) k = T l k v r) t').
  apply splay_tree_ind; intros; simpl;
    [ rewrite Nat.eqb_refl; exists_tree
    | bdall; subst; exists_tree | | | ];
    splay; bdall; subst; try exists_tree;
    match goal with
    | IH: forall k v, BST ?l -> _, HBST: BST ?l |-
                               exists _ _, match splay (ins ?k ?v ?l) ?k with
                                      | E => _
                                      | T _ _ _ _ => _
                                      end = T _ _ _ _ =>
    apply (IH k v) in HBST; destruct HBST as [? [? HBST]];
    rewrite HBST; exists_tree
  end.
Qed.

Lemma lookup_aux_insert_eq : forall (V : Type) (k : key) (d v : V) (t : tree V),
    BST t -> lookup_aux d k (insert k v t) = v.
Proof.
  intros. unfold insert.
  assert (H1: exists l r, splay (ins k v t) k = T l k v r) by
    (apply ins_splay; auto).
  destruct H1 as [l [r H1]]. rewrite H1. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_aux_ins_eq : forall (V : Type) (k : key) (d v : V) (t : tree V),
    BST t -> lookup_aux d k (ins k v t) = v.
Proof.
  intros. induction H.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. bdall.
Qed.

(* this proof uses lookup_aux_splay and lookup_aux_ins_eq instead of ins_splay *)
Lemma lookup_aux_insert_eq_alt : forall (V : Type) (k : key) (d v : V) (t : tree V),
    BST t -> lookup_aux d k (insert k v t) = v.
Proof.
  intros. unfold insert. rewrite <- lookup_aux_splay.
  apply lookup_aux_ins_eq; auto.
  apply ins_BST; auto.
Qed.

Theorem lookup_insert_eq : forall (V : Type) (k : key) (d v : V) (t : tree V),
    BST t -> fst (lookup d k (insert k v t)) = v.
Proof.
  intros. unfold lookup. simpl.
  apply lookup_aux_insert_eq. assumption.
Qed.

(** 3 *)

Lemma lookup_aux_ins_neq :
  forall (V : Type) (t : tree V) (k k' : key) (d v : V),
    BST t ->
    k <> k' ->
    lookup_aux d k' (ins k v t) = lookup_aux d k' t.
Proof.
  induction t; intros; simpl; bdall; splay; auto.
Qed.

Lemma lookup_aux_insert_neq :
  forall (V : Type) (t : tree V) (k k' : key) (d v : V),
    BST t ->
    k <> k' ->
    lookup_aux d k' (insert k v t) = lookup_aux d k' t.
Proof.
  intros. unfold insert. rewrite <- lookup_aux_splay.
  apply lookup_aux_ins_neq; auto.
  apply ins_BST; auto.
Qed.

Theorem lookup_insert_neq :
  forall (V : Type) (t : tree V) (k k' : key) (d v : V),
    BST t ->
    k <> k' ->
    fst (lookup d k' (insert k v t)) = fst (lookup d k' t).
Proof.
  intros. unfold lookup. simpl. apply lookup_aux_insert_neq; auto.
Qed.

(** [insert_in] proof; not used anywhere *)
Lemma splay_in_val : forall (V : Type) (t : tree V) (k : key) (v : V),
    InBST k v t -> exists l r, splay t k = T l k v r.
Proof.
  intros V.
  change (forall t' : tree V, (fun t => forall k v, InBST k v t ->
                                     exists l r, splay t k = T l k v r) t').
  apply splay_tree_ind; intros;
    [ inv H
    | inv H; try inv H7; simpl; rewrite Nat.eqb_refl; exists_tree
    | | | ];
    try (inv H1; simpl;
         try (rewrite Nat.eqb_refl; exists_tree); inv H9;
         try (try (apply H in H10); try (apply H0 in H10);
              destruct H10 as [l [r H10]];
              bdall; rewrite H10; exists_tree);
         bdall; exists_tree).
  inv H3; simpl; try (rewrite Nat.eqb_refl; exists_tree); inv H11;
    try (try (apply H in H12); try (apply H0 in H12);
         try (apply H1 in H12); try (apply H2 in H12);
         destruct H12 as [l [r H12]];
         bdall; rewrite H12; exists_tree);
    bdall; try exists_tree.
Qed.

Lemma ins_in : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> InBST k v (ins k v t).
Proof.
  intros. induction H.
  - simpl. apply in_root.
  - simpl. bdall.
    + rewrite H3. apply in_root.
    + apply in_right; auto; lia.
Qed.

Lemma insert_in : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> InBST k v (insert k v t).
Proof.
  intros. assert (H1: InBST k v (ins k v t)) by (apply ins_in; auto).
  unfold insert.
  assert (H2: exists l r, splay (ins k v t) k = T l k v r)
    by (apply splay_in_val; auto).
  destruct H2 as [l [r H2]]. rewrite H2. apply in_root.
Qed.
