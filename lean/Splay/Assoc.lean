import Mathlib.Tactic.Linarith

import Splay.Tactics
import Splay.STree
import Splay.BST

@[simp]
def STree.abs {α : Type} (t : STree α) : List (Nat × α) := t.elements

@[simp]
def bound_assoc {α : Type} (l : List (Nat × α)) (k : Nat) :=
  match l with
  | .nil => false
  | .cons (k', _) tl => k' = k || bound_assoc tl k

@[simp]
def lookup_assoc {α : Type} (l : List (Nat × α)) (k : Nat) :=
  match l with
  | .nil => none
  | .cons (k', v) tl =>
    if k' = k then some v else lookup_assoc tl k

-- sorted insert
@[simp]
def insert_assoc {α : Type} (l : List (Nat × α)) (k : Nat) (v : α) :=
  match l with
  | .nil => [(k, v)]
  | .cons (k', v') tl =>
    if k < k' then (k, v) :: l
    else if k > k' then (k', v') :: insert_assoc tl k v
    else (k, v) :: tl

-- @[simp]
-- def do_shit {α : Type} (nil_case : Nat -> α -> β) (gt_case : Nat -> α -> Nat -> α -> List (Nat × α) -> β) (lt_case : Nat -> α -> List (Nat × α) -> List (Nat × α) -> β) (eq_case : Nat -> α -> List (Nat × α) -> β) (l : List (Nat × α)) (k : Nat) (v : α) :=
--   match l with
--   | .nil => nil_case k v
--   | .cons (k', v') tl =>
--     if k < k' then lt_case k v l tl
--     else if k > k' then gt_case k v k' v' tl
--     else eq_case k v tl

-- def bound_shit (l : List (Nat × α)) (k : Nat) (v : α) :=
--   do_shit (fun _ _ => false) (fun _ _ _ _ tl => bound_shit tl k v) (fun _ _ _ tl => bound_shit tl k v) (fun _ _ _ => true) l k v

theorem elements_splay_impl {α : Type} (t : STree α) (key : Nat) (hbst : BST t)
  : t.elements = (t.splay key).elements := by
  induction t using STree.inductionOn with
  | base => simp
  | ind_te k v => simp
  | ind_tl k v ll lk lv lr ihll ihlr =>
    simp
    by_cases' (key = k) heq
    by_cases' (key < k) hlt
    by_cases' (key = lk) heqlk
    by_cases' (key < lk) hltlk
    case pos =>
      cases hdes : ll.splay key with
      | leaf => simp
      | node lll llk llv llr =>
        rw [hdes] at ihll
        simp at *
        rw [ihll]
        simp
        cases hbst
        rename_i hbstl _ _ _
        cases hbstl
        assumption
    case neg =>
      cases hdes : lr.splay key with
      | leaf => simp
      | node lrl lrk lrv lrr =>
        rw [hdes] at ihlr
        simp at *
        rw [ihlr]
        simp
        cases hbst
        rename_i hbstl _ _ _
        cases hbstl
        assumption
  | ind_tr k v rl rk rv rr ihrl ihrr =>
    simp
    by_cases' (key = k) heq
    by_cases' (key < k) hlt
    by_cases' (key = rk) heqrk
    by_cases' (key < rk) hltrk
    case pos =>
      cases hdes : rl.splay key with
      | leaf => simp
      | node rll rlk rlv rlr =>
        rw [hdes] at ihrl
        simp at *
        rw [ihrl]
        simp
        cases hbst
        rename_i hbstr _
        cases hbstr
        assumption
    case neg =>
      cases hdes : rr.splay key with
      | leaf => simp
      | node rrl rrk rrv rrr =>
        rw [hdes] at ihrr
        simp at *
        rw [ihrr]
        cases hbst
        rename_i hbstr _
        cases hbstr
        assumption
  | ind k v ll lk lv lr rl rk rv rr ihll ihlr ihrl ihrr =>
    simp
    by_cases' (key = k) heq
    by_cases' (key < k) hlt
    case pos =>
      by_cases' (key = lk) heqlk
      by_cases' (key < lk) hltlk
      case pos =>
        cases hdes : ll.splay key with
        | leaf => simp
        | node lll llk llv llr =>
          rw [hdes] at ihll
          simp at *
          rw [ihll]
          simp
          cases hbst
          rename_i hbstl _ _ _
          cases hbstl
          assumption
      case neg =>
        cases hdes : lr.splay key with
        | leaf => simp
        | node lrl lrk lrv lrr =>
          rw [hdes] at ihlr
          simp at *
          rw [ihlr]
          simp
          cases hbst
          rename_i hbstl _ _ _
          cases hbstl
          assumption
    case neg =>
      by_cases' (key = rk) heqrk
      by_cases' (key < rk) hltrk
      case pos =>
        cases hdes : rl.splay key with
        | leaf => simp
        | node rll rlk rlv rlr =>
          rw [hdes] at ihrl
          simp at *
          rw [ihrl]
          simp
          cases hbst
          rename_i hbstr _
          cases hbstr
          assumption
      case neg =>
        cases hdes : rr.splay key with
        | leaf => simp
        | node rrl rrk rrv rrr =>
          rw [hdes] at ihrr
          simp at *
          rw [ihrr]
          cases hbst
          rename_i hbstr _
          cases hbstr
          assumption

---- helpers for the rest
theorem fuck2 {α : Type} {b1 : Prop} {b2 : Prop} [Decidable b1] [Decidable b2] (a : α) (l1 l2 l3 : List α)
  : a :: (if b1 then l1 else if b2 then l2 else l3) = if b1 then a :: l1 else if b2 then a :: l2 else a :: l3 := by
  by_cases b1 <;> simp [*]
  by_cases b2 <;> simp [*]

theorem bound_assoc_not (l : List (Nat × α)) (k : Nat)
  : Forall (fun x => x.1 ≠ k) l -> bound_assoc l k = false := by
  induction l with
  | nil => simp
  | cons e t ih =>
    intro h
    cases h
    simp [*]

theorem bound_assoc_split {α : Type} (k k' : Nat) (v' : α) (l1 l2 : List (Nat × α))
  : Forall (fun (k0, _) => k0 < k') l1 ->
    Forall (fun (k0, _) => k0 > k') l2 ->
    bound_assoc (l1 ++ (k', v') :: l2) k =
    if k < k' then
      bound_assoc l1 k
    else if k > k' then
      bound_assoc l2 k
    else true := by
  induction l1 with
  | nil =>
    simp
    intros _ h2
    by_cases' (k < k') hlt
    apply And.intro
    linarith
    apply bound_assoc_not
    apply Forall_imp
    apply h2
    intros
    linarith
    by_cases' (k' < k) hgt
    have hneq : k' ≠ k := by linarith
    simp [*]
    have heq : k' = k := by linarith
    simp [*]
  | cons e l1 ih =>
    simp at *
    intros h1 h2
    cases h1
    rename_i hlte h1
    by_cases' (k < k') hlt
    by_cases' (k' < k) hgt
    have hneq : e.1 ≠ k := by linarith
    simp [*]

theorem lookup_assoc_not (l : List (Nat × α)) (k : Nat)
  : Forall (fun x => x.1 ≠ k) l -> lookup_assoc l k = none := by
  induction l with
  | nil => simp
  | cons e t ih =>
    intro h
    cases h
    simp [*]

-- TODO combine these three, terrible
theorem lookup_assoc_split (k k' : Nat) (v' : α) (l1 l2 : List (Nat × α))
  : Forall (fun (k0, _) => k0 < k') l1 ->
    Forall (fun (k0, _)     => k0 > k') l2 ->
    lookup_assoc (l1 ++ (k', v') :: l2) k =
    if k < k' then
      lookup_assoc l1 k
    else if k > k' then
      lookup_assoc l2 k
    else some v' := by
  induction l1 with
  | nil =>
    simp
    intro _ h2
    by_cases' (k < k') hlt
    have hneq : k' ≠ k := by linarith
    simp [*]
    apply lookup_assoc_not
    apply Forall_imp
    apply h2
    intros
    linarith
    by_cases' (k' < k) hgt
    have hneq : k' ≠ k := by linarith
    intros
    contradiction
    have heq : k' = k := by linarith
    simp [*]
  | cons e l1 ih =>
    simp at *
    intros h1 h2
    cases h1
    rename_i hlte h1
    by_cases' (k < k') hlt
    by_cases' (k' < k) hgt
    intros
    exfalso
    linarith
    intros
    exfalso
    linarith

-- TODO try to make this more generic so that it applies to the other guys?
theorem insert_assoc_split {α : Type} (k k' : Nat) (v v' : α) (l1 l2 : List (Nat × α))
  : Forall (fun (k0, _) => k0 < k') l1 ->
    Forall (fun (k0, _)     => k0 > k') l2 ->
    insert_assoc (l1 ++ (k', v') :: l2) k v =
    if k < k' then
      (insert_assoc l1 k v) ++ (k', v') :: l2
    else if k > k' then
      l1 ++ (k', v') :: insert_assoc l2 k v
    else
      l1 ++ (k, v) :: l2 := by
  induction l1 with
  | nil => simp
  | cons h l1 ihl =>
    intros hl hr
    cases h
    rename_i kl vl
    cases hl
    rename_i hlt1 hfl
    simp at *
    by_cases' (k < kl) hlt
    case pos =>
      have hlt2 : k < k' := by linarith
      simp [*]
    case neg =>
      rw [<-ihl]
      simp [*]
      by_cases' (kl < k) hgt
      rw [<-fuck2]
      have heq : kl = k := by linarith
      subst heq
      simp [*]
      apply hfl
      apply hr

theorem bound'_relate {α : Type} (t : STree α) (key : Nat) (hbst : BST t)
  : t.bound' key = bound_assoc t.abs key := by
  induction hbst with
  | leaf => simp
  | node l k v r hfl hfr hbstl hbstr ihl ihr =>
    simp
    have hfal : Forall (fun (k', _) ↦ k' < k) l.elements := by
      rw [Forall_relate] at hfl
      apply hfl
    have hfar : Forall (fun (k', _) ↦ k' > k) r.elements := by
      rw [Forall_relate] at hfr
      apply hfr
    rw [bound_assoc_split] <;> try assumption
    by_cases' (key = k) heq
    by_cases' (key < k) hlt
    have hgt : k < key := by apply obvious_arith <;> assumption
    simp [*]

theorem bound_relate_impl {α : Type} (t : STree α) (k : Nat) (hbst : BST t)
  : t.bound k = bound_assoc t.abs k := by
  rw [splay_bound_equiv]
  apply bound'_relate t k hbst

theorem lookup'_relate {α : Type} (t : STree α) (key : Nat) (hbst : BST t)
  : (t.lookup' key).1 = lookup_assoc t.abs key := by
  induction hbst with
  | leaf => simp
  | node l k v r hfl hfr hbstl hbstr ihl ihr =>
    simp
    have hfal : Forall (fun (k', _) ↦ k' < k) l.elements := by
      rw [Forall_relate] at hfl
      apply hfl
    have hfar : Forall (fun (k', _) ↦ k' > k) r.elements := by
      rw [Forall_relate] at hfr
      apply hfr
    rw [lookup_assoc_split] <;> try assumption
    by_cases' (key = k) heq
    by_cases' (key < k) hlt
    case pos =>
      apply ihl
    case neg =>
      have hgt : k < key := by apply obvious_arith <;> assumption
      simp [*]
      apply ihr

theorem lookup_relate_impl {α : Type} (t : STree α) (k : Nat) (hbst : BST t)
  : (t.lookup? k).1 = lookup_assoc t.abs k := by
  rw [splay_lookup_equiv]
  apply lookup'_relate t k hbst

theorem ins_relate {α : Type} (t : STree α) (key : Nat) (val : α) (hbst : BST t)
  : (t.ins key val).abs = insert_assoc t.abs key val := by
  induction hbst with
  | leaf => simp
  | node l k v r hfl hfr hbstl hbstr ihl ihr =>
    simp
    have hfal : Forall (fun (k', _) ↦ k' < k) l.elements := by
      rw [Forall_relate] at hfl
      apply hfl
    have hfar : Forall (fun (k', _) ↦ k' > k) r.elements := by
      rw [Forall_relate] at hfr
      apply hfr
    rw [insert_assoc_split] <;> try assumption
    by_cases' (key = k) heq
    by_cases' (key < k) hlt
    case pos =>
      apply ihl
    case neg =>
      have hgt : key > k := by apply obvious_arith <;> assumption
      simp [*]
      apply ihr

theorem insert_relate_impl {α : Type} (t : STree α) (k : Nat) (v : α) (hbst : BST t)
  : (t.insert k v).abs = insert_assoc t.abs k v := by
  simp
  rw [<-elements_splay_impl]
  . apply ins_relate t k v hbst
  . apply ins_BST t k v hbst
