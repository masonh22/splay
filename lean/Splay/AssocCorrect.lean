-- proving that the association lists are correct using a basic map
import Mathlib.Tactic.Linarith

import Splay.Assoc
import Splay.Tactics

def Map (α : Type) := Nat -> Option α

@[simp]
def insert_map {α : Type} (m : Map α) (k : Nat) (v : α) :=
  fun k' => if k' = k then some v else m k'

@[simp]
def union_map {α : Type} (m1 m2 : Map α) :=
  fun k' =>
    match m1 k' with
    | none => m2 k'
    | x => x

@[simp]
def bound_map {α : Type} (m : Map α) (k : Nat) :=
  match m k with
  | none => false
  | some _ => true

@[simp]
def lookup_map {α : Type} (m : Map α) (k : Nat) := m k

@[simp]
def empty_map {α : Type} : Map α := fun _ => none

@[simp]
def map_of_list {α : Type} (l : Assoc α) : Map α :=
  match l with
  | .nil => empty_map
  | .cons (k, v) tl => insert_map (map_of_list tl) k v

@[simp]
def abs_assoc {α : Type} (l : Assoc α) : Map α := map_of_list l
-- this def doesn't work because of universes?
-- @[simp]
-- def abs_assoc {α : Type u} (l : Assoc α) :=
--   l.foldl (fun m (k, v) => fun k' => if k' = k then some v else m k') (fun _ => none)

-- TODO assoc α doesn't work with app (++)
theorem abs_assoc_app {α : Type} (l1 l2 : List (Nat × α)) :
  abs_assoc (l1 ++ l2) = union_map (abs_assoc l1) (abs_assoc l2) := by
  funext k
  induction l1 with
  | nil => simp
  | cons elt l1 ihl1 =>
    cases elt
    rename_i k' v'
    simp
    by_cases' (k = k') heq
    unfold abs_assoc at ihl1
    rw [ihl1]
    rfl

theorem bound_relate {α : Type} (l : Assoc α) (k : Nat) :
  bound_map (abs_assoc l) k = bound_assoc l k := by
  induction l with
  | nil => simp
  | cons elt l ihl =>
    cases elt
    rename_i k' v'
    simp
    by_cases' (k = k') heq
    rw [<- ihl]
    have heq2 : ¬k' = k := by -- TODO dumb... is there a tactic that can handle this?
      intro hasdf
      apply heq
      rw [hasdf]
    simp [*]

theorem lookup_relate {α : Type} (l : Assoc α) (k : Nat) :
  lookup_map (abs_assoc l) k = lookup_assoc l k := by
  induction l with
  | nil => simp
  | cons elt l ihl =>
    cases elt
    rename_i k' v'
    simp
    by_cases' (k = k') heq
    rw [<- ihl]
    have heq2 : ¬k' = k := by -- TODO dumb... is there a tactic that can handle this?
      intro hasdf
      apply heq
      rw [hasdf]
    simp [*]

theorem insert_relate {α : Type} (l : Assoc α) (k : Nat) (v : α) :
  insert_map (abs_assoc l) k v = abs_assoc (insert_assoc l k v) := by
  induction l with
  | nil => simp
  | cons elt l ihl =>
    funext k0
    cases elt
    rename_i k' v'
    simp
    by_cases' (k < k') hlt
    by_cases' (k > k') hgt
    case pos =>
      by_cases' (k0 = k) heq0
      case pos =>
        have hneq : k ≠ k' := by linarith
        simp [*]
        unfold abs_assoc at ihl
        rw [<-ihl]
        simp [*]
      case neg =>
        by_cases' (k0 = k') heq'
        unfold abs_assoc at ihl
        rw [<-ihl]
        simp [*]
    case neg =>
      have heq' : k = k' := by linarith
      by_cases' (k0 = k) heq0
      subst heq'
      simp [*]

-- algebraic specification
-- 1. ∀ k, lookup_assoc empty_assoc k = none
-- 2. ∀ k v l, lookup_assoc (insert_assoc l k v) k = some v
-- 3. ∀ k k' v l, k' ≠ k -> lookup_assoc (insert_assoc l k v) k' = lookup_assoc l k'

-- TODO how to apply the time to empty_assoc even though it's implicit?
-- theorem lookup_assoc_empty {α : Type} (k : Nat) : lookup_assoc empty_assoc k = none := by simp

theorem lookup_assoc_eq (α : Type) (k : Nat) (v : α) (l : Assoc α) :
  lookup_assoc (insert_assoc l k v) k = some v := by
  induction l with
  | nil => simp
  | cons elt l ihl =>
    cases elt
    rename_i k' v'
    simp
    by_cases' (k < k') hlt
    by_cases (k > k')
    case pos =>
      rename_i hgt
      simp [hgt]
      have hne : k' ≠ k := by linarith
      simp [*]
    case neg =>
      have heq : k' = k := by linarith
      subst heq
      simp

theorem lookup_assoc_neq {α : Type} (k k' : Nat) (v : α) (l : Assoc α) :
  k ≠ k' ->
  lookup_assoc (insert_assoc l k v) k' = lookup_assoc l k' := by
  intro h
  induction l with
  | nil => simp [h]
  | cons elt l ihl =>
    cases elt
    rename_i k0 v0
    simp
    by_cases' (k < k0) hlt
    by_cases' (k > k0) hgt
    have heq : k = k0 := by linarith
    subst heq
    simp [*]
