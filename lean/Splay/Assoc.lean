abbrev Assoc (α : Type) := List (Nat × α)

def empty_assoc {α : Type} : Assoc α := []

-- sorted insert
@[simp]
def insert_assoc {α : Type} (l : Assoc α) (k : Nat) (v : α) :=
  match l with
  | .nil => [(k, v)]
  | .cons (k', v') tl =>
    if k < k' then (k, v) :: l
    else if k > k' then (k', v') :: insert_assoc tl k v
    else (k, v) :: tl

@[simp]
def bound_assoc {α : Type} (l : Assoc α) (k : Nat) :=
  match l with
  | .nil => false
  | .cons (k', _) tl => k' = k || bound_assoc tl k

@[simp]
def lookup_assoc {α : Type} (l : Assoc α) (k : Nat) :=
  match l with
  | .nil => none
  | .cons (k', v) tl =>
    if k' = k then some v else lookup_assoc tl k
