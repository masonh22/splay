import Std.Data.AssocList

import Splay.STree
import Splay.SplayBST
import Splay.Assoc
---- TODO section the bst invariant, proving insert_BST ----

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

---- association lists
theorem elements_splay {α : Type} (t : STree α) (k : Nat) (hbst : BST t)
  : t.elements = (t.splay k).elements := by
  apply elements_splay_impl t k hbst

theorem bound_relate {α : Type} (t : STree α) (k : Nat) (hbst : BST t)
  : t.bound k = bound_assoc t.abs k := by
  apply bound_relate_impl t k hbst

theorem lookup_relate {α : Type} (t : STree α) (k : Nat) (hbst : BST t)
  : (t.lookup? k).1 = lookup_assoc t.abs k := by
  apply lookup_relate_impl t k hbst

theorem insert_relate {α : Type} (t : STree α) (k : Nat) (v : α) (hbst : BST t)
  : (t.insert k v).abs = insert_assoc t.abs k v := by
  apply insert_relate_impl t k v hbst

------- TODO section doc; algebraic spec -------

