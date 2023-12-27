import Splay.SplayBST
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

------- TODO section doc; algebraic spec -------

