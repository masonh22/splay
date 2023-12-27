macro "have_eq " lhs:term:max rhs:term:max : tactic =>
  `(tactic|
    (have h : $lhs = $rhs :=
       -- TODO: replace with linarith
       by simp_arith at *; apply Nat.le_antisymm <;> assumption
     try subst $lhs))

macro "by_cases' " e:term:max h:Lean.binderIdent : tactic =>
  `(tactic| by_cases $e <;> rename_i $h <;> simp [*])
