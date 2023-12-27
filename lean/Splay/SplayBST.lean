import Mathlib.Tactic.Linarith

import Splay.Tactics
import Splay.STree
import Splay.BST

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
          . cases hdes : ll.splay key with
            | leaf =>
              simp
              repeat constructor
              all_goals try assumption
              constructor <;> assumption
            | node lll llk llv llr =>
              have hfsll : ForallTree p (ll.splay key) := by apply ihll; apply hfll
              rw [hdes] at hfsll
              cases hfsll
              rename_i hflll hllk hfllr
              simp
              repeat constructor
              all_goals (try assumption)
              repeat constructor
              all_goals (try assumption)
              constructor <;> assumption
          . cases hdes : lr.splay key with
            | leaf =>
              simp
              repeat constructor
              all_goals try assumption
              constructor <;> assumption
            | node lrl lrk lrv lrr =>
              have hfslr : ForallTree p (lr.splay key) := by apply ihlr; apply hflr
              rw [hdes] at hfslr
              cases hfslr
              rename_i hflrl hlrk hflrr
              simp
              repeat constructor
              all_goals (try assumption)
              constructor
              all_goals assumption
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
          . cases hdes : rl.splay key with
            | leaf =>
              simp
              constructor
              constructor
              constructor
              all_goals assumption
            | node rll rlk rlv rlr =>
              have hfsrl : ForallTree p (rl.splay key) := by apply ihrl; apply hfrl
              rw [hdes] at hfsrl
              cases hfsrl
              rename_i hfrll hrlk hfrlr
              simp
              constructor
              constructor
              constructor
              apply hp
              apply hfrll
              apply hrlk
              constructor <;> assumption
          . cases hdes : rr.splay key with
            | leaf =>
              simp
              constructor
              constructor
              constructor
              all_goals assumption
            | node rrl rrk rrv rrr =>
              have hfsrr : ForallTree p (rr.splay key) := by apply ihrr; apply hfrr
              rw [hdes] at hfsrr
              cases hfsrr
              rename_i hfrrl hrrk hfrrr
              simp
              repeat constructor
              all_goals assumption
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
            . cases hdes : ll.splay key with
              | leaf =>
                simp
                repeat constructor
                all_goals try assumption
                constructor <;> assumption
              | node lll llk llv llr =>
                have hfsll : ForallTree p (ll.splay key) := by apply ihll; apply hfll
                rw [hdes] at hfsll
                cases hfsll
                rename_i hflll hllk hfllr
                simp
                repeat constructor
                all_goals (try assumption)
                repeat constructor
                all_goals (try assumption)
                constructor <;> assumption
            . cases hdes : lr.splay key with
              | leaf =>
                simp
                repeat constructor
                all_goals try assumption
                constructor <;> assumption
              | node lrl lrk lrv lrr =>
                have hfslr : ForallTree p (lr.splay key) := by apply ihlr; apply hflr
                rw [hdes] at hfslr
                cases hfslr
                rename_i hflrl hlrk hflrr
                simp
                repeat constructor
                all_goals (try assumption)
                constructor
                all_goals assumption
      . cases hfr with
        | node _ _ _ _ hfrl hpr hfrr =>
          by_cases' (key = rk) heqrk
          . constructor <;> try assumption
            constructor <;> assumption
          . cases hfl
            rename_i hfrll hrlk hfrlr
            by_cases' (key < rk) hltrk
            . cases hdes : rl.splay key with
              | leaf =>
                simp
                repeat constructor
                all_goals try assumption
              | node rll rlk rlv rlr =>
                have hfsrl : ForallTree p (rl.splay key) := by apply ihrl; apply hfrl
                rw [hdes] at hfsrl
                cases hfsrl
                simp
                repeat constructor
                all_goals try assumption
                constructor <;> assumption
            . cases hdes : rr.splay key with
              | leaf =>
                simp
                constructor
                constructor
                constructor
                all_goals assumption
              | node rrl rrk rrv rrr =>
                have hfsrr : ForallTree p (rr.splay key) := by apply ihrr; apply hfrr
                rw [hdes] at hfsrr
                cases hfsrr
                rename_i hfrrl hrrk hfrrr
                simp
                repeat constructor
                all_goals assumption

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
        cases hfl
        rename_i hfll2 hlk hflr2
        by_cases' (key = lk) hlkeq
        case pos =>
          rw [<-splayBST_equiv]
          repeat constructor
          all_goals repeat constructor
          all_goals try simp [*]
          all_goals repeat constructor
          all_goals (rw [splayBST_equiv]; assumption)
        case neg =>
          by_cases' (key < lk) hlklt
          case pos =>
            cases hdes : ll.splay key with
            | leaf =>
              simp
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals (rw [splayBST_equiv]; assumption)
            | node lll llk llv llr =>
              simp
              have hfsll : ForallTree (fun k' _ ↦ k' < lk) (ll.splay key) := by
                apply splay_Forall; assumption
              have hfsll2 : ForallTree (fun k' _ ↦ k' < k) (ll.splay key) := by
                apply splay_Forall; assumption
              rw [hdes] at hfsll
              rw [hdes] at hfsll2
              cases hfsll
              rename_i hfslll hllk hfsllr
              cases hfsll2
              rename_i hfslll2 hllk2 hfsllr2
              rw [hdes] at ihll
              rw [<-splayBST_equiv] at ihll
              cases ihll
              rename_i ihlll ihflll ihllr ihfllr
              rw [<-splayBST_equiv]
              repeat constructor <;> repeat constructor
              all_goals repeat constructor
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_greater; apply hflr; assumption
              rw [splayBST_equiv]; assumption
          case neg =>
            cases hdes : lr.splay key with -- TODO NOTE THIS: equivalent of destruct eqn:hdes
            | leaf =>
              simp
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals (rw [splayBST_equiv]; assumption)
            | node lrl lrk lrv lrr =>
              simp
              have hfslr : ForallTree (fun k' _ ↦ k' > lk) (lr.splay key) := by
                apply splay_Forall; assumption
              have hfslr2 : ForallTree (fun k' _ ↦ k' < k) (lr.splay key) := by
                apply splay_Forall; assumption
              rw [hdes] at hfslr
              rw [hdes] at hfslr2
              cases hfslr
              rename_i hfslrl hlrk hfslrr
              cases hfslr2
              rename_i hfslrl2 hlrk2 hfslrr2
              rw [hdes] at ihlr
              rw [<-splayBST_equiv] at ihlr
              cases ihlr
              rename_i ihlrl ihflrl ihlrr ihflrr
              rw [<-splayBST_equiv]
              repeat constructor <;> repeat constructor
              all_goals repeat constructor
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_less; apply hfll; assumption
              rw [splayBST_equiv]; assumption
      case neg =>
        apply splayBST.node_l <;> simp [*]
  | node_r k v rl rk rv rr hfrl hfrr hfr hsbstrl hsbstrr ihrl ihrr =>
    simp
    by_cases' (key = k) heq
    case pos =>
      apply splayBST.node_r <;> simp [*]
    case neg =>
      by_cases' (key < k) hlt
      case pos =>
        apply splayBST.node_r <;> simp [*]
      case neg =>
        cases hfr
        rename_i hfrl2 hfrk hfrr2
        by_cases' (key = rk) heqrk
        case pos =>
          rw [<-splayBST_equiv]
          repeat constructor
          all_goals repeat constructor
          all_goals try simp [*]
          all_goals repeat constructor
          all_goals (rw [splayBST_equiv]; assumption)
        case neg =>
          by_cases' (key < rk) hltrk
          case pos =>
            cases hdes : rl.splay key with
            | leaf =>
              simp
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals (rw [splayBST_equiv]; assumption)
            | node rll rlk rlv rlr =>
              simp
              have hfsrl : ForallTree (fun k' _ ↦ k' < rk) (rl.splay key) := by
                apply splay_Forall; assumption
              have hfsrl2 : ForallTree (fun k' _ ↦ k' > k) (rl.splay key) := by
                apply splay_Forall; assumption
              rw [hdes] at hfsrl
              rw [hdes] at hfsrl2
              cases hfsrl
              rename_i hfsrll hrlk hfsrlr
              cases hfsrl2
              rename_i hfsrll2 hrlk2 hfsrlr2
              rw [hdes] at ihrl
              rw [<-splayBST_equiv] at ihrl
              cases ihrl
              rename_i ihrll ihfrll ihrlr ihfrlr
              rw [<-splayBST_equiv]
              repeat constructor <;> repeat constructor
              all_goals repeat constructor
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_greater; apply hfrr; assumption
              rw [splayBST_equiv]; assumption
          case neg =>
            cases hdes : rr.splay key with
            | leaf =>
              simp
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals (rw [splayBST_equiv]; assumption)
            | node rrl rrk rrv rrr =>
              simp
              have hfsrr : ForallTree (fun k' _ ↦ k' > rk) (rr.splay key) := by
                apply splay_Forall; assumption
              have hfsrr2 : ForallTree (fun k' _ ↦ k' > k) (rr.splay key) := by
                apply splay_Forall; assumption
              rw [hdes] at hfsrr
              rw [hdes] at hfsrr2
              cases hfsrr
              rename_i hfsrrl hrrk hfsrrr
              cases hfsrr2
              rename_i hfsrrl2 hrrk2 hfsrrr2
              rw [hdes] at ihrr
              rw [<-splayBST_equiv] at ihrr
              cases ihrr
              rename_i ihrrl ihfrrl ihrrr ihfrrr
              rw [<-splayBST_equiv]
              repeat constructor <;> repeat constructor
              all_goals repeat constructor
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_less; apply hfrl; assumption
              rw [splayBST_equiv]; assumption
  | node_rl k v ll lk lv lr rl rk rv rr hfll hflr hfrl hfrr hfl hfr hsbstll hsbstlr hsbstrl hsbstrr ihll ihlr ihrl ihrr =>
    simp
    by_cases' (key = k) heq
    case pos =>
      apply splayBST.node_rl <;> simp [*]
    case neg =>
      cases hfr
      rename_i hfrl2 hfrk hfrr2
      cases hfl
      rename_i hfll2 hflk hflr2
      by_cases' (key < k) hlt
      case pos =>
        by_cases' (key = lk) heqlk
        case pos =>
          rw [<-splayBST_equiv]
          repeat constructor
          all_goals try simp [*]
          all_goals repeat constructor
          all_goals try simp [*]
          all_goals repeat constructor
          all_goals try simp [*]
          apply ForallTree_greater
          apply hfrl2
          assumption
          linarith
          apply ForallTree_greater
          apply hfrr2
          assumption
          all_goals (rw [splayBST_equiv]; assumption)
        case neg =>
          by_cases' (key < lk) hltlk
          case pos =>
            cases hdes : ll.splay key with
            | leaf =>
              simp
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_greater
              apply hfrl2
              assumption
              linarith
              apply ForallTree_greater
              apply hfrr2
              assumption
              all_goals (rw [splayBST_equiv]; assumption)
            | node lll llk llv llr =>
              simp
              have hfsll : ForallTree (fun k' _ ↦ k' < lk) (ll.splay key) := by
                apply splay_Forall; assumption
              have hfsll2 : ForallTree (fun k' _ ↦ k' < k) (ll.splay key) := by
                apply splay_Forall; assumption
              rw [hdes] at hfsll
              rw [hdes] at hfsll2
              cases hfsll
              rename_i hfslll hllk hfsllr
              cases hfsll2
              rename_i hfslll2 hllk2 hfsllr2
              rw [hdes] at ihll
              rw [<-splayBST_equiv] at ihll
              cases ihll
              rename_i ihlll ihflll ihllr ihfllr
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_greater; apply hflr; assumption
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_greater; apply hfrl2; assumption
              linarith
              apply ForallTree_greater; apply hfrr2; assumption
              apply ForallTree_greater; apply hfrl2; assumption
              linarith
              apply ForallTree_greater; apply hfrr2; assumption
              all_goals (rw [splayBST_equiv]; assumption)
          case neg =>
            cases hdes : lr.splay key with -- TODO NOTE THIS: equivalent of destruct eqn:hdes
            | leaf =>
              simp
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_greater
              apply hfrl2
              assumption
              linarith
              apply ForallTree_greater
              apply hfrr2
              assumption
              all_goals (rw [splayBST_equiv]; assumption)
            | node lrl lrk lrv lrr =>
              simp
              have hfslr : ForallTree (fun k' _ ↦ k' > lk) (lr.splay key) := by
                apply splay_Forall; assumption
              have hfslr2 : ForallTree (fun k' _ ↦ k' < k) (lr.splay key) := by
                apply splay_Forall; assumption
              rw [hdes] at hfslr
              rw [hdes] at hfslr2
              cases hfslr
              rename_i hfslrl hlrk hfslrr
              cases hfslr2
              rename_i hfslrl2 hlrk2 hfslrr2
              rw [hdes] at ihlr
              rw [<-splayBST_equiv] at ihlr
              cases ihlr
              rename_i ihlrl ihflrl ihlrr ihflrr
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_less; apply hfll; assumption
              apply ForallTree_greater; apply hfrl2; assumption
              linarith
              apply ForallTree_greater; apply hfrr2; assumption
              all_goals (rw [splayBST_equiv]; assumption)
      case neg =>
        by_cases' (key = rk) heqrk
        case pos =>
          rw [<-splayBST_equiv]
          repeat constructor
          all_goals try simp [*]
          all_goals repeat constructor
          all_goals try simp [*]
          all_goals repeat constructor
          all_goals try simp [*]
          apply ForallTree_less
          apply hfll
          linarith
          linarith
          apply ForallTree_less
          apply hflr2
          assumption
          all_goals (rw [splayBST_equiv]; assumption)
        case neg =>
          by_cases' (key < rk) hltrk
          case pos =>
            cases hdes : rl.splay key with
            | leaf =>
              simp
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_less
              apply hfll2
              assumption
              linarith
              apply ForallTree_less
              apply hflr2
              assumption
              all_goals (rw [splayBST_equiv]; assumption)
            | node rll rlk rlv rlr =>
              simp
              have hfsrl : ForallTree (fun k' _ ↦ k' < rk) (rl.splay key) := by
                apply splay_Forall; assumption
              have hfsrl2 : ForallTree (fun k' _ ↦ k' > k) (rl.splay key) := by
                apply splay_Forall; assumption
              rw [hdes] at hfsrl
              rw [hdes] at hfsrl2
              cases hfsrl
              rename_i hfsrll hrlk hfsrlr
              cases hfsrl2
              rename_i hfsrll2 hrlk2 hfsrlr2
              rw [hdes] at ihrl
              rw [<-splayBST_equiv] at ihrl
              cases ihrl
              rename_i ihrll ihfrll ihrlr ihfrlr
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_less; apply hfll2; assumption
              all_goals repeat constructor
              all_goals try simp [*]
              linarith
              apply ForallTree_less; apply hflr2; assumption
              apply ForallTree_greater; apply hfrr; assumption
              all_goals (rw [splayBST_equiv]; assumption)
          case neg =>
            cases hdes : rr.splay key with
            | leaf =>
              simp
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_less
              apply hfll2
              assumption
              linarith
              apply ForallTree_less
              apply hflr2
              assumption
              all_goals (rw [splayBST_equiv]; assumption)
            | node rrl rrk rrv rrr =>
              simp
              have hfsrr : ForallTree (fun k' _ ↦ k' > rk) (rr.splay key) := by
                apply splay_Forall; assumption
              have hfsrr2 : ForallTree (fun k' _ ↦ k' > k) (rr.splay key) := by
                apply splay_Forall; assumption
              rw [hdes] at hfsrr
              rw [hdes] at hfsrr2
              cases hfsrr
              rename_i hfsrrl hrrk hfsrrr
              cases hfsrr2
              rename_i hfsrrl2 hrrk2 hfsrrr2
              rw [hdes] at ihrr
              rw [<-splayBST_equiv] at ihrr
              cases ihrr
              rename_i ihrrl ihfrrl ihrrr ihfrrr
              rw [<-splayBST_equiv]
              repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              all_goals repeat constructor
              all_goals try simp [*]
              apply ForallTree_less; apply hfll2; assumption
              linarith
              apply ForallTree_less; apply hflr2; assumption
              apply ForallTree_less; apply hfrl; assumption
              apply ForallTree_less; apply hfll2; assumption
              linarith
              apply ForallTree_less; apply hflr2; assumption
              constructor
              all_goals try simp [*]
              all_goals (rw [splayBST_equiv]; assumption)
