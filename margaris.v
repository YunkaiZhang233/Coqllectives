Require Import Coq.Logic.FinFun.

Parameter ZZ : Set.
Parameter oZ : ZZ.
Parameter pZ sZ : ZZ -> ZZ.

Section margaris.

Hypothesis Zps : forall x : ZZ, pZ (sZ x) = x.
Hypothesis Zsp : forall x : ZZ, sZ (pZ x) = x.
Hypothesis ZZ_ind_margaris : forall Q : ZZ-> Prop,
  Q oZ -> (forall y, Q y <-> Q (sZ y)) -> forall x, Q x.

(*
Define the predicate N (N(x) says that “x is a natural number”) on Z by 
N (x) := ∀Q, Q(0) → (∀y, Q(y) → Q(s(y))) → Q(x)
*)

(* says, x is a natural number *)
Definition N (x : ZZ) : Prop :=
  forall Q : ZZ -> Prop, 
    Q (oZ) -> (forall y : ZZ, Q (y) -> Q (sZ y)) -> Q (x).

(*
and add as an axiom (using Coq’s Hypothesis command) 
the assumption ¬N (p(0))
*)

Hypothesis nNp0 : ~ N (pZ oZ).

(*
Define the predicate M on Z by
M (x) := ∀Q, Q(0) → (∀y, Q(y) → Q(p(y))) → Q(x)
*)

(*
  says x is a non-positive number.
*)
Definition M (x : ZZ) : Prop :=
  forall Q : ZZ -> Prop, 
    Q (oZ) -> (forall y : ZZ, Q (y) -> Q (pZ y)) -> Q (x).


(*

Prove the following lemmas for Z:
 s and p are injective.
 N(0) and M(0), ∀x,N(x) → N(s(x)) and ∀x,M(x) → M(p(x)).  ∀x,N(p(x)) → N(x) and ∀x,M(s(x)) → M(x).
 ∀x,p(x) ̸= x and ∀x,s(x) ̸= x.
 ∀x,N(x) → s(x) ̸= 0 and ∀x,M(x) → p(x) ̸= 0.
 ∀x,M(x) → ¬N(p(x)) and ¬M(s(0)) and ∀x,N(x) → ¬M(s(x)).

*)

(*
  s and p are injective.
*)

Theorem s_injective:
  Injective sZ.
Proof.
  unfold Injective.
  intros x y H.
  assert (H1: pZ (sZ x) = pZ (sZ y)).
  {
    rewrite H.
    auto.
  }
  rewrite !Zps in H1.
  auto.
Qed.

Theorem p_injective:
  Injective pZ.
Proof.
  unfold Injective.
  intros x y H.
  assert (H1 : sZ (pZ x) = sZ (pZ y)).
  {
    rewrite H.
    auto.
  }
  rewrite !Zsp in H1.
  auto.
Qed.

(*
  N(0) and M(0), 
*)
Theorem n0: N (oZ).
Proof.
  unfold N.
  intros Q Ho Hi.
  auto.
Qed.

Theorem m0: M (oZ).
Proof.
  unfold M.
  intros Q Ho Hi.
  auto.
Qed.

(*
  ∀x,N(x) → N(s(x)) and ∀x,M(x) → M(p(x)).  
*)

Ltac nm_ind :=   
  intros Hn; 
  intros Q Hoz Hind; 
  apply Hind; 
  apply Hn; 
  auto.

Theorem n_s_ind:
  forall x:ZZ, N x -> N (sZ x).
Proof.
  intros x.
  unfold N.
  nm_ind.
Qed.

Theorem m_s_ind:
  forall x:ZZ, M x -> M (pZ x).
Proof.
  intros x.
  unfold M.
  nm_ind.
Qed.

(*
  ∀x,N(p(x)) → N(x) and ∀x,M(s(x)) → M(x).
*)

Theorem n_inv_ind:
  forall x:ZZ, N (pZ x) -> N x.
Proof.
  intros x.
  unfold N.
  intros Hz Q Ho Hind.
  rewrite <-Zsp.
  apply Hind.
  apply Hz; auto.
Qed.

Theorem m_inv_ind:
  forall x:ZZ, M (sZ x) -> M x.
Proof.
  intros x.
  unfold M.
  intros Hz Q Ho Hind.
  rewrite <-Zps.
  apply Hind.
  apply Hz; auto.
Qed.

(*
  ∀x,p(x) ̸= x and ∀x,s(x) ̸= x.
*)
Theorem p_change:
  forall x:ZZ, pZ x <> x.
Proof.
  apply ZZ_ind_margaris.
  (* base case: p 0 <> 0 *)
  {
    intros Heq.
    rewrite Heq in nNp0.
    assert (H0 : N oZ) by apply n0.
    apply nNp0 in H0.
    auto.
  }
  (* inductive case *)
  {
    intros y.
    split; intros H1 Heq; apply H1.
    (* p y <> y -> p (s y) <> s y *)
    {
      apply s_injective.
      rewrite Zsp.
      rewrite Zps in Heq.
      auto.
    }
    (* p (s y) <> s y -> p y <> y*)
    {
      rewrite Zps.
      apply p_injective.
      rewrite Zps.
      auto.
    }
  }

Qed.

Theorem s_change:
  forall x:ZZ, sZ x <> x.
Proof.
  apply ZZ_ind_margaris.
  (* base case: p 0 <> 0 *)
  {
    intros Heq.
    symmetry in Heq.
    rewrite Heq in nNp0.
    rewrite Zps in nNp0.
    apply nNp0.
    apply n0.
  }
  (* inductive case *)
  {
    intros y.
    split; intros H1 Heq; apply H1.
    (* s y <> y -> s (s y) <> s y *)
    {
      apply s_injective.
      auto.
    }
    (* s (s y) <> s y -> s y <> y*)
    {
      rewrite Heq.
      auto.
    }
  }

Qed.

(*
  ∀x,N(x) → s(x) ̸= 0 and ∀x,M(x) → p(x) ̸= 0.
*)
Theorem n_ind_neq_0:
  forall x : ZZ, N x -> sZ x <> oZ.
Proof.
  intros x Hnx Heq.
  rewrite <-Heq in nNp0.
  rewrite Zps in nNp0.
  apply nNp0.
  auto.
Qed.

Theorem m_ind_neq_0:
  forall x: ZZ, M x -> pZ x <> oZ.
Proof.
  intros x Hmx Heq.
  assert (Hx1 : x = sZ oZ).
  {
    rewrite <- (Zsp x).
    apply f_equal.
    auto.
  }
  inversion_clear Heq.
  rewrite Hx1 in Hmx.
  (*
    M x: applies to all x <= 0
    N x: applies to all x >= 0
  *)
  
  set (q := fun x : ZZ => ~N (pZ x)).

  assert (H0 : q oZ) by apply nNp0.

  assert (Hind : forall y : ZZ, q y -> q (pZ y)).
  {
    intros y.
    unfold q.
    intros Hny Hnpy.
    apply Hny.
    apply n_inv_ind.
    auto.
  }

  specialize (Hmx q).
  
  assert (Hf: q (sZ oZ)).
  {
    apply Hmx; auto.
  }

  unfold q in Hf.
  rewrite Zps in Hf.
  
  apply Hf.

  apply n0.
Qed.

(*
  ∀x,M(x) → ¬N(p(x)) 
*)
Theorem mx_not_npx:
  forall x : ZZ, M x -> ~ N (pZ x).
Proof.
  intros x Hmx H.
  unfold M in Hmx.
  specialize (Hmx (fun x => ~N (pZ x))).
  simpl in Hmx.

  assert (Hind: (forall y : ZZ, ~ N (pZ y) -> ~ N (pZ (pZ y)))).
  {
    intros y H1 H2.
    apply H1.
    apply n_inv_ind.
    auto.
  }

  assert (H' : ~ N (pZ x)).
  {
    apply Hmx.
    - apply nNp0.
    - apply Hind.
  }

  apply H'.
  apply H.

Qed.

(*
 and ¬M(s(0)) 
*)
Theorem not_ms0:
  ~ M (sZ oZ).
Proof.
  intros H.
  unfold M in H.
  specialize (H (fun x => ~ N (pZ x))).
  simpl in H.
  rewrite Zps in H.
  assert (H' : ~ N oZ).
  {
    apply H; auto.
    intros y.
    intros H1 H2.
    apply H1.
    apply n_inv_ind.
    auto.
  }
  apply H'.
  apply n0.
Qed.

(*
 and ∀x,N(x) → ¬M(s(x)).
*)
Theorem nx_not_msx :
  forall x : ZZ, N x -> ~ M (sZ x).
Proof.
  intros x Hn Hm.
  unfold N in Hn.
  specialize (Hn (fun x => ~ M (sZ x))).
  simpl in Hn.
  apply Hn; auto.
  - apply not_ms0.
  - intros y H1 H2.
    apply H1.
    apply m_inv_ind.
    auto.
Qed.

(* Define “positive” and “negative” as predicates pos and neg on Z. *)

(*

Possible definitions are pos(x) := N(p(x)) 
  and neg(x) := M(s(x)) 
and then prove ∀x : Z, N (x) → x = 0 ∨ N (p(x)) 
  and ∀x : Z, M (x) → x = 0 ∨ M (s(x)) 
to prove ∀x : Z,pos(x)∨x = 0∨neg(x) 
  and ∀x : Z,pos(x) → x ̸= 0∧¬neg(x) etc.
*)

(*
  Prove that, 
  for x : Z, either pos(x) or x = 0 or neg(x).
*)

Definition pos (x : ZZ) := N (pZ x).

Definition neg (x : ZZ) := M (sZ x).

Theorem n_non_neg (x : ZZ) :
  N x -> x = oZ \/ N (pZ x).
Proof.
  intros Hn.
  set (q := fun x => x = oZ \/ N (pZ x)).
  specialize (Hn q) as H.
  induction H.
  (* x = oZ *)
  {
    auto.
  }
  (* N (pZ x) *)
  {
    auto.
  }
  (* base case *)
  {
    unfold q.
    auto.
  }
  (* inductive step *)
  {
    intros y Hqy.
    unfold q.
    right.
    rewrite Zps.
    destruct Hqy as [H0 | Hind].
    {
      rewrite H0.
      apply n0.
    }
    {
      apply n_inv_ind.
      auto.
    }
  }
Qed.

Theorem m_non_pos (x : ZZ) :
  M x -> x = oZ \/ M (sZ x).
Proof.
  intros Hm.
  set (q := fun x => x = oZ \/ M (sZ x)).
  specialize (Hm q) as H.
  induction H; auto.
  (* base case *)
  {
    unfold q.
    auto.
  }
  (* inductive case *)
  {
    intros y.
    unfold q.
    intros Hind.
    rewrite Zsp.
    right.
    destruct Hind as [H1 | H2].
    {
      rewrite H1.
      apply m0.
    }
    {
      apply m_inv_ind.
      auto.
    }
  }
Qed.

(* proving pos, 0, neg are mutually exclusive *)
Theorem pos_mutex:
  forall x : ZZ, pos x -> (x <> oZ) /\ (~ neg x).
Proof.
  intros x Hp.
  split.
  {
    intros Heq.
    rewrite Heq in Hp.
    unfold pos in Hp.
    apply nNp0.
    auto.
  }
  {
    intros Hneg.
    unfold neg in Hneg.
    unfold pos in Hp.
    apply mx_not_npx in Hneg.
    apply Hneg.
    rewrite Zps.
    apply n_inv_ind.
    auto.
  }
Qed.

Theorem o_mutex:
  forall x : ZZ, x = oZ -> (~ pos x) /\ (~ neg x).
Proof.
  intros x Heq.
  rewrite !Heq.
  split.
  {
    intros Hp.
    unfold pos in Hp.
    apply nNp0.
    auto.
  }
  {
    intros Hn.
    unfold neg in Hn.
    apply not_ms0.
    auto.
  }
Qed.

Theorem neg_mutex:
  forall x : ZZ, neg x -> (x <> oZ) /\ (~ pos x).
Proof.
  intros x Hn.
  split.
  {
    intros Heq.
    rewrite Heq in Hn.
    unfold neg in Hn.
    apply not_ms0.
    auto.
  }
  {
    intros Hp.
    apply pos_mutex in Hp.
    destruct Hp as [H1 H2].
    apply H2.
    auto.
  }
Qed.

Theorem int_composition:
  forall x : ZZ, pos x \/  x = oZ \/  neg x.
Proof.
  intros x.
  set (f := fun y : ZZ => pos y \/ y = oZ \/ neg y).
  specialize (ZZ_ind_margaris f).
  assert (Hbase : f oZ) by (unfold f; auto).
  assert (Hind : (forall y : ZZ, f y <-> f (sZ y))).
  {
    intros y.
    split;
    intros H.
    (* f y -> f (sZ y) *)
    {
      (* pos - pos *)
      destruct H as [Hpos | [Ho | Hneg]].
      {
        unfold pos in Hpos.
        left.
        unfold pos.
        rewrite Zps.
        apply n_inv_ind.
        auto.
      }
      (* 0 - pos *)
      {
        rewrite Ho.
        left.
        unfold pos.
        rewrite Zps.
        apply n0.        
      }
      (* neg: neg or 0 *)
      {
        right.
        unfold neg in Hneg.
        unfold neg.
        apply m_non_pos in Hneg.
        auto.
      }
    }
    (* f (sZ y) -> f y *)
    {
      destruct H as [Hpos | [Ho | Hneg]].
      (* pos - pos / 0 *)
      {
        unfold pos in Hpos.
        rewrite Zps in Hpos.
        apply n_non_neg in Hpos.
        unfold f.
        unfold pos.
        destruct Hpos as [H1 | H2].
        - right. left. auto.
        - left. auto.
      }
      (* 0 - neg *)
      {
        right.
        right.
        unfold neg.
        rewrite Ho.
        apply m0.
      }
      (* neg - neg *)
      {
        right. right.
        unfold neg in Hneg.
        unfold neg.
        apply m_inv_ind.
        auto.        
      }
    }
  }
  apply ZZ_ind_margaris.
  (* base case *)
  - apply Hbase.
  (* inductive steps *)
  - apply Hind.
Qed.
End margaris.