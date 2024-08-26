Require Import Nat Lia Arith.


Inductive Acc {X : Type} (R : X -> X -> Prop) (x : X) : Prop :=
  Acc_intro : (forall y : X, R y x -> Acc R y) -> Acc R x.

Definition well_founded {X : Type} (R : X -> X -> Prop) : Prop :=
   forall (x : X), Acc R x.

(* Prove that the standard ordering on natural numbers is well- founded. *)
Theorem nat_wf : well_founded lt.
Proof.
  unfold well_founded.
  intros x.
  induction x as [|x' Hind]; apply Acc_intro.
  - intros y Hy. destruct y; exfalso; lia.
  - intros y Hy. inversion Hind.
    apply Acc_intro.
    intros y' Hy'.
    destruct (lt_eq_lt_dec y' x') eqn:Hcon; try (elim s).
    + intros H0. apply H. auto.
    + intros H0. rewrite H0. auto.
    + exfalso. lia.
Qed.

(*
there is an obvious “less than” relation on the type bool of Booleans. 
Show that this relation is constructively well-founded. 
*)

Definition bool_lt (b1 b2 : bool) : Prop := (b1 = false) /\ (b2 = true).

Theorem bool_lt_wf : well_founded bool_lt.
Proof.
  unfold well_founded.
  intros x. 
  destruct x; apply Acc_intro; intros y H; unfold bool_lt in H; destruct H as [H1 H2].
  - subst. apply Acc_intro. intros z Hb. unfold bool_lt in Hb. exfalso. lia.
  - exfalso. lia.
Qed.


(*
Show that if this relation is classically well-founded 
  (every non-empty subset has a minimal element), 
then the law of excluded middle holds.
*)

(*
  For a written version of the theoretical reasoning,
  refer to 
  https://ncatlab.org/toddtrimble/published/classical+well-foundedness
  https://ncatlab.org/nlab/show/well-founded+relation
*)
Definition classical_well_founded {X : Type} (R : X -> X -> Prop) :=
  forall (P : X -> Prop), 
    (exists x, P x) ->
         exists t, P t /\ (forall y, P y -> ~ (R y t)).

Lemma bool_lt_f_t :
  bool_lt false true.
Proof.
  unfold bool_lt.
  auto.
Qed.

Theorem classical_lem :
  classical_well_founded bool_lt -> (forall Q : Prop, Q \/ ~ Q).
Proof.
  intros H.
  unfold classical_well_founded in H.
  intros Q.
  set (fP := fun a => (a = true) \/ (bool_lt a true /\ Q)).
  
  assert (H0 : exists x : bool, fP x).
  {
    exists true.
    unfold fP.
    auto.
  }


  specialize (H fP).
  apply H in H0.

  destruct H0 as [t [H1 H2]].
  unfold fP in H1.

  elim H1.
  {
    intros Ht.
    rewrite Ht in H1.
    rewrite Ht in H2.
    right.
    intros Hq.
    specialize (H2 false).
    assert (Hf : fP false).
    {
      unfold fP.
      right.
      split; auto.
      apply bool_lt_f_t.
    }
    apply H2 in Hf.
    assert (Hf' : bool_lt false true) by (apply bool_lt_f_t).
    auto.
  }
  {
    intros [Ht1 Ht2].
    left.
    auto.
  }
Qed.


  



