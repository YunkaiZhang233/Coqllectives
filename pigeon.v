Require Import Arith.
Require Import Lia.

(* 
If you put n pigeons in m holes, 
with m < n, then at least one hole with have more than one pigeon in it.
 *)


(* 
f is the function that maps the number of a pigeon in {0...n−1} 
to the number of its hole in {0...m−1}

The fact that f also will map numbers ≥ n to something will not hurt.
 *)


Lemma pigeon_hole :
  forall m n, m < n ->
    forall f, (forall i, i < n -> f i < m) ->
      exists i, i < n /\
        exists j, j < n /\ i <> j /\ f i = f j.
Proof.
  intros m n.
  induction n as [|n' IH]; intros Hmn f Hf; simpl.
  - specialize (Hf O). 
    exfalso.
    lia.
  - elim (le_lt_dec n' m); intros Hcmp.
    (* n' <= m*)
    {
      admit.
    }
    (* m < n' *)
    {

    }
    
Qed.
