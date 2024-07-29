Require Import String.
Require Import Equality.
Local Open Scope string_scope.
(* 
  Define inductive types type and term 
  for the types and terms of the simply typed lambda calculus. 
  For example the definition of type might look like 
*)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

(* Defining Map *)

Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Compute (examplemap "foo").

(* Map Finished *)
(* Will be used for typing context *)

Inductive type : Set :=
  | var_type : string -> type
  | fun_type : type -> type -> type
  .

(*
  The type checker needs to be able to decide equality of types. 
  (If you apply a function to an argument, 
  the type of the argument needs to match the type of the domain of the function.) 
  For this prove the lemma
*)
Lemma type_dec: forall A B : type, {A = B} + {A <> B}.
Proof.
  decide equality.
  apply string_dec. (* from "Search sumbool string" *)
Qed.

(*
  term form:
  1. variable, use `string` to represent
  2. abstraction, variable + STLC term
  3. application, STLC term + STLC term
*)

Definition variable_STLC : Set := string.

Inductive term : Set :=
  | var_term : string -> term
  | abs_term : string -> type -> term -> term
  | app_term : term -> term -> term.


(* Definition assoc: forall A B : Set, list (A * B) -> A -> B -> Prop.
Proof. *)
Definition context := total_map (option type).
Definition empty_context : context := t_empty None.
(* Inductive has_type: list (string * type) -> term -> type -> Prop :=
  | has_type_var (gamma: list (string * type)) (x : string) (a : type): 
      assoc (cons (x, a) gamma) x a -> has_type gamma (var_term x) a
  | has_type_abs (gamma: list (string * type)) (x : string) (a : type) (m : term) (b : type) (ft : type):
      assoc (cons (x, a) gamma) x a -> has_type gamma m b -> ft = fun_type a b ->  has_type gamma (abs_term x a m) ft
  | has_type_app (gamma: list (string * type)) (a b : type) (f n : term):
      has_type gamma f (fun_type a b) -> has_type gamma n a -> has_type gamma (app_term f n) b
  . *)

(* tests *)
(* Definition test1_gamma := (cons (3, 4) nil).
Eval compute in (assoc test1_gamma 1 2). *)

(*
 Define an inductive predicate has_type, such that the Coq formula
  has_type Gamma M A
corresponds to the derivability of the judgment
  Gamma |- M : A
*)  

Definition context_update (gamma: context) (x : string) (a : type) :=
  t_update gamma x (Some a).

Inductive has_type : context -> term -> type -> Prop :=
  | has_type_var (gamma : context) (x : string) (t : type):
      gamma x = Some t -> has_type gamma (var_term x) t
  | has_type_abs (gamma : context) (x : string) (a : type) (m : term) (b : type):
      has_type (context_update gamma x a) m b -> has_type gamma (abs_term x a m) (fun_type a b)
  | has_type_app (gamma : context) (f n : term) (a b : type):
      has_type gamma f (fun_type a b) /\ has_type gamma n a -> has_type gamma (app_term f n) b
  .

(*
  Write a recursive function type_check that (in a given context) 
  returns the type of an element of term. 
  A possible Coq type for this function might be

  type_check
       : list (string * type) -> term -> option type
  
  If the input term (the second argument) is not type correct, 
  the function will have to return None. 
  For this reason the output type is not type but option type.
*)

Fixpoint type_check
  (gamma : context) 
  (m: term) 
  {struct m}: option type :=
  match m as m with 
  | var_term x => gamma x
  | abs_term x a m => 
      match type_check (context_update gamma x a) m with
      | Some b => Some (fun_type a b)
      | None => None
      end
  | app_term f n => 
      match type_check gamma f, type_check gamma n with
      | Some (fun_type a b), Some c =>
          if type_dec a c then Some b else None
      | _, _ => None
      end
  end.

Search sumbool.

Definition typeA := var_type "A".
Definition varX := var_term "x".

Compute (type_check (context_update empty_context "x" typeA) varX).

Theorem typecheck_safe (gamma : context) (m : term) (t : type):
  type_check gamma m = Some t -> has_type gamma m t.
Proof.
  generalize dependent gamma.
  generalize dependent t.
  induction m; intros ty gamma Htc; inversion Htc.
  (* var *)
  {
    apply has_type_var.
    assumption. 
  }
  (* abs *)
  {
    rename s into x.
    remember (context_update gamma x t) as gamma'.
    remember (type_check gamma' m) as t'.
    destruct t'; try solve_by_invert.
    inversion H0. subst.
    apply has_type_abs.
    apply IHm.
    symmetry.
    apply Heqt'.
  }
  (* app *)
  {
    remember (type_check gamma m1) as to1.
    destruct to1 as [t1|]; try solve_by_invert.
    destruct t1 as [| t11 t12]; try solve_by_invert.
    remember (type_check gamma m2) as to2.
    destruct to2 as [t2|]; try solve_by_invert.
    destruct (type_dec t11 t2) eqn:Hteq; try solve_by_invert.
    apply has_type_app with (a:=t2).
    injection H0 as H0.
    subst.
    split; [apply IHm1 | apply IHm2]; symmetry; [apply Heqto1 | apply Heqto2].
  }
Qed.