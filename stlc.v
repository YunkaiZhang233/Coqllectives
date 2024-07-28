Require Import String.
Require Import Equality.
Local Open Scope string_scope.
(* 
  Define inductive types type and term 
  for the types and terms of the simply typed lambda calculus. 
  For example the definition of type might look like 
*)

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
Proof.

Defined. *)


(*
  for duplicate bindings: only the first value in typing context matters!!!
*)

Inductive assoc {A B: Set}: list (A * B) -> A -> B -> Prop :=
  | assoc_front (rest: list (A * B)) (e1 : A) (e2 : B) : assoc (cons (e1, e2) rest) e1 e2
  | assoc_cons (rest: list (A * B)) (e1 : A) (e2 : B) (f1 : A) (f2 : B) : assoc rest e1 e2 -> assoc (cons (f1, f2) rest) e1 e2
  .

Print sig.
Check exist.

Fixpoint lookup {A B: Set}
  (equal_proc_dec: forall x y : A, {x = y} + {x <> y}) 
  (context: list (A * B))
  (key: A) 
  {struct context}
  :
  option B:=

  match context with
    | nil => None
    | (cons (pair a b) rest) => if equal_proc_dec a key then Some b else (lookup equal_proc_dec rest key)
  end.

(* tests *)
(* Definition test1_gamma := (cons (3, 4) nil).
Eval compute in (assoc test1_gamma 1 2). *)

(*
 Define an inductive predicate has_type, such that the Coq formula
  has_type Gamma M A
corresponds to the derivability of the judgment
  Gamma |- M : A
*)  

Inductive has_type: list (string * type) -> term -> type -> Prop :=
  | has_type_var (gamma: list (string * type)) (x : string) (a : type): 
      assoc (cons (x, a) gamma) x a -> has_type gamma (var_term x) a
  | has_type_abs (gamma: list (string * type)) (x : string) (a : type) (m : term) (b : type):
      assoc (cons (x, a) gamma) x a -> has_type gamma m b -> has_type gamma (abs_term x a m) (fun_type a b)
  | has_type_app (gamma: list (string * type)) (a b : type) (f n : term):
      has_type gamma f (fun_type a b) -> has_type gamma n a -> has_type gamma (app_term f n) b
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
  (context: list (string * type)) 
  (m: term) 
  {struct m}: option type :=
  match m as m with 
  | var_term x => lookup string_dec context x
  | abs_term x a m => 
      match type_check (cons (x, a) context) m with
      | None => None
      | Some b => Some (fun_type a b)
      end
  | app_term f n => 
      match type_check context f, type_check context n with
      | Some tf, Some a =>
          match tf with
          | fun_type a b => Some b
          | _ => None
          end
      | _, _ => None
      end
  end.


Definition typeA := var_type "A".
Definition varX := var_term "x".

Definition empty_env : list (string * type) := nil.
Compute (type_check (cons ("x", typeA) empty_env) varX).
