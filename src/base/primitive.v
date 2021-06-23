(* The primitive types *)

(* ================================================================ *)
(** ** Notation for builtin function types with constant codomain   *)
(* ================================================================ *)

(* begfrag:notation-function-type *)
Notation "X -> Y" := (forall (_ : X), Y)
  (at level 99, right associativity, Y at level 200).
(* endfrag *)

(* ================================================================ *)
(** ** The false type                                               *)
(* ================================================================ *)

(* begfrag:false-type *)
Inductive False: Type := .
(* endfrag *)

(* begfrag:false-induction *)
Definition false_induction
  : forall (F : False -> Type) (x : False), F x
  := False_rect.
(* endfrag *)

(* ================================================================ *)
(** ** The true type                                                *)
(* ================================================================ *)

(* begfrag:true-type *)
Inductive True : Type := only : True.
(* endfrag *)

(* begfrag:true-induction *)
Definition true_induction
  : forall (F : True -> Type), F only -> forall (x : True), F x
  := True_rect.
(* endfrag *)

(* ================================================================ *)
(** ** The boolean type                                             *)
(* ================================================================ *)

(* begfrag:boolean-type *)
Inductive Boolean : Type := yes : Boolean | no : Boolean.
(* endfrag *)

(* begfrag:boolean-induction *)
Definition boolean_induction
  : forall (F : Boolean -> Type),
      F yes -> F no -> forall (x : Boolean), F x
  := Boolean_rect.
(* endfrag *)

(* ================================================================ *)
(** ** The type of natural numbers                                  *)
(* ================================================================ *)

(* begfrag:natural-type *)
Inductive Natural : Type
  := zero : Natural | successor : Natural -> Natural.
(* endfrag *)

(* begfrag:natural-induction *)
Definition natural_induction
  : forall (F : Natural -> Type),
      F zero
        -> (forall (n : Natural), F n -> F (successor n))
            -> forall (n : Natural), F n
  := Natural_rect.
(* endfrag *)

(* ================================================================ *)
(** ** Equality types                                               *)
(* ================================================================ *)

(* begfrag:equal-type *)
Inductive Equal (X : Type) (x : X) : X -> Type
  := reflexive : Equal X x x.

Arguments Equal {X} x  _.
Arguments reflexive {X} x.
(* endfrag *)

(* begfrag:equal-induction *)
Definition equal_induction
  : forall (X : Type)
           (x : X)
           (F : forall (x' : X), Equal x x' -> Type),
      F x (reflexive x) -> forall (x' : X) (p : Equal x x'), F x' p
  := Equal_rect.

Arguments equal_induction {X} x F _ x' p.
(* endfrag *)

(* ================================================================ *)
(** ** Sigma types                                                  *)
(* ================================================================ *)

(* begfrag:sigma-type *)
Record _Sigma (X : Type) (F : X -> Type) : Type
  := sigma {sigma1 : X; sigma2 : F sigma1}.

Arguments _Sigma {X} F.
Arguments sigma {X} F _ _.
Arguments sigma1 {X F} _.
Arguments sigma2 {X F} _.
(* endfrag *)

(* begfrag:notation-sigma-type *)
Notation "'Sigma' x .. y , P"
  := (_Sigma (fun x => .. (_Sigma (fun y => P)) ..))
       (at level 200, x binder, y binder, right associativity).
(* endfrag *)

(* End of file *)
