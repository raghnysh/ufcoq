(* The primitive types *)

(* ================================================================ *)
(** ** Notation for builtin function types with constant codomain   *)
(* ================================================================ *)

(* begfrag:ave0dtr6 *)
Notation "X -> Y" := (forall (_ : X), Y)
  (at level 99, right associativity, Y at level 200).
(* endfrag *)

(* ================================================================ *)
(** ** The false type                                               *)
(* ================================================================ *)

(* begfrag:776l3lwg *)
Inductive False: Type := .
(* endfrag *)

(* begfrag:b79a8cj0 *)
Definition false_induction
  : forall (F : False -> Type) (x : False), F x
  := False_rect.
(* endfrag *)

(* ================================================================ *)
(** ** The true type                                                *)
(* ================================================================ *)

(* begfrag:815by4qc *)
Inductive True : Type := only : True.
(* endfrag *)

(* begfrag:xfdlpg97 *)
Definition true_induction
  : forall (F : True -> Type), F only -> forall (x : True), F x
  := True_rect.
(* endfrag *)

(* ================================================================ *)
(** ** The boolean type                                             *)
(* ================================================================ *)

(* begfrag:2xu2p4rk *)
Inductive Boolean : Type := yes : Boolean | no : Boolean.
(* endfrag *)

(* begfrag:e8s65324 *)
Definition boolean_induction
  : forall (F : Boolean -> Type),
      F yes -> F no -> forall (x : Boolean), F x
  := Boolean_rect.
(* endfrag *)

(* ================================================================ *)
(** ** The type of natural numbers                                  *)
(* ================================================================ *)

(* begfrag:x6u83qds *)
Inductive Natural : Type
  := zero : Natural | successor : Natural -> Natural.
(* endfrag *)

(* begfrag:mblpgwu0 *)
Definition natural_induction
  : forall (F : Natural -> Type),
      F zero
        -> (forall (n : Natural), F n -> F (successor n))
            -> forall (n : Natural), F n
  := Natural_rect.
(* endfrag *)

(* ================================================================ *)
(** ** Identity types                                               *)
(* ================================================================ *)

(* begfrag:whnabw73 *)
Inductive Ident (X : Type) (x : X) : X -> Type
  := ident_unit : Ident X x x.

Arguments Ident {X} x  _.
Arguments ident_unit {X} x.
(* endfrag *)

(* begfrag:xxyabzuf *)
Definition ident_induction
  : forall (X : Type)
           (x : X)
           (F : forall (y : X), Ident x y -> Type),
      F x (ident_unit x) -> forall (y : X) (p : Ident x y), F y p
  := Ident_rect.

Arguments ident_induction {X} x F _ y p.
(* endfrag *)

(* ================================================================ *)
(** ** Sigma types                                                  *)
(* ================================================================ *)

(* begfrag:agn2f6jd *)
Record Sigma (X : Type) (F : X -> Type) : Type
  := sigma {sigma1 : X; sigma2 : F sigma1}.

Arguments Sigma {X} F.
Arguments sigma {X} F _ _.
Arguments sigma1 {X F} _.
Arguments sigma2 {X F} _.
(* endfrag *)

(* End of file *)
