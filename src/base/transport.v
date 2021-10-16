(* Transport along identities *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:a61auiqf *)
Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.
Require Import ufcoq.base.ident.
(* endfrag *)

(* ================================================================ *)
(** ** Transport                                                    *)
(* ================================================================ *)

(* begfrag:szbmydj4 *)
Definition transport
  : forall (X : Type) (F : X -> Type) (x y : X),
      Ident x y -> F x -> F y
  := fun (X : Type)
         (F : X -> Type)
         (x : X)
       => ident_recursion  x
                           (fun (y : X) => F x -> F y)
                           (function_unit (F x)).

Arguments transport {X} F {x y} _ _.
(* endfrag *)

(* ================================================================ *)
(** ** The functoriality of transport                               *)
(* ================================================================ *)

(* begfrag:14dnjq1z *)
Example _transport_unital
  : forall (X : Type) (F : X -> Type) (x y : X),
      Ident (function_unit (F x)) (transport F (ident_unit x))
  := fun (X : Type) (F : X -> Type) (x y : X)
       => ident_unit (function_unit (F x)).
(* endfrag *)

(* begfrag:dee0teec *)
Definition transport_multiplicative
  : forall (X : Type)
           (F : X -> Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident (transport F (ident_compose p q))
            (function_compose (transport F q) (transport F p))
  := fun (X : Type) (F : X -> Type) (x : X)
       =>
         let
           G : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident y z),
                       Ident (transport F (ident_compose p q))
                             (function_compose (transport F q)
                                               (transport F p))
         in let
           base : G x (ident_unit x)
             := fun (z : X) (q : Ident x z)
                  => ident_unit (transport F q)
         in
           ident_induction x G base.

Arguments transport_multiplicative {X} F {x y} p {z} q.
(* endfrag *)

(* ================================================================ *)
(** ** Inverse transport                                            *)
(* ================================================================ *)

(* begfrag:xsfz3fch *)
Definition transport_inverse
  : forall (X : Type) (F : X -> Type) (x y : X),
      Ident x y -> F y -> F x
  := fun (X : Type) (F : X -> Type) (x y : X) (p : Ident x y)
       => transport F (ident_inverse p).

Arguments transport_inverse {X} F {x y} _ _.
(* endfrag *)

(* begfrag:3h9vmhhx *)
Definition transport_left_inverse
  : forall (X : Type) (F : X -> Type) (x y : X) (p : Ident x y),
      Ident (function_unit (F x))
            (function_compose (transport_inverse F p)
                              (transport F p))
  := fun (X : Type) (F : X -> Type) (x : X)
       =>
         let
           G : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => Ident (function_unit (F x))
                           (function_compose (transport_inverse F p)
                                             (transport F p))
         in let
           base : G x (ident_unit x)
             := ident_unit (function_unit (F x))
         in
           ident_induction x G base.

Arguments transport_left_inverse {X} F {x y} p.
(* endfrag *)

(* begfrag:fxpptx7v *)
Definition transport_right_inverse
  : forall (X : Type) (F : X -> Type) (x y : X) (p : Ident x y),
      Ident (function_unit (F y))
            (function_compose (transport F p)
                              (transport_inverse F p))
  := fun (X : Type) (F : X -> Type) (x : X)
       =>
         let
           G : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => Ident (function_unit (F y))
                           (function_compose (transport F p)
                                             (transport_inverse F p))
         in let
           base : G x (ident_unit x)
             := ident_unit (function_unit (F x))
         in
           ident_induction x G base.

Arguments transport_right_inverse {X} F {x y} p.
(* endfrag *)

(* ================================================================ *)
(** ** Transport along 2-identities                                 *)
(* ================================================================ *)

(* begfrag:bpd9ik8n *)
Definition transport_ident
  : forall (X : Type) (F : X -> Type) (x y : X) (p q : Ident x y),
      Ident p q -> Ident (transport F p) (transport F q)
  := fun (X : Type) (F : X -> Type) (x y : X) (p : Ident x y)
     => ident_recursion p
                        (fun (q : Ident x y)
                           => Ident (transport F p) (transport F q))
                        (ident_unit (transport F p)).

Arguments transport_ident {X} F {x y p q} _.
(* endfrag *)

(* ================================================================ *)
(** ** Relative transport                                           *)
(* ================================================================ *)

(* begfrag:hl07wyga *)
Definition transport_relative
  : forall (X : Type)
           (F : X -> Type)
           (G : forall (x : X), F x -> Type)
           (x y : X)
           (p : Ident x y)
           (e : F x),
      G x e -> G y (transport F p e)
  := fun (X : Type)
         (F : X -> Type)
         (G : forall (x : X), F x -> Type)
         (x : X)
       =>
         let
           H : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (e : F x), G x e -> G y (transport F p e)
         in let
           base : H x (ident_unit x)
             := fun (e : F x) => function_unit (G x e)
         in
           ident_induction x H base.

Arguments transport_relative {X F} G {x y} p e _.
(* endfrag *)

(* End of file *)
