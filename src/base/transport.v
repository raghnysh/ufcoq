(* Transport along identities *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:a61auiqf *)
Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.
Require Import ufcoq.base.ident.
Require Import ufcoq.base.elident.
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

(* ================================================================ *)
(** ** The lift of an identity                                      *)
(* ================================================================ *)

(* begfrag:3p6u5byg *)
Definition ident_lift
  : forall (X : Type)
           (F : X -> Type)
           (x y : X)
           (p : Ident x y)
           (e : F x),
      Ident (sigma F x e) (sigma F y (transport F p e))
  := fun (X : Type) (F : X -> Type) (x : X)
       =>
         let
           G : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (e : F x),
                       Ident (sigma F x e)
                             (sigma F y (transport F p e))
         in let
           base : G x (ident_unit x)
             := fun (e : F x) => ident_unit (sigma F x e)
         in
           ident_induction x G base.

Arguments ident_lift {X} F {x y} p e.
(* endfrag *)

(* begfrag:amyvyisd *)
Definition ident_map_dependent
  : forall (X : Type)
           (F : X -> Type)
           (f : forall (x : X), F x)
           (x y : X)
           (p : Ident x y),
      Ident (transport F p (f x)) (f y)
  := fun (X : Type) (F : X -> Type) (f : forall (x : X), F x) (x : X)
       =>
         let
           G : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => Ident (transport F p (f x)) (f y)
         in let
           base : G x (ident_unit x)
             := ident_unit (f x)
         in
           ident_induction x G base.

Arguments ident_map_dependent {X} F f {x y} p.
(* endfrag *)

(* ================================================================ *)
(** ** Transport in a constant family                               *)
(* ================================================================ *)

(* begfrag:zb5p2ik1 *)
Definition transport_constant
  : forall (X Y : Type) (x x' : X) (p : Ident x x') (y : Y),
      Ident (transport (@constant_function X Type Y) p y) y
  := fun (X Y : Type) (x : X)
       =>
         let
           G : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => forall (y : Y),
                       Ident (transport
                                (@constant_function X Type Y) p y)
                             y
         in let
           base : G x (ident_unit x)
             := fun (y : Y) => ident_unit y
         in
           ident_induction x G base.

Arguments transport_constant {X Y x x'} p y.
(* endfrag *)

(* begfrag:adxkhzcz *)
Definition ident_map_dependent_constant
  : forall (X Y : Type) (f : X -> Y) (x x' : X) (p : Ident x x'),
      Ident (ident_map_dependent (@constant_function X Type Y) f p)
            (ident_compose (transport_constant p (f x))
                           (ident_map f p))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       =>
         let
           G : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => Ident (ident_map_dependent
                              (@constant_function X Type Y) f p)
                           (ident_compose (transport_constant p (f x))
                                          (ident_map f p))
         in let
           base : G x (ident_unit x)
             := ident_unit (ident_unit (f x))
         in
           ident_induction x G base.

Arguments ident_map_dependent_constant {X Y} f {x x'} p.
(* endfrag *)

(* ================================================================ *)
(** ** Transport in a pullback family                               *)
(* ================================================================ *)

(* begfrag:twntxsxu *)
Definition transport_pullback
  : forall (Y : Type)
           (F : Y -> Type)
           (X : Type)
           (f : X -> Y)
           (x x' : X)
           (p : Ident x x')
           (e : F (f x)),
      Ident (transport (function_compose F f) p e)
            (transport F (ident_map f p) e)
  := fun (Y : Type) (F : Y -> Type) (X : Type) (f : X -> Y) (x : X)
       =>
         let
           G : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => forall (e : F (f x)),
                       Ident (transport (function_compose F f) p e)
                             (transport F (ident_map f p) e)
         in let
           base : G x (ident_unit x)
             := fun (e : F (f x)) => ident_unit e
         in
           ident_induction x G base.

Arguments transport_pullback {Y} F {X} f {x x'} p e.
(* endfrag *)

(* ================================================================ *)
(** ** Action of a map of families on transport                     *)
(* ================================================================ *)

(* begfrag:5285t6hn *)
Definition transport_map
  : forall (X : Type)
           (F G : X -> Type)
           (u : forall (x : X), F x -> G x)
           (x y : X)
           (p : Ident x y)
           (e : F x),
      Ident (transport G p (u x e))
            (u y (transport F p e))
  := fun (X : Type)
         (F G : X -> Type)
         (u : forall (x : X), F x -> G x)
         (x : X)
       =>
         let
           H : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (e : F x),
                       Ident (transport G p (u x e))
                             (u y (transport F p e))
         in let
           base : H x (ident_unit x)
             := fun (e : F x) => ident_unit (u x e)
         in
           ident_induction x H base.

Arguments transport_map {X} F G u {x y} p e.
(* endfrag *)

(* End of file *)
