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
(** ** Transport on the false type                                  *)
(* ================================================================ *)

(* begfrag:e4llc30a *)
Definition false_double_induction
  : forall (F : False -> False -> Type) (x y : False), F x y
  := fun (F : False -> False -> Type)
       => false_induction
            (fun (x : False) => forall (y : False), F x y).
(* endfrag *)

(* begfrag:535lvwe9 *)
Definition false_double_elident
  : forall (F : False -> False -> Type)
           (f g : forall (x y : False), F x y)
           (x y : False),
      Ident (f x y) (g x y)
  := fun (F : False -> False -> Type)
         (f g : forall (x y : False), F x y)
       => false_double_induction
            (fun (x y : False) => Ident (f x y) (g x y)).

Arguments false_double_elident {F} f g x y.
(* endfrag *)

(* begfrag:ahm8ghsp *)
Definition transport_false
  : forall (F : False -> Type) (x y : False),
      Ident (fun (p : Ident x y) => (transport F p))
            (false_double_induction
               (fun (a b : False) => Ident a b -> F a -> F b)
               x y)
  := fun (F : False -> Type)
       => false_double_elident
            (@transport False F)
            (false_double_induction
               (fun (a b : False) => Ident a b -> F a -> F b)).
(* endfrag *)

(* ================================================================ *)
(** ** Transport on the true type                                   *)
(* ================================================================ *)

(* begfrag:won8oy5d *)
Definition true_double_induction
  : forall (F : True -> True -> Type),
      F only only -> forall (x y : True), F x y
  := fun (F : True -> True -> Type) (u : F only only)
       => true_induction (fun (x : True) => forall (y : True), F x y)
                         (true_induction (fun (y : True) => F only y)
                                         u).
(* endfrag *)

(* begfrag:xlmz2ube *)
Definition true_double_elident
  : forall (F : True -> True -> Type)
           (f g : forall (x y : True), F x y),
      Ident (f only only) (g only only)
        -> forall (x y : True), Ident (f x y) (g x y)
  := fun (F : True -> True -> Type)
         (f g : forall (x y : True), F x y)
       => true_double_induction
            (fun (x y : True) => Ident (f x y) (g x y)).

Arguments true_double_elident {F} f g _ _ _.
(* endfrag *)

(* begfrag:sdp39fus *)
Definition transport_true
  : forall (F : True -> Type) (x y : True),
        Ident (fun (p : Ident x y) => transport F p)
              (true_double_induction
                 (fun (a b : True) => Ident a b -> F a -> F b)
                 (fun (p : Ident only only) => transport F p)
                 x y)
  := fun (F : True -> Type)
       => true_double_elident
            (@transport True F)
            (true_double_induction
               (fun (a b : True) => Ident a b -> F a -> F b)
               (fun (p : Ident only only) => transport F p))
            (ident_unit (fun (p : Ident only only) => transport F p)).
(* endfrag *)

(* ================================================================ *)
(** ** Transport on the boolean type                                *)
(* ================================================================ *)

(* begfrag:96eavgp6 *)
Definition boolean_double_induction
  : forall (F : Boolean -> Boolean -> Type),
      F yes yes -> F yes no -> F no yes -> F no no
        -> forall (x y : Boolean), F x y
  := fun (F : Boolean -> Boolean -> Type)
         (s : F yes yes) (t : F yes no) (u : F no yes) (v : F no no)
       => boolean_induction
            (fun (x : Boolean) => forall (y : Boolean), F x y)
            (boolean_induction (fun (y : Boolean) => F yes y) s t)
            (boolean_induction (fun (y : Boolean) => F no y) u v).
(* endfrag *)

(* begfrag:dnd8qln5 *)
Definition boolean_double_elident
  : forall (F : Boolean -> Boolean -> Type)
           (f g : forall (x y : Boolean), F x y),
      Ident (f yes yes) (g yes yes) -> Ident (f yes no) (g yes no)
        -> Ident (f no yes) (g no yes) -> Ident (f no no) (g no no)
          -> forall (x y : Boolean), Ident (f x y) (g x y)
  := fun (F : Boolean -> Boolean -> Type)
         (f g : forall (x y : Boolean), F x y)
       => boolean_double_induction
            (fun (x y : Boolean) => Ident (f x y) (g x y)).

Arguments boolean_double_elident {F} f g _ _ _ _ x y.
(* endfrag *)

(* begfrag:r68r8epq *)
Definition transport_boolean
  : forall (F : Boolean -> Type) (x y : Boolean),
      Ident (fun (p : Ident x y) => transport F p)
            (boolean_double_induction
               (fun (a b : Boolean) => Ident a b -> F a -> F b)
               (fun (p : Ident yes yes) => transport F p)
               (fun (p : Ident yes no) => transport F p)
               (fun (p : Ident no yes) => transport F p)
               (fun (p : Ident no no) => transport F p)
               x y)
  := fun (F : Boolean -> Type)
       => boolean_double_elident
            (@transport Boolean F)
            (boolean_double_induction
               (fun (a b : Boolean) => Ident a b -> F a -> F b)
               (fun (p : Ident yes yes) => transport F p)
               (fun (p : Ident yes no) => transport F p)
               (fun (p : Ident no yes) => transport F p)
               (fun (p : Ident no no) => transport F p))
            (ident_unit (fun (p : Ident yes yes) => transport F p))
            (ident_unit (fun (p : Ident yes no) => transport F p))
            (ident_unit (fun (p : Ident no yes) => transport F p))
            (ident_unit (fun (p : Ident no no) => transport F p)).
(* endfrag *)

(* End of file *)
