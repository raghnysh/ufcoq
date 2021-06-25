(* Basic constructions with equality types *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.

(* ================================================================ *)
(** ** The composition of equalities                                *)
(* ================================================================ *)

(* begfrag:equal-compose *)
Definition equal_compose
  : forall (X : Type) (x y z : X), Equal x y -> Equal y z -> Equal x z
  := fun (X : Type)
         (x y z : X)
       => let F : X -> Type := fun (a : X) => Equal a z
          in transport_inverse F.
Arguments equal_compose {X x y z} _ _.
(* endfrag *)

(* begfrag:equal-compose-left-unit *)
Example _equal_compose_left_unit
  : forall (X : Type) (x y : X) (p : Equal x y),
      Equal p (equal_compose (reflexive x) p)
  := fun (X : Type) (x y : X) (p : Equal x y) => reflexive p.
(* endfrag *)

(* begfrag:equal-compose-right-unit *)
Definition equal_compose_right_unit
  : forall (X : Type) (x y : X) (p : Equal x y),
      Equal p (equal_compose p (reflexive y))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (a : X), Equal x a -> Type
             := fun (a : X) (e : Equal x a)
                  => Equal e (equal_compose e (reflexive a))
         in let
           base : F x (reflexive x) := reflexive (reflexive x)
         in
           equal_induction x F base.

Arguments equal_compose_right_unit {X x y} p.
(* endfrag *)

(* begfrag:equal-compose-associative *)
Definition equal_compose_associative
  : forall (X : Type)
           (w x y z : X)
           (p : Equal w x)
           (q : Equal x y)
           (r : Equal y z),
      Equal (equal_compose (equal_compose p q) r)
            (equal_compose p (equal_compose q r))
  := fun (X : Type)
         (w x y z : X)
         (p : Equal w x)
         (q : Equal x y)
         (r : Equal y z)
       =>
         let
           F : forall (a : X), Equal w a -> Type
             := fun (a : X) (i : Equal w a)
                  => forall (j : Equal a y),
                       Equal (equal_compose (equal_compose i j) r)
                             (equal_compose i (equal_compose j r))
         in let
           base : F w (reflexive w)
             := fun (j : Equal w y)
                  => reflexive (equal_compose j r)
         in let
           inductive : forall (a : X) (i : Equal w a), F a i
             := equal_induction w F base
         in
           inductive x p q.

Arguments equal_compose_associative {X w x y z} p q r.
(* endfrag *)

(* ================================================================ *)
(** ** The inverse of an equality                                   *)
(* ================================================================ *)

(* begfrag:equal-inverse *)
Definition equal_inverse
  : forall (X : Type) (x y : X), Equal x y -> Equal y x
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) => constant_function (Equal y x)
         in let
           base : F x (reflexive x) := reflexive x
         in
           equal_induction x F base.

Arguments equal_inverse {X x y} _.
(* endfrag *)

(* begfrag:equal-inverse-reflexive *)
Example _equal_inverse_reflexive
  : forall (X : Type) (x : X),
      Equal (reflexive x) (equal_inverse (reflexive x))
  := fun (X : Type) (x : X) => reflexive (reflexive x).
(* endfrag *)

(* begfrag:equal-left-inverse *)
Definition equal_left_inverse
  : forall (X : Type) (x y : X) (p : Equal x y),
      Equal (reflexive y) (equal_compose (equal_inverse p) p)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                  => Equal (reflexive y)
                           (equal_compose (equal_inverse p) p)
         in let
           base : F x (reflexive x) := reflexive (reflexive x)
         in
           equal_induction x F base.

Arguments equal_left_inverse {X x y} p.
(* endfrag *)

(* begfrag:equal-right-inverse *)
Definition equal_right_inverse
  : forall (X : Type) (x y : X) (p : Equal x y),
      Equal (reflexive x) (equal_compose p (equal_inverse p))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                  => Equal (reflexive x)
                           (equal_compose p (equal_inverse p))
         in let
           base : F x (reflexive x) := reflexive (reflexive x)
         in
           equal_induction x F base.

Arguments equal_right_inverse {X x y} p.
(* endfrag *)

(* ================================================================ *)
(** ** The map between equalities that is induced by a function     *)
(* ================================================================ *)

(* begfrag:equal-map *)
Definition equal_map
  : forall (X Y : Type) (f : X -> Y) (x x' : X),
      Equal x x' -> Equal (f x) (f x')
  := fun (X Y : Type) (f : X -> Y) (x : X)
       =>
         let
           F : forall (x' : X), Equal x x' -> Type
             := fun (x' : X) => constant_function (Equal (f x) (f x'))
         in let
           base : F x (reflexive x) := reflexive (f x)
         in
           equal_induction x F base.

Arguments equal_map {X Y} f {x x'} _.
(* endfrag *)

(* begfrag:equal-map-unital *)
Example _equal_map_unital
  : forall (X Y : Type) (f : X -> Y) (x : X),
      Equal (reflexive (f x)) (equal_map f (reflexive x))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       => reflexive (reflexive (f x)).
(* endfrag *)

(* begfrag:equal-map-multiplicative *)
Definition equal_map_multiplicative
  : forall (X Y : Type)
           (f : X -> Y)
           (x1 x2 x3 : X)
           (p : Equal x1 x2)
           (q : Equal x2 x3),
      Equal (equal_map f (equal_compose p q))
            (equal_compose (equal_map f p) (equal_map f q))
  := fun (X Y : Type) (f : X -> Y) (x1 x2 x3 : X)
       =>
         let
           F : forall (a : X), Equal x1 a -> Type
             := fun (a : X) (p : Equal x1 a)
                  => forall (q : Equal a x3),
                       Equal (equal_map f (equal_compose p q))
                             (equal_compose (equal_map f p) (equal_map f q))
         in let
           base : F x1 (reflexive x1)
             := fun (q : Equal x1 x3)
                  => reflexive (equal_map f q)
         in
           equal_induction x1 F base x2.

Arguments equal_map_multiplicative {X Y} f {x1 x2 x3} p q.
(* endfrag *)

(* begfrag:equal-map-inverse *)
Definition equal_map_inverse
  : forall (X Y : Type) (f : X -> Y) (x x' : X) (p : Equal x x'),
      Equal (equal_map f (equal_inverse p))
            (equal_inverse (equal_map f p))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       =>
         let
           F : forall (x' : X), Equal x x' -> Type
             := fun (x' : X) (p : Equal x x')
                  => Equal (equal_map f (equal_inverse p))
                           (equal_inverse (equal_map f p))
         in let
           base : F x (reflexive x) := reflexive (reflexive (f x))
         in
           equal_induction x F base.

Arguments equal_map_inverse {X Y} f {x x'} p.
(* endfrag *)

(* End of file *)
