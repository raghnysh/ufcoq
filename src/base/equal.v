(* Basic constructions with equality types *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:e82fgb1k *)
Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.
(* endfrag *)

(* ================================================================ *)
(** ** The composition of equalities                                *)
(* ================================================================ *)

(* begfrag:ybsrqsg4 *)
Definition equal_compose
  : forall (X : Type) (x y z : X), Equal x y -> Equal y z -> Equal x z
  := fun (X : Type)
         (x y z : X)
       => let F : X -> Type := fun (a : X) => Equal a z
          in transport_inverse F.

Arguments equal_compose {X x y z} _ _.
(* endfrag *)

(* begfrag:ky5unwbq *)
Example _equal_left_unit
  : forall (X : Type) (x y : X) (p : Equal x y),
      Equal p (equal_compose (reflexive x) p)
  := fun (X : Type) (x y : X) (p : Equal x y) => reflexive p.
(* endfrag *)

(* begfrag:afizq40q *)
Definition equal_right_unit
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

Arguments equal_right_unit {X x y} p.
(* endfrag *)

(* begfrag:qj3cqa2b *)
Definition equal_associative
  : forall (X : Type)
           (w x: X)
           (p : Equal w x)
           (y : X)
           (q : Equal x y)
           (z : X)
           (r : Equal y z),
      Equal (equal_compose (equal_compose p q) r)
            (equal_compose p (equal_compose q r))
  := fun (X : Type) (w : X)
       =>
         let
           F : forall (x : X), Equal w x -> Type
             := fun (x : X) (p : Equal w x)
                  => forall (y : X) (q : Equal x y) (z : X) (r : Equal y z),
                       Equal (equal_compose (equal_compose p q) r)
                             (equal_compose p (equal_compose q r))
         in let
           base : F w (reflexive w)
             := fun (y : X) (q : Equal w y) (z : X) (r : Equal y z)
                  => reflexive (equal_compose q r)
         in
           equal_induction w F base.

Arguments equal_associative {X w x} p {y} q {z} r.
(* endfrag *)

(* begfrag:smege15s *)
Definition equal_compose_left_equal
  : forall (X : Type) (x y : X) (p p' : Equal x y),
      Equal p p'
        -> forall (z : X) (q : Equal y z),
             Equal (equal_compose p q) (equal_compose p' q)
  := fun (X : Type) (x y : X) (p : Equal x y)
       =>
         let
           F : forall (p' : Equal x y), Equal p p' -> Type
             := fun (p'  : Equal x y)
                  => constant_function
                       (forall (z : X) (q : Equal y z),
                          Equal (equal_compose p q)
                                (equal_compose p' q))
         in let
           base : F p (reflexive p)
             := fun (z : X) (q : Equal y z)
                  => reflexive (equal_compose p q)
         in
           equal_induction p F base.

Arguments equal_compose_left_equal {X x y p p'} _ {z} q.
(* endfrag *)

(* begfrag:g6ql88po *)
Definition equal_compose_right_equal
  : forall (X : Type)
           (x y : X)
           (p : Equal x y)
           (z : X)
           (q q' : Equal y z),
      Equal q q' -> Equal (equal_compose p q) (equal_compose p q')
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                  => forall (z : X) (q q' : Equal y z),
                       Equal q q'
                         -> Equal (equal_compose p q)
                                  (equal_compose p q')
         in let
           base : F x (reflexive x)
             := fun (z : X) (q q' : Equal x z)
                  => @identity_function (Equal q q')
         in
           equal_induction x F base.

Arguments equal_compose_right_equal {X x y} p {z q q'} _.
(* endfrag *)

(* begfrag:npsmi0d4 *)
Definition equal_compose_equal
  : forall (X : Type)
           (x y : X)
           (p p' : Equal x y),
      Equal p p'
        -> forall (z : X) (q q' : Equal y z),
             Equal q q'
               -> Equal (equal_compose p q) (equal_compose p' q')
  := fun (X : Type)
         (x y : X)
         (p : Equal x y)
       =>
         let
           F : forall (p' : Equal x y), Equal p p' -> Type
             := fun (p' : Equal x y)
                  => constant_function
                       (forall (z : X) (q q' : Equal y z),
                          Equal q q'
                            -> Equal (equal_compose p q)
                                     (equal_compose p' q'))
         in let
           base: F p (reflexive p)
             := @equal_compose_right_equal X x y p
         in
           equal_induction p F base.

Arguments equal_compose_equal {X x y p p'} _ {z q q'} _.
(* endfrag *)

(* ================================================================ *)
(** ** The inverse of an equality                                   *)
(* ================================================================ *)

(* begfrag:37wczvy0 *)
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

(* begfrag:fehutg63 *)
Example _equal_inverse_reflexive
  : forall (X : Type) (x : X),
      Equal (reflexive x) (equal_inverse (reflexive x))
  := fun (X : Type) (x : X) => reflexive (reflexive x).
(* endfrag *)

(* begfrag:czd5dw60 *)
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

(* begfrag:eay5nxer *)
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

(* begfrag:lxgjdap3 *)
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

(* begfrag:udxkkzqg *)
Example _equal_map_unital
  : forall (X Y : Type) (f : X -> Y) (x : X),
      Equal (reflexive (f x)) (equal_map f (reflexive x))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       => reflexive (reflexive (f x)).
(* endfrag *)

(* begfrag:bul2i30n *)
Definition equal_map_multiplicative
  : forall (X Y : Type)
           (f : X -> Y)
           (x1 x2 : X)
           (p : Equal x1 x2)
           (x3 : X)
           (q : Equal x2 x3),
      Equal (equal_map f (equal_compose p q))
            (equal_compose (equal_map f p) (equal_map f q))
  := fun (X Y : Type) (f : X -> Y) (x1 : X)
       =>
         let
           F : forall (x2 : X), Equal x1 x2 -> Type
             := fun (x2 : X) (p : Equal x1 x2)
                  => forall (x3 : X) (q : Equal x2 x3),
                       Equal (equal_map f (equal_compose p q))
                             (equal_compose (equal_map f p) (equal_map f q))
         in let
           base : F x1 (reflexive x1)
             := fun (x3 : X) (q : Equal x1 x3)
                  => reflexive (equal_map f q)
         in
           equal_induction x1 F base.

Arguments equal_map_multiplicative {X Y} f {x1 x2} p {x3} q.
(* endfrag *)

(* begfrag:5e7zp56e *)
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

(* begfrag:qs50e5ab *)
Definition equal_map_equal
  : forall (X Y : Type) (f : X -> Y) (x y : X) (p q : Equal x y),
      Equal p q -> Equal (equal_map f p) (equal_map f q)
  := fun (X Y : Type) (f : X -> Y) (x y : X) (p : Equal x y)
       =>
         let
           F : forall (q : Equal x y), Equal p q -> Type
             := fun (q : Equal x y)
                  => constant_function (Equal (equal_map f p)
                                              (equal_map f q))
         in let
           base : F p (reflexive p)
             := reflexive (equal_map f p)
         in
           equal_induction p F base.

Arguments equal_map_equal {X Y} f {x y p q} _.
(* endfrag *)

(* ================================================================ *)
(** ** Functoriality of the induced map                             *)
(* ================================================================ *)

(* begfrag:rsfbjxq8 *)
Definition equal_map_identity_function
  : forall (X : Type) (x x' : X) (p : Equal x x'),
      Equal p (equal_map (@identity_function X) p)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (x' : X), Equal x x' -> Type
             := fun (x' : X) (p : Equal x x')
                  => Equal p (equal_map (@identity_function X) p)
         in let
           base : F x (reflexive x) := reflexive (reflexive x)
         in
           equal_induction x F base.

Arguments equal_map_identity_function {X x x'} p.
(* endfrag *)

(* begfrag:tm7axffm *)
Definition equal_map_function_compose
  : forall (X Y Z : Type)
           (g : Y -> Z)
           (f : X -> Y)
           (x x' : X)
           (p : Equal x x'),
      Equal (equal_map (function_compose g f) p)
            (equal_map g (equal_map f p))
  := fun (X Y Z : Type)
         (g : Y -> Z)
         (f : X -> Y)
         (x : X)
       =>
         let
           F : forall (x' : X), Equal x x' -> Type
             := fun (x' : X) (p : Equal x x')
                  => Equal (equal_map (function_compose g f) p)
                           (equal_map g (equal_map f p))
         in let
           base : F x (reflexive x) := reflexive (reflexive (g (f x)))
         in
           equal_induction x F base.

Arguments equal_map_function_compose {X Y Z} g f {x x'} p.
(* endfrag *)

(* begfrag:t9j8usog *)
Definition equal_map_constant_function
  : forall (X Y : Type) (y : Y) (x x' : X) (p : Equal x x'),
      Equal (reflexive y) (equal_map (@constant_function X Y y) p)
  := fun (X Y : Type) (y : Y) (x : X)
       =>
         let
           F : forall (x' : X), Equal x x' -> Type
             := fun (x' : X) (p : Equal x x')
                  => Equal (reflexive y)
                           (equal_map (@constant_function X Y y) p)
         in let
           base : F x (reflexive x) := reflexive (reflexive y)
         in
           equal_induction x F base.

Arguments equal_map_constant_function {X Y} y {x x'} p.
(* endfrag *)

(* ================================================================ *)
(** ** Cancellation laws                                            *)
(* ================================================================ *)

(* begfrag:omtjvrai *)
Definition equal_left_cancel
  : forall (X : Type)
           (x y : X)
           (p : Equal x y)
           (z : X)
           (q q' : Equal y z),
      Equal (equal_compose p q) (equal_compose p q') -> Equal q q'
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                  => forall (z : X) (q q' :  Equal y z),
                       Equal (equal_compose p q) (equal_compose p q')
                         -> Equal q q'
         in let
           base : F x (reflexive x)
             := fun (z : X) (q q' : Equal x z)
                  => @identity_function (Equal q q')
         in
           equal_induction x F base.

Arguments equal_left_cancel {X x y} p {z} q q' _.
(* endfrag *)

(* begfrag:865g4mt7 *)
Definition equal_left_remove
  : forall (X : Type)
           (x y : X)
           (p p' : Equal x y),
      Equal p p'
        -> forall (z : X) (q q' : Equal y z),
             Equal (equal_compose p q) (equal_compose p' q')
               -> Equal q q'
  := fun (X : Type)
         (x y : X)
         (p : Equal x y)
       =>
         let
           F : forall (p' : Equal x y), Equal p p' -> Type
             := fun (p' : Equal x y)
                  => constant_function
                       (forall (z : X) (q q' : Equal y z),
                          Equal (equal_compose p q)
                                (equal_compose p' q')
                            -> Equal q q')
         in let
           base : F p (reflexive p)
             := fun (z : X) (q q' : Equal y z)
                  => equal_left_cancel p q q'
         in
           equal_induction p F base.

Arguments equal_left_remove {X x y p p'} _ {z} q q' _.
(* endfrag *)

(* begfrag:8gh9140h *)
Definition equal_right_cancel
  : forall (X : Type)
           (x y : X)
           (p p' : Equal x y)
           (z : X)
           (q : Equal y z),
      Equal (equal_compose p q) (equal_compose p' q) -> Equal p p'
  := fun (X : Type) (x y : X) (p p' : Equal x y)
       =>
         let
           F : forall (z : X), Equal y z -> Type
             := fun (z : X) (q : Equal y z)
                  => Equal (equal_compose p q) (equal_compose p' q)
                       -> Equal p p'
         in let
           base : F y (reflexive y)
             := fun (u : Equal (equal_compose p (reflexive y))
                               (equal_compose p' (reflexive y)))
                  =>
                    let
                      e1 : Equal p (equal_compose p (reflexive y))
                         := equal_right_unit p
                    in let
                      e2 : Equal (equal_compose p' (reflexive y)) p'
                         := equal_inverse (equal_right_unit p')
                    in
                      equal_compose (equal_compose e1 u) e2
         in
           equal_induction y F base.

Arguments equal_right_cancel {X x y} p p' {z} q _.
(* endfrag *)

(* begfrag:sqhuo1hf *)
Definition equal_right_remove
  : forall (X : Type)
           (x y : X)
           (p p' : Equal x y)
           (z : X)
           (q q' : Equal y z),
      Equal q q'
        -> Equal (equal_compose p q) (equal_compose p' q')
          -> Equal p p'
  := fun (X : Type)
         (x y : X)
         (p p' : Equal x y)
         (z : X)
         (q : Equal y z)
       =>
         let
           F : forall (q' : Equal y z), Equal q q' -> Type
             := fun (q' : Equal y z)
                  =>  constant_function
                        (Equal (equal_compose p q)
                               (equal_compose p' q')
                           -> Equal p p')
         in let
           base : F q (reflexive q)
             := equal_right_cancel p p' q
         in
           equal_induction q F base.

Arguments equal_right_remove {X x y} p p' {z} {q q'} _ _.
(* endfrag *)

(* ================================================================ *)
(** ** Uniqueness of units                                          *)
(* ================================================================ *)

(* begfrag:x71kqflr *)
Definition equal_left_unit_unique
  : forall (X : Type) (x y : X) (p : Equal x x) (q : Equal x y),
      Equal q (equal_compose p q) -> Equal (reflexive x) p
  := fun (X : Type) (x y : X) (p : Equal x x) (q : Equal x y)
       => equal_right_cancel (reflexive x) p q.

Arguments equal_left_unit_unique {X x y} p {q} _.
(* endfrag *)

(* begfrag:m1jqzny4 *)
Definition equal_right_unit_unique
  : forall (X : Type) (x y : X) (p : Equal x y) (q : Equal y y),
      Equal p (equal_compose p q) -> Equal (reflexive y) q
  := fun (X : Type)
         (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                  => forall (q : Equal y y),
                       Equal p (equal_compose p q)
                         -> Equal (reflexive y) q
         in let
           base : F x (reflexive x)
             := fun (q : Equal x x)
                  => @identity_function (Equal (reflexive x) q)
         in
           equal_induction x F base.

Arguments equal_right_unit_unique {X x y p} q _.
(* endfrag *)

(* ================================================================ *)
(** ** Uniqueness of inverses                                       *)
(* ================================================================ *)

(* begfrag:5f147sym *)
Definition equal_left_inverse_unique
  : forall (X : Type) (x y : X) (p : Equal x y) (q : Equal y x),
      Equal (equal_compose p q) (reflexive x)
        -> Equal p (equal_inverse q)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                  => forall (q : Equal y x),
                       Equal (equal_compose p q) (reflexive x)
                         -> Equal p (equal_inverse q)
         in let
           base : F x (reflexive x)
             := fun (q : Equal x x) (e : Equal q (reflexive x))
                  => equal_inverse (equal_map equal_inverse e)
         in
           equal_induction x F base.

Arguments equal_left_inverse_unique {X x y} p q _.
(* endfrag *)

(* begfrag:bwldujz3 *)
Definition equal_right_inverse_unique
  : forall (X : Type) (x y : X) (p : Equal x y) (q : Equal y x),
      Equal (equal_compose p q) (reflexive x)
        -> Equal q (equal_inverse p)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                  => forall (q : Equal y x),
                       Equal (equal_compose p q) (reflexive x)
                         -> Equal q (equal_inverse p)
         in let
           base : F x (reflexive x)
             := fun (q : Equal x x)
                  => @identity_function (Equal q (reflexive x))
         in
           equal_induction x F base.

Arguments equal_right_inverse_unique {X x y} p q _.
(* endfrag *)

(* ================================================================ *)
(** ** Antimultiplicativity of inversion                           *)
(* ================================================================ *)

(* begfrag:vl4svtgg *)
Definition equal_inverse_antimultiplicative
  : forall (X : Type)
           (x y : X)
           (p : Equal x y)
           (z : X)
           (q : Equal y z),
      Equal (equal_inverse (equal_compose p q))
            (equal_compose (equal_inverse q) (equal_inverse p))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                  => forall (z : X) (q : Equal y z),
                       Equal (equal_inverse (equal_compose p q))
                             (equal_compose (equal_inverse q)
                                            (equal_inverse p))
         in let
           base : F x (reflexive x)
             := fun (z : X) (q : Equal x z)
                  => equal_right_unit (equal_inverse q)
         in
           equal_induction x F base.

Arguments equal_inverse_antimultiplicative {X x y} p {z} q.
(* endfrag *)

(* ================================================================ *)
(** ** Involutivity of inversion                                    *)
(* ================================================================ *)

(* begfrag:mmbhn8r1 *)
Definition equal_inverse_involutive
  : forall (X : Type) (x y : X) (p : Equal x y),
      Equal p (equal_inverse (equal_inverse p))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                  => Equal p (equal_inverse (equal_inverse p))
         in let
           base : F x (reflexive x)
             := reflexive (reflexive x)
         in
           equal_induction x F base.

Arguments equal_inverse_involutive {X x y} p.
(* endfrag *)

(* ================================================================ *)
(** ** Putting and removing an inverse                              *)
(* ================================================================ *)

(* begfrag:zgnf348j *)
Definition equal_put_inverse
  : forall (X : Type) (x y : X) (p q : Equal x y),
      Equal p q -> Equal (equal_inverse p) (equal_inverse q)
  := fun (X : Type) (x y : X) (p : Equal x y)
     =>
       let
         F : forall (q : Equal x y), Equal p q -> Type
           := fun (q : Equal x y)
                => constant_function (Equal (equal_inverse p)
                                            (equal_inverse q))
       in let
         base : F p (reflexive p)
           := reflexive (equal_inverse p)
       in
         equal_induction p F base.

Arguments equal_put_inverse {X x y p q} _.
(* endfrag *)

(* begfrag:93zoshti *)
Definition equal_remove_inverse
  : forall (X : Type) (x y : X) (p q : Equal x y),
      Equal (equal_inverse p) (equal_inverse q) -> Equal p q
  := fun (X : Type)
         (x y : X)
         (p q : Equal x y)
         (e : Equal (equal_inverse p) (equal_inverse q))
       =>
         let
           u1 : Equal p (equal_inverse (equal_inverse p))
              := equal_inverse_involutive p
         in let
           u2 : Equal (equal_inverse (equal_inverse p))
                      (equal_inverse (equal_inverse q))
              := equal_put_inverse e
         in let
           u3 : Equal (equal_inverse (equal_inverse q)) q
              := equal_inverse (equal_inverse_involutive q)
         in
           equal_compose (equal_compose u1 u2) u3.

Arguments equal_remove_inverse {X x y} p q _.
(* endfrag *)

(* ================================================================ *)
(** ** Moving factors across an equality                            *)
(* ================================================================ *)

(* begfrag:m4s5b57h *)
Definition equal_move_prefix_right
  : forall (X : Type)
           (x y : X)
           (p : Equal x y)
           (z : X)
           (q : Equal y z)
           (r : Equal x z),
      Equal (equal_compose p q) r
        -> Equal q (equal_compose (equal_inverse p) r)
  := fun (X : Type)
         (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                => forall (z : X) (q : Equal y z) (r : Equal x z),
                     Equal (equal_compose p q) r
                       -> Equal q (equal_compose (equal_inverse p) r)
         in let
           base : F x (reflexive x)
             := fun (z : X) (q : Equal x z) (r : Equal x z)
                  => @identity_function (Equal q r)
         in
           equal_induction x F base.

Arguments equal_move_prefix_right {X x y} p {z} q {r} _.
(* endfrag *)

(* begfrag:62xaggnq *)
Definition equal_move_prefix_left
  : forall (X : Type)
           (x y : X)
           (p : Equal x y)
           (z : X)
           (q : Equal y z)
           (r : Equal x z),
      Equal r (equal_compose p q)
        -> Equal (equal_compose (equal_inverse p) r) q
  := fun (X : Type)
         (x : X)
       =>
         let
           F : forall (y : X), Equal x y -> Type
             := fun (y : X) (p : Equal x y)
                => forall (z : X) (q : Equal y z) (r : Equal x z),
                     Equal r (equal_compose p q)
                       -> Equal (equal_compose (equal_inverse p) r) q
         in let
           base : F x (reflexive x)
             := fun (z : X) (q : Equal x z) (r : Equal x z)
                  => @identity_function (Equal r q)
         in
           equal_induction x F base.

Arguments equal_move_prefix_left {X x y} p {z} q {r} _.
(* endfrag *)

(* begfrag:10g8q8xv *)
Definition equal_move_suffix_right
  : forall (X : Type)
           (y z : X)
           (q : Equal y z)
           (x : X)
           (p : Equal x y)
           (r : Equal x z),
      Equal (equal_compose p q) r
        -> Equal p (equal_compose r (equal_inverse q))
  := fun (X : Type)
         (y : X)
       =>
         let
           F : forall (z : X), Equal y z -> Type
             := fun (z : X) (q : Equal y z)
                => forall (x : X) (p : Equal x y) (r : Equal x z),
                     Equal (equal_compose p q) r
                       -> Equal p (equal_compose r (equal_inverse q))
         in let
           base : F y (reflexive y)
             := fun (x : X)
                    (p : Equal x y)
                    (r : Equal x y)
                    (e : Equal (equal_compose p (reflexive y)) r)
                  =>
                    let
                      u1 : Equal p (equal_compose p (reflexive y))
                         := equal_right_unit p
                    in let
                      u2 : Equal r (equal_compose r (reflexive y))
                         := equal_right_unit r
                    in
                      equal_compose (equal_compose u1 e) u2
         in
           equal_induction y F base.

Arguments equal_move_suffix_right {X y z} q {x} p {r} _.
(* endfrag *)

(* begfrag:xz2levku *)
Definition equal_move_suffix_left
  : forall (X : Type)
           (y z : X)
           (q : Equal y z)
           (x : X)
           (p : Equal x y)
           (r : Equal x z),
      Equal r (equal_compose p q)
        -> Equal (equal_compose r (equal_inverse q)) p
  := fun (X : Type)
         (y : X)
       =>
         let
           F : forall (z : X), Equal y z -> Type
             := fun (z : X) (q : Equal y z)
                => forall (x : X) (p : Equal x y) (r : Equal x z),
                     Equal r (equal_compose p q)
                       -> Equal (equal_compose r (equal_inverse q)) p
         in let
           base : F y (reflexive y)
             := fun (x : X)
                    (p : Equal x y)
                    (r : Equal x y)
                    (e : Equal r (equal_compose p (reflexive y)))
                  =>
                    let
                      u1 : Equal (equal_compose r (reflexive y)) r
                         := equal_inverse (equal_right_unit r)
                    in let
                      u2 : Equal (equal_compose p (reflexive y)) p
                         := equal_inverse (equal_right_unit p)
                    in
                      equal_compose (equal_compose u1 e) u2
         in
           equal_induction y F base.

Arguments equal_move_suffix_left {X y z} q {x} p {r} _.
(* endfrag *)

(* End of file *)
