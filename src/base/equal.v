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

Arguments equal_associative {X w x y z} p q r.
(* endfrag *)

(* begfrag:smege15s *)
Definition equal_compose_left_equal
  : forall (X : Type) (x y : X) (p p' : Equal x y),
      Equal p p'
        -> forall (z : X) (q : Equal y z),
             Equal (equal_compose p q) (equal_compose p' q)
  := fun (X : Type)
         (x y : X)
         (p p' : Equal x y)
         (u : Equal p p')
         (z : X)
         (q : Equal y z)
       =>
         let
           F : forall (i : Equal x y), Equal p i -> Type
             := fun (i  : Equal x y)
                  => constant_function (Equal (equal_compose p q)
                                              (equal_compose i q))
         in let
           base : F p (reflexive p)
             := reflexive (equal_compose p q)
         in
           equal_induction p F base p' u.

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
  := fun (X : Type)
         (x y : X)
         (p : Equal x y)
         (z : X)
         (q q' : Equal y z)
         (v : Equal q q')
       =>
         let
           F : forall (j : Equal y z), Equal q j -> Type
             := fun (j  : Equal y z)
                  => constant_function (Equal (equal_compose p q)
                                              (equal_compose p j))
         in let
           base : F q (reflexive q)
             := reflexive (equal_compose p q)
         in
           equal_induction q F base q' v.

Arguments equal_compose_right_equal {X x y} p {z q q'} _.
(* endfrag *)

(* begfrag:npsmi0d4 *)
Definition equal_compose_equal
  : forall (X : Type)
           (x y z : X)
           (p p' : Equal x y)
           (q q' : Equal y z),
      Equal p p' -> Equal q q'
        -> Equal (equal_compose p q) (equal_compose p' q')
  := fun (X : Type)
         (x y z : X)
         (p p' : Equal x y)
         (q q' : Equal y z)
         (u : Equal p p')
         (v : Equal q q')
       =>
         let
           e : Equal (equal_compose p q) (equal_compose p' q)
             := equal_compose_left_equal u q
         in let
           f : Equal (equal_compose p' q) (equal_compose p' q')
             := equal_compose_right_equal p' v
         in
           equal_compose e f.

Arguments equal_compose_equal {X x y z p p' q q'} _ _.
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

(* ================================================================ *)
(** ** Cancellation laws                                            *)
(* ================================================================ *)

(* begfrag:omtjvrai *)
Definition equal_left_cancel
  : forall (X : Type) (x y z : X) (p : Equal x y) (q q' : Equal y z),
      Equal (equal_compose p q) (equal_compose p q') -> Equal q q'
  := fun (X : Type) (x y z : X) (p : Equal x y) (q q' : Equal y z)
       =>
         let
           F : forall (a : X), Equal x a -> Type
             := fun (a : X) (i : Equal x a)
                  => forall (j j' :  Equal a z),
                       Equal (equal_compose i j) (equal_compose i j')
                         -> Equal j j'
         in let
           base : F x (reflexive x)
             := fun (j j' : Equal x z)
                  => @identity_function (Equal j j')
         in let
           inductive : forall (a : X) (i : Equal x a), F a i
             := equal_induction x F base
         in
           inductive y p q q'.

Arguments equal_left_cancel {X x y z} p q q' _.
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
         (p p' : Equal x y)
         (u : Equal p p')
         (z : X)
         (q q' : Equal y z)
         (e : Equal (equal_compose p q) (equal_compose p' q'))
       =>
         let
           e1 : Equal (equal_compose p q') (equal_compose p' q')
              := equal_compose_left_equal u q'
         in let
           e2 : Equal (equal_compose p q) (equal_compose p q')
              := equal_compose e (equal_inverse e1)
         in
           equal_left_cancel p q q' e2.

Arguments equal_left_remove {X x y p p'} _ {z} q q' _.
(* endfrag *)

(* begfrag:8gh9140h *)
Definition equal_right_cancel
  : forall (X : Type) (x y z : X) (p p' : Equal x y) (q : Equal y z),
      Equal (equal_compose p q) (equal_compose p' q) -> Equal p p'
  := fun (X : Type) (x y z : X) (p p' : Equal x y) (q : Equal y z)
       =>
         let
           F : forall (a : X), Equal y a -> Type
             := fun (a : X) (j : Equal y a)
                  => forall (i i' :  Equal x y),
                       Equal (equal_compose i j) (equal_compose i' j)
                         -> Equal i i'
         in let
           base : F y (reflexive y)
             := fun (i i' : Equal x y)
                    (u : Equal (equal_compose i (reflexive y))
                               (equal_compose i' (reflexive y)))
                  =>
                    let
                      e1 : Equal i (equal_compose i (reflexive y))
                         := equal_right_unit i
                    in let
                      e2 : Equal (equal_compose i' (reflexive y)) i'
                         := equal_inverse (equal_right_unit i')
                    in
                      equal_compose (equal_compose e1 u) e2
         in let
           inductive : forall (a : X) (j : Equal y a), F a j
             := equal_induction y F base
         in
           inductive z q p p'.

Arguments equal_right_cancel {X x y z} p p' q _.
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
         (q q' : Equal y z)
         (v : Equal q q')
         (e : Equal (equal_compose p q) (equal_compose p' q'))
       =>
         let
           e1 : Equal (equal_compose p' q) (equal_compose p' q')
              := equal_compose_right_equal p' v
         in let
           e2 : Equal (equal_compose p q) (equal_compose p' q)
              := equal_compose e (equal_inverse e1)
         in
           equal_right_cancel p p' q e2.

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
         (x y : X)
         (p : Equal x y)
         (q : Equal y y)
         (u : Equal p (equal_compose p q))
       =>
         let
           e : Equal p (equal_compose p (reflexive y))
             := equal_right_unit p
         in let
           f : Equal (equal_compose p (reflexive y))
                     (equal_compose p q)
             := equal_compose (equal_inverse e) u
         in
           equal_left_cancel p (reflexive y) q f.

Arguments equal_right_unit_unique {X x y p} q _.
(* endfrag *)

(* End of file *)
