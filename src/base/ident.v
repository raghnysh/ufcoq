(* Basic constructions with identity types *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:e82fgb1k *)
Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.
(* endfrag *)

(* ================================================================ *)
(** ** The composition of identities                                *)
(* ================================================================ *)

(* begfrag:ybsrqsg4 *)
Definition ident_compose
  : forall (X : Type) (x y : X),
      Ident x y -> forall (z : X), Ident y z -> Ident x z
  := fun (X : Type) (x : X)
       => ident_recursion x
                          (fun (y : X) => forall (z : X),
                                            Ident y z -> Ident x z)
                          (fun (z : X) => function_unit (Ident x z)).

Arguments ident_compose {X x y} _ {z} _.
(* endfrag *)

(* begfrag:ky5unwbq *)
Example _ident_left_unit
  : forall (X : Type) (x y : X) (p : Ident x y),
      Ident p (ident_compose (ident_unit x) p)
  := fun (X : Type) (x y : X) (p : Ident x y) => ident_unit p.
(* endfrag *)

(* begfrag:afizq40q *)
Definition ident_right_unit
  : forall (X : Type) (x y : X) (p : Ident x y),
      Ident p (ident_compose p (ident_unit y))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (a : X), Ident x a -> Type
             := fun (a : X) (e : Ident x a)
                  => Ident e (ident_compose e (ident_unit a))
         in let
           base : F x (ident_unit x) := ident_unit (ident_unit x)
         in
           ident_induction x F base.

Arguments ident_right_unit {X x y} p.
(* endfrag *)

(* begfrag:qj3cqa2b *)
Definition ident_associative
  : forall (X : Type)
           (w x: X)
           (p : Ident w x)
           (y : X)
           (q : Ident x y)
           (z : X)
           (r : Ident y z),
      Ident (ident_compose (ident_compose p q) r)
            (ident_compose p (ident_compose q r))
  := fun (X : Type) (w : X)
       =>
         let
           F : forall (x : X), Ident w x -> Type
             := fun (x : X) (p : Ident w x)
                  => forall (y : X)
                            (q : Ident x y)
                            (z : X)
                            (r : Ident y z),
                       Ident (ident_compose (ident_compose p q) r)
                             (ident_compose p (ident_compose q r))
         in let
           base : F w (ident_unit w)
             := fun (y : X) (q : Ident w y) (z : X) (r : Ident y z)
                  => ident_unit (ident_compose q r)
         in
           ident_induction w F base.

Arguments ident_associative {X w x} p {y} q {z} r.
(* endfrag *)

(* ================================================================ *)
(** ** The inverse of an identity                                   *)
(* ================================================================ *)

(* begfrag:37wczvy0 *)
Definition ident_inverse
  : forall (X : Type) (x y : X), Ident x y -> Ident y x
  := fun (X : Type) (x : X)
       => ident_recursion x
                          (fun (y : X) => Ident y x)
                          (ident_unit x).

Arguments ident_inverse {X x y} _.
(* endfrag *)

(* begfrag:fehutg63 *)
Example _ident_inverse_ident_unit
  : forall (X : Type) (x : X),
      Ident (ident_unit x) (ident_inverse (ident_unit x))
  := fun (X : Type) (x : X) => ident_unit (ident_unit x).
(* endfrag *)

(* begfrag:czd5dw60 *)
Definition ident_left_inverse
  : forall (X : Type) (x y : X) (p : Ident x y),
      Ident (ident_unit y) (ident_compose (ident_inverse p) p)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => Ident (ident_unit y)
                           (ident_compose (ident_inverse p) p)
         in let
           base : F x (ident_unit x) := ident_unit (ident_unit x)
         in
           ident_induction x F base.

Arguments ident_left_inverse {X x y} p.
(* endfrag *)

(* begfrag:eay5nxer *)
Definition ident_right_inverse
  : forall (X : Type) (x y : X) (p : Ident x y),
      Ident (ident_unit x) (ident_compose p (ident_inverse p))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => Ident (ident_unit x)
                           (ident_compose p (ident_inverse p))
         in let
           base : F x (ident_unit x) := ident_unit (ident_unit x)
         in
           ident_induction x F base.

Arguments ident_right_inverse {X x y} p.
(* endfrag *)

(* ================================================================ *)
(** ** The map between identities that is induced by a function     *)
(* ================================================================ *)

(* begfrag:lxgjdap3 *)
Definition ident_map
  : forall (X Y : Type) (f : X -> Y) (x x' : X),
      Ident x x' -> Ident (f x) (f x')
  := fun (X Y : Type) (f : X -> Y) (x : X)
       => ident_recursion x
                          (fun (x' : X) => Ident (f x) (f x'))
                          (ident_unit (f x)).

Arguments ident_map {X Y} f {x x'} _.
(* endfrag *)

(* begfrag:udxkkzqg *)
Example _ident_map_unital
  : forall (X Y : Type) (f : X -> Y) (x : X),
      Ident (ident_unit (f x)) (ident_map f (ident_unit x))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       => ident_unit (ident_unit (f x)).
(* endfrag *)

(* begfrag:bul2i30n *)
Definition ident_map_multiplicative
  : forall (X Y : Type)
           (f : X -> Y)
           (x1 x2 : X)
           (p : Ident x1 x2)
           (x3 : X)
           (q : Ident x2 x3),
      Ident (ident_map f (ident_compose p q))
            (ident_compose (ident_map f p) (ident_map f q))
  := fun (X Y : Type) (f : X -> Y) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p : Ident x1 x2)
                  => forall (x3 : X) (q : Ident x2 x3),
                       Ident (ident_map f (ident_compose p q))
                             (ident_compose (ident_map f p)
                                            (ident_map f q))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X) (q : Ident x1 x3)
                  => ident_unit (ident_map f q)
         in
           ident_induction x1 F base.

Arguments ident_map_multiplicative {X Y} f {x1 x2} p {x3} q.
(* endfrag *)

(* begfrag:5e7zp56e *)
Definition ident_map_inverse
  : forall (X Y : Type) (f : X -> Y) (x x' : X) (p : Ident x x'),
      Ident (ident_map f (ident_inverse p))
            (ident_inverse (ident_map f p))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       =>
         let
           F : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => Ident (ident_map f (ident_inverse p))
                           (ident_inverse (ident_map f p))
         in let
           base : F x (ident_unit x) := ident_unit (ident_unit (f x))
         in
           ident_induction x F base.

Arguments ident_map_inverse {X Y} f {x x'} p.
(* endfrag *)

(* begfrag:oqkd01vv *)
Definition ident_map_left_inverse
  : forall (X Y : Type) (f : X -> Y) (x x' : X) (p : Ident x x'),
      Ident (ident_unit (f x'))
            (ident_compose (ident_map f (ident_inverse p))
                           (ident_map f p))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       =>
         let
           F : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => Ident (ident_unit (f x'))
                           (ident_compose
                              (ident_map f (ident_inverse p))
                              (ident_map f p))
         in let
           base : F x (ident_unit x)
             := ident_unit (ident_unit (f x))
         in
           ident_induction x F base.

Arguments ident_map_left_inverse {X Y} f {x x'} p.
(* endfrag *)

(* begfrag:4slbpngd *)
Definition ident_map_right_inverse
  : forall (X Y : Type) (f : X -> Y) (x x' : X) (p : Ident x x'),
      Ident (ident_unit (f x))
            (ident_compose (ident_map f p)
                           (ident_map f (ident_inverse p)))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       =>
         let
           F : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => Ident (ident_unit (f x))
                           (ident_compose
                              (ident_map f p)
                              (ident_map f (ident_inverse p)))
         in let
           base : F x (ident_unit x)
             := ident_unit (ident_unit (f x))
         in
           ident_induction x F base.

Arguments ident_map_right_inverse {X Y} f {x x'} p.
(* endfrag *)

(* begfrag:qs50e5ab *)
Definition ident_map_ident
  : forall (X Y : Type) (f : X -> Y) (x y : X) (p q : Ident x y),
      Ident p q -> Ident (ident_map f p) (ident_map f q)
  := fun (X Y : Type) (f : X -> Y) (x y : X) (p : Ident x y)
       => ident_recursion p
                          (fun (q : Ident x y)
                             => Ident (ident_map f p) (ident_map f q))
                          (ident_unit (ident_map f p)).

Arguments ident_map_ident {X Y} f {x y p q} _.
(* endfrag *)

(* ================================================================ *)
(** ** Functoriality of the induced map                             *)
(* ================================================================ *)

(* begfrag:rsfbjxq8 *)
Definition ident_map_function_unit
  : forall (X : Type) (x x' : X) (p : Ident x x'),
      Ident p (ident_map (function_unit X) p)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => Ident p (ident_map (function_unit X) p)
         in let
           base : F x (ident_unit x) := ident_unit (ident_unit x)
         in
           ident_induction x F base.

Arguments ident_map_function_unit {X x x'} p.
(* endfrag *)

(* begfrag:tm7axffm *)
Definition ident_map_function_compose
  : forall (X Y Z : Type)
           (g : Y -> Z)
           (f : X -> Y)
           (x x' : X)
           (p : Ident x x'),
      Ident (ident_map (function_compose g f) p)
            (ident_map g (ident_map f p))
  := fun (X Y Z : Type)
         (g : Y -> Z)
         (f : X -> Y)
         (x : X)
       =>
         let
           F : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => Ident (ident_map (function_compose g f) p)
                           (ident_map g (ident_map f p))
         in let
           base : F x (ident_unit x)
             := ident_unit (ident_unit (g (f x)))
         in
           ident_induction x F base.

Arguments ident_map_function_compose {X Y Z} g f {x x'} p.
(* endfrag *)

(* begfrag:t9j8usog *)
Definition ident_map_constant_function
  : forall (X Y : Type) (y : Y) (x x' : X) (p : Ident x x'),
      Ident (ident_unit y) (ident_map (constant_function y) p)
  := fun (X Y : Type) (y : Y) (x : X)
       =>
         let
           F : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => Ident (ident_unit y)
                           (ident_map (constant_function y) p)
         in let
           base : F x (ident_unit x) := ident_unit (ident_unit y)
         in
           ident_induction x F base.

Arguments ident_map_constant_function {X Y} y {x x'} p.
(* endfrag *)

(* ================================================================ *)
(** ** Cancellation laws                                            *)
(* ================================================================ *)

(* begfrag:omtjvrai *)
Definition ident_left_cancel
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q q' : Ident y z),
      Ident (ident_compose p q) (ident_compose p q') -> Ident q q'
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q q' :  Ident y z),
                       Ident (ident_compose p q) (ident_compose p q')
                         -> Ident q q'
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q q' : Ident x z)
                  => function_unit (Ident q q')
         in
           ident_induction x F base.

Arguments ident_left_cancel {X x y} p {z} q q' _.
(* endfrag *)

(* begfrag:865g4mt7 *)
Definition ident_left_remove
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y),
      Ident p p'
        -> forall (z : X) (q q' : Ident y z),
             Ident (ident_compose p q) (ident_compose p' q')
               -> Ident q q'
  := fun (X : Type)
         (x y : X)
         (p : Ident x y)
       => ident_recursion p
                          (fun (p' : Ident x y)
                             => forall (z : X) (q q' : Ident y z),
                                  Ident (ident_compose p q)
                                        (ident_compose p' q')
                                    -> Ident q q')
                          (fun (z : X) (q q' : Ident y z)
                             => ident_left_cancel p q q').

Arguments ident_left_remove {X x y p p'} _ {z} q q' _.
(* endfrag *)

(* begfrag:8gh9140h *)
Definition ident_right_cancel
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident (ident_compose p q) (ident_compose p' q) -> Ident p p'
  := fun (X : Type) (x y : X) (p p' : Ident x y)
       =>
         let
           F : forall (z : X), Ident y z -> Type
             := fun (z : X) (q : Ident y z)
                  => Ident (ident_compose p q) (ident_compose p' q)
                       -> Ident p p'
         in let
           base : F y (ident_unit y)
             := fun (u : Ident (ident_compose p (ident_unit y))
                               (ident_compose p' (ident_unit y)))
                  =>
                    let
                      e1 : Ident p (ident_compose p (ident_unit y))
                         := ident_right_unit p
                    in let
                      e2 : Ident (ident_compose p' (ident_unit y)) p'
                         := ident_inverse (ident_right_unit p')
                    in
                      ident_compose (ident_compose e1 u) e2
         in
           ident_induction y F base.

Arguments ident_right_cancel {X x y} p p' {z} q _.
(* endfrag *)

(* begfrag:sqhuo1hf *)
Definition ident_right_remove
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (z : X)
           (q q' : Ident y z),
      Ident q q'
        -> Ident (ident_compose p q) (ident_compose p' q')
          -> Ident p p'
  := fun (X : Type)
         (x y : X)
         (p p' : Ident x y)
         (z : X)
         (q : Ident y z)
       => ident_recursion q
                          (fun (q' : Ident y z)
                             => Ident (ident_compose p q)
                                      (ident_compose p' q')
                                  -> Ident p p')
                          (ident_right_cancel p p' q).

Arguments ident_right_remove {X x y} p p' {z q q'} _ _.
(* endfrag *)

(* ================================================================ *)
(** ** Uniqueness of units                                          *)
(* ================================================================ *)

(* begfrag:x71kqflr *)
Definition ident_left_unit_unique
  : forall (X : Type) (x y : X) (p : Ident x x) (q : Ident x y),
      Ident q (ident_compose p q) -> Ident (ident_unit x) p
  := fun (X : Type) (x y : X) (p : Ident x x) (q : Ident x y)
       => ident_right_cancel (ident_unit x) p q.

Arguments ident_left_unit_unique {X x y} p {q} _.
(* endfrag *)

(* begfrag:m1jqzny4 *)
Definition ident_right_unit_unique
  : forall (X : Type) (x y : X) (p : Ident x y) (q : Ident y y),
      Ident p (ident_compose p q) -> Ident (ident_unit y) q
  := fun (X : Type)
         (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (q : Ident y y),
                       Ident p (ident_compose p q)
                         -> Ident (ident_unit y) q
         in let
           base : F x (ident_unit x)
             := fun (q : Ident x x)
                  => function_unit (Ident (ident_unit x) q)
         in
           ident_induction x F base.

Arguments ident_right_unit_unique {X x y p} q _.
(* endfrag *)

(* ================================================================ *)
(** ** Uniqueness of inverses                                       *)
(* ================================================================ *)

(* begfrag:5f147sym *)
Definition ident_left_inverse_unique
  : forall (X : Type) (x y : X) (p : Ident x y) (q : Ident y x),
      Ident (ident_compose p q) (ident_unit x)
        -> Ident p (ident_inverse q)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (q : Ident y x),
                       Ident (ident_compose p q) (ident_unit x)
                         -> Ident p (ident_inverse q)
         in let
           base : F x (ident_unit x)
             := fun (q : Ident x x) (e : Ident q (ident_unit x))
                  => ident_inverse (ident_map ident_inverse e)
         in
           ident_induction x F base.

Arguments ident_left_inverse_unique {X x y} p q _.
(* endfrag *)

(* begfrag:bwldujz3 *)
Definition ident_right_inverse_unique
  : forall (X : Type) (x y : X) (p : Ident x y) (q : Ident y x),
      Ident (ident_compose p q) (ident_unit x)
        -> Ident q (ident_inverse p)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (q : Ident y x),
                       Ident (ident_compose p q) (ident_unit x)
                         -> Ident q (ident_inverse p)
         in let
           base : F x (ident_unit x)
             := fun (q : Ident x x)
                  => function_unit (Ident q (ident_unit x))
         in
           ident_induction x F base.

Arguments ident_right_inverse_unique {X x y} p q _.
(* endfrag *)

(* ================================================================ *)
(** ** Antimultiplicativity of inversion                            *)
(* ================================================================ *)

(* begfrag:vl4svtgg *)
Definition ident_inverse_antimultiplicative
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident (ident_inverse (ident_compose p q))
            (ident_compose (ident_inverse q) (ident_inverse p))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident y z),
                       Ident (ident_inverse (ident_compose p q))
                             (ident_compose (ident_inverse q)
                                            (ident_inverse p))
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z)
                  => ident_right_unit (ident_inverse q)
         in
           ident_induction x F base.

Arguments ident_inverse_antimultiplicative {X x y} p {z} q.
(* endfrag *)

(* ================================================================ *)
(** ** Involutivity of inversion                                    *)
(* ================================================================ *)

(* begfrag:mmbhn8r1 *)
Definition ident_inverse_involutive
  : forall (X : Type) (x y : X) (p : Ident x y),
      Ident p (ident_inverse (ident_inverse p))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => Ident p (ident_inverse (ident_inverse p))
         in let
           base : F x (ident_unit x)
             := ident_unit (ident_unit x)
         in
           ident_induction x F base.

Arguments ident_inverse_involutive {X x y} p.
(* endfrag *)

(* ================================================================ *)
(** ** Putting and removing an inverse                              *)
(* ================================================================ *)

(* begfrag:zgnf348j *)
Definition ident_put_inverse
  : forall (X : Type) (x y : X) (p q : Ident x y),
      Ident p q -> Ident (ident_inverse p) (ident_inverse q)
  := fun (X : Type) (x y : X) (p : Ident x y)
     => ident_recursion p
                        (fun (q : Ident x y)
                           => Ident (ident_inverse p)
                                    (ident_inverse q))
                        (ident_unit (ident_inverse p)).

Arguments ident_put_inverse {X x y p q} _.
(* endfrag *)

(* begfrag:93zoshti *)
Definition ident_remove_inverse
  : forall (X : Type) (x y : X) (p q : Ident x y),
      Ident (ident_inverse p) (ident_inverse q) -> Ident p q
  := fun (X : Type)
         (x y : X)
         (p q : Ident x y)
         (e : Ident (ident_inverse p) (ident_inverse q))
       =>
         let
           u1 : Ident p (ident_inverse (ident_inverse p))
              := ident_inverse_involutive p
         in let
           u2 : Ident (ident_inverse (ident_inverse p))
                      (ident_inverse (ident_inverse q))
              := ident_put_inverse e
         in let
           u3 : Ident (ident_inverse (ident_inverse q)) q
              := ident_inverse (ident_inverse_involutive q)
         in
           ident_compose (ident_compose u1 u2) u3.

Arguments ident_remove_inverse {X x y} p q _.
(* endfrag *)

(* ================================================================ *)
(** ** Moving factors across an identity                            *)
(* ================================================================ *)

(* begfrag:m4s5b57h *)
Definition ident_move_prefix_right
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z)
           (r : Ident x z),
      Ident (ident_compose p q) r
        -> Ident q (ident_compose (ident_inverse p) r)
  := fun (X : Type)
         (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident y z) (r : Ident x z),
                       Ident (ident_compose p q) r
                         -> Ident q
                                  (ident_compose (ident_inverse p) r)
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z) (r : Ident x z)
                  => function_unit (Ident q r)
         in
           ident_induction x F base.

Arguments ident_move_prefix_right {X x y} p {z} q {r} _.
(* endfrag *)

(* begfrag:62xaggnq *)
Definition ident_move_prefix_left
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z)
           (r : Ident x z),
      Ident r (ident_compose p q)
        -> Ident (ident_compose (ident_inverse p) r) q
  := fun (X : Type)
         (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident y z) (r : Ident x z),
                       Ident r (ident_compose p q)
                         -> Ident (ident_compose (ident_inverse p) r)
                                  q
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z) (r : Ident x z)
                  => function_unit (Ident r q)
         in
           ident_induction x F base.

Arguments ident_move_prefix_left {X x y} p {z} q {r} _.
(* endfrag *)

(* begfrag:10g8q8xv *)
Definition ident_move_suffix_right
  : forall (X : Type)
           (y z : X)
           (q : Ident y z)
           (x : X)
           (p : Ident x y)
           (r : Ident x z),
      Ident (ident_compose p q) r
        -> Ident p (ident_compose r (ident_inverse q))
  := fun (X : Type)
         (y : X)
       =>
         let
           F : forall (z : X), Ident y z -> Type
             := fun (z : X) (q : Ident y z)
                  => forall (x : X) (p : Ident x y) (r : Ident x z),
                       Ident (ident_compose p q) r
                         -> Ident p
                                  (ident_compose r (ident_inverse q))
         in let
           base : F y (ident_unit y)
             := fun (x : X)
                    (p : Ident x y)
                    (r : Ident x y)
                    (e : Ident (ident_compose p (ident_unit y)) r)
                  =>
                    let
                      u1 : Ident p (ident_compose p (ident_unit y))
                         := ident_right_unit p
                    in let
                      u2 : Ident r (ident_compose r (ident_unit y))
                         := ident_right_unit r
                    in
                      ident_compose (ident_compose u1 e) u2
         in
           ident_induction y F base.

Arguments ident_move_suffix_right {X y z} q {x} p {r} _.
(* endfrag *)

(* begfrag:xz2levku *)
Definition ident_move_suffix_left
  : forall (X : Type)
           (y z : X)
           (q : Ident y z)
           (x : X)
           (p : Ident x y)
           (r : Ident x z),
      Ident r (ident_compose p q)
        -> Ident (ident_compose r (ident_inverse q)) p
  := fun (X : Type)
         (y : X)
       =>
         let
           F : forall (z : X), Ident y z -> Type
             := fun (z : X) (q : Ident y z)
                  => forall (x : X) (p : Ident x y) (r : Ident x z),
                       Ident r (ident_compose p q)
                         -> Ident (ident_compose r (ident_inverse q))
                                  p
         in let
           base : F y (ident_unit y)
             := fun (x : X)
                    (p : Ident x y)
                    (r : Ident x y)
                    (e : Ident r (ident_compose p (ident_unit y)))
                  =>
                    let
                      u1 : Ident (ident_compose r (ident_unit y)) r
                         := ident_inverse (ident_right_unit r)
                    in let
                      u2 : Ident (ident_compose p (ident_unit y)) p
                         := ident_inverse (ident_right_unit p)
                    in
                      ident_compose (ident_compose u1 e) u2
         in
           ident_induction y F base.

Arguments ident_move_suffix_left {X y z} q {x} p {r} _.
(* endfrag *)

(* ================================================================ *)
(** ** Associativity of fourfold compositions of identities         *)
(* ================================================================ *)

(* begfrag:vwqasqd9 *)
Definition ident_associative41
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5),
      Ident (ident_compose
               (ident_compose (ident_compose p1 p2) p3) p4)
            (ident_compose
               (ident_compose p1 p2) (ident_compose p3 p4))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose p1 p2) p3) p4)
                             (ident_compose
                                (ident_compose p1 p2)
                                (ident_compose p3 p4))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                  => ident_associative p2 p3 p4
         in
           ident_induction x1 F base.

Arguments ident_associative41 {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4.
(* endfrag *)

(* begfrag:htm3siep *)
Definition ident_associative42
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5),
      Ident (ident_compose
               (ident_compose (ident_compose p1 p2) p3) p4)
            (ident_compose
               p1 (ident_compose p2 (ident_compose p3 p4)))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose p1 p2) p3) p4)
                             (ident_compose
                                p1 (ident_compose
                                      p2 (ident_compose p3 p4)))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                  => ident_associative p2 p3 p4
         in
           ident_induction x1 F base.

Arguments ident_associative42 {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4.
(* endfrag *)

(* begfrag:6bp6vvke *)
Definition ident_associative43
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5),
      Ident (ident_compose (ident_compose (ident_compose p1 p2) p3)
                           p4)
            (ident_compose (ident_compose p1 (ident_compose p2 p3))
                           p4)
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose p1 p2) p3) p4)
                             (ident_compose
                                (ident_compose
                                   p1 (ident_compose p2 p3)) p4)
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                  => ident_unit (ident_compose (ident_compose p2 p3)
                                               p4)
         in
           ident_induction x1 F base.

Arguments ident_associative43 {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4.
(* endfrag *)

(* begfrag:yy35505a *)
Definition ident_associative44
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5),
      Ident (ident_compose
               (ident_compose (ident_compose p1 p2) p3) p4)
            (ident_compose p1
                           (ident_compose (ident_compose p2 p3) p4))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose p1 p2) p3) p4)
                             (ident_compose
                                p1 (ident_compose
                                      (ident_compose p2 p3) p4))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                  => ident_unit (ident_compose (ident_compose p2 p3)
                                               p4)
         in
           ident_induction x1 F base.

Arguments ident_associative44 {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4.
(* endfrag *)

(* ================================================================ *)
(** ** Associativity of fivefold compositions of identities         *)
(* ================================================================ *)

(* begfrag:vosu70t8 *)
Definition ident_associative501
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               (ident_compose
                  (ident_compose p1 p2) p3) (ident_compose p4 p5))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                (ident_compose
                                   (ident_compose p1 p2) p3)
                                (ident_compose p4 p5))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative41 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative501
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:9195neum *)
Definition ident_associative502
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               (ident_compose
                  p1 (ident_compose p2 p3)) (ident_compose p4 p5))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                (ident_compose
                                   p1 (ident_compose p2 p3))
                                (ident_compose p4 p5))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative41 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative502
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:5ik0jqo4 *)
Definition ident_associative503
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               p1 (ident_compose
                     (ident_compose p2 p3) (ident_compose p4 p5)))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                p1 (ident_compose
                                      (ident_compose p2 p3)
                                      (ident_compose p4 p5)))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative41 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative503
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:tmu84qas *)
Definition ident_associative504
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               p1
               (ident_compose p2
                              (ident_compose p3
                                             (ident_compose p4 p5))))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                p1
                                (ident_compose
                                   p2 (ident_compose
                                         p3 (ident_compose p4 p5))))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative42 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative504
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:3mvhdnzr *)
Definition ident_associative505
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               (ident_compose
                  (ident_compose p1 (ident_compose p2 p3)) p4) p5)
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                (ident_compose
                                   (ident_compose
                                      p1 (ident_compose p2 p3)) p4)
                                p5)
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_unit (ident_compose
                                  (ident_compose
                                     (ident_compose p2 p3) p4) p5)
         in
           ident_induction x1 F base.

Arguments ident_associative505
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:9ayo8k2s *)
Definition ident_associative506
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               (ident_compose
                  p1 (ident_compose (ident_compose p2 p3) p4)) p5)
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                (ident_compose
                                   p1 (ident_compose
                                         (ident_compose p2 p3) p4))
                                p5)
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_unit (ident_compose
                                  (ident_compose
                                     (ident_compose p2 p3) p4) p5)
         in
           ident_induction x1 F base.

Arguments ident_associative506
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:pcffagae *)
Definition ident_associative507
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               p1 (ident_compose
                     (ident_compose (ident_compose p2 p3) p4) p5))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                p1 (ident_compose
                                      (ident_compose
                                         (ident_compose p2 p3) p4)
                                      p5))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_unit (ident_compose
                                  (ident_compose
                                     (ident_compose p2 p3) p4) p5)
         in
           ident_induction x1 F base.

Arguments ident_associative507
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:zy0t91bl *)
Definition ident_associative508
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               p1 (ident_compose
                     (ident_compose p2 (ident_compose p3 p4)) p5))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                p1 (ident_compose
                                      (ident_compose
                                         p2 (ident_compose p3 p4))
                                      p5))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative43 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative508
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:fsxr6lni *)
Definition ident_associative509
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               p1 (ident_compose
                     p2 (ident_compose (ident_compose p3 p4) p5)))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                p1 (ident_compose
                                      p2 (ident_compose
                                            (ident_compose p3 p4)
                                            p5)))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative44 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative509
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:yms4fe4g *)
Definition ident_associative510
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               (ident_compose
                  p1 (ident_compose p2 (ident_compose p3 p4))) p5)
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                (ident_compose
                                   p1
                                   (ident_compose p2
                                                  (ident_compose p3
                                                                 p4)))
                                p5)
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative43 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative510
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:vg53m3dr *)
Definition ident_associative511
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               (ident_compose
                  (ident_compose p1 p2) (ident_compose p3 p4)) p5)
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                (ident_compose
                                   (ident_compose p1 p2)
                                   (ident_compose p3 p4)) p5)
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative43 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative511
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:p0ba31nt *)
Definition ident_associative512
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               (ident_compose p1 p2)
               (ident_compose (ident_compose p3 p4) p5))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                (ident_compose
                                   p1 p2) (ident_compose
                                             (ident_compose p3 p4)
                                             p5))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative44 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative512
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* begfrag:3m4jej4m *)
Definition ident_associative513
  : forall (X : Type)
           (x1 x2 : X)
           (p1 : Ident x1 x2)
           (x3 : X)
           (p2 : Ident x2 x3)
           (x4 : X)
           (p3 : Ident x3 x4)
           (x5 : X)
           (p4 : Ident x4 x5)
           (x6 : X)
           (p5 : Ident x5 x6),
      Ident (ident_compose
               (ident_compose
                  (ident_compose (ident_compose p1 p2) p3) p4) p5)
            (ident_compose
               (ident_compose p1 p2)
               (ident_compose p3 (ident_compose p4 p5)))
  := fun (X : Type) (x1 : X)
       =>
         let
           F : forall (x2 : X), Ident x1 x2 -> Type
             := fun (x2 : X) (p1 : Ident x1 x2)
                  => forall (x3 : X)
                            (p2 : Ident x2 x3)
                            (x4 : X)
                            (p3 : Ident x3 x4)
                            (x5 : X)
                            (p4 : Ident x4 x5)
                            (x6 : X)
                            (p5 : Ident x5 x6),
                       Ident (ident_compose
                                (ident_compose
                                   (ident_compose
                                      (ident_compose p1 p2) p3) p4)
                                p5)
                             (ident_compose
                                (ident_compose
                                   p1 p2)
                                (ident_compose p3
                                               (ident_compose p4 p5)))
         in let
           base : F x1 (ident_unit x1)
             := fun (x3 : X)
                    (p2 : Ident x1 x3)
                    (x4 : X)
                    (p3 : Ident x3 x4)
                    (x5 : X)
                    (p4 : Ident x4 x5)
                    (x6 : X)
                    (p5 : Ident x5 x6)
                  => ident_associative42 p2 p3 p4 p5
         in
           ident_induction x1 F base.

Arguments ident_associative513
          {X x1 x2} p1 {x3} p2 {x4} p3 {x5} p4 {x6} p5.
(* endfrag *)

(* ================================================================ *)
(** ** Expanding an identity                                        *)
(* ================================================================ *)

(* begfrag:pav3j1ul *)
Definition ident_expand1
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident q (ident_compose (ident_compose (ident_inverse p) p) q)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident y z),
                       Ident q
                             (ident_compose
                                (ident_compose (ident_inverse p) p) q)
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z) => ident_unit q
         in
           ident_induction x F base.

Arguments ident_expand1 {X x y} p {z} q.
(* endfrag *)

(* begfrag:mvvftk3d *)
Definition ident_expand2
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident q (ident_compose (ident_inverse p) (ident_compose p q))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident y z),
                       Ident q
                             (ident_compose (ident_inverse p)
                                            (ident_compose p q))
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z) => ident_unit q
         in
           ident_induction x F base.

Arguments ident_expand2 {X x y} p {z} q.
(* endfrag *)

(* begfrag:cy9tfe66 *)
Definition ident_expand3
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident x z),
      Ident q (ident_compose (ident_compose p (ident_inverse p)) q)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident x z),
                       Ident q
                             (ident_compose
                                (ident_compose p (ident_inverse p)) q)
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z) => ident_unit q
         in
           ident_induction x F base.

Arguments ident_expand3 {X x y} p {z} q.
(* endfrag *)

(* begfrag:l9g32inq *)
Definition ident_expand4
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident x z),
      Ident q (ident_compose p (ident_compose (ident_inverse p) q))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident x z),
                       Ident q
                             (ident_compose
                                p (ident_compose (ident_inverse p) q))
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z) => ident_unit q
         in
           ident_induction x F base.

Arguments ident_expand4 {X x y} p {z} q.
(* endfrag *)

(* begfrag:9bk52g36 *)
Definition ident_expand5
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident z y),
      Ident p (ident_compose p (ident_compose (ident_inverse q) q))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident z y),
                       Ident p
                             (ident_compose
                                p (ident_compose (ident_inverse q) q))
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident z x) => ident_left_inverse q
         in
           ident_induction x F base.

Arguments ident_expand5 {X x y} p {z} q.
(* endfrag *)

(* begfrag:qyfzkb9p *)
Definition ident_expand6
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident z y),
      Ident p (ident_compose (ident_compose p (ident_inverse q)) q)
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident z y),
                       Ident p
                             (ident_compose
                                (ident_compose p (ident_inverse q)) q)
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident z x) => ident_left_inverse q
         in
           ident_induction x F base.

Arguments ident_expand6 {X x y} p {z} q.
(* endfrag *)

(* begfrag:imwi89t9 *)
Definition ident_expand7
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident p (ident_compose p (ident_compose q (ident_inverse q)))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident y z),
                       Ident p
                             (ident_compose
                                p (ident_compose q (ident_inverse q)))
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z) => ident_right_inverse q
         in
           ident_induction x F base.

Arguments ident_expand7 {X x y} p {z} q.
(* endfrag *)

(* begfrag:3e8zmhrz *)
Definition ident_expand8
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident p (ident_compose (ident_compose p q) (ident_inverse q))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident y z),
                       Ident p
                             (ident_compose (ident_compose p q)
                                            (ident_inverse q))
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z) => ident_right_inverse q
         in
           ident_induction x F base.

Arguments ident_expand8 {X x y} p {z} q.
(* endfrag *)

(* begfrag:g1p8yp91 *)
Definition ident_expand9
  : forall (X : Type)
           (w x : X)
           (p : Ident w x)
           (y : X)
           (q : Ident w y)
           (z : X)
           (r : Ident z y),
      Ident q (ident_compose
                 (ident_compose
                    (ident_compose
                       p (ident_compose (ident_inverse p) q))
                    (ident_inverse r))
                 r)
  := fun (X : Type) (w : X)
       =>
         let
           F : forall (x : X), Ident w x -> Type
             := fun (x : X) (p : Ident w x)
                  => forall (y : X)
                            (q : Ident w y)
                            (z : X)
                            (r : Ident z y),
                       Ident q (ident_compose
                                  (ident_compose
                                     (ident_compose
                                        p (ident_compose
                                             (ident_inverse p) q))
                                     (ident_inverse r))
                                  r)
         in let
           base : F w (ident_unit w)
             := fun (y : X) (q : Ident w y) (z : X) (r : Ident z y)
                  => ident_expand6 q r
         in
           ident_induction w F base.

Arguments ident_expand9 {X w x} p {y} q {z} r.
(* endfrag *)

(* ================================================================ *)
(** ** Triviality of idempotent identities                          *)
(* ================================================================ *)

(* begfrag:ra3f2wje *)
Definition ident_idempotent_trivial
  : forall (X : Type) (x : X) (p : Ident x x),
      Ident p (ident_compose p p) -> Ident (ident_unit x) p
  := fun (X : Type) (x : X) (p : Ident x x)
       => ident_right_cancel (ident_unit x) p p.

Arguments ident_idempotent_trivial {X x p} _.
(* endfrag *)

(* ================================================================ *)
(** ** Identities from elements                                     *)
(* ================================================================ *)

(* begfrag:ge0788wo *)
Definition IsIdentFrom : forall (X : Type), X -> Type
  := fun (X : Type) (x : X) => Sigma (fun (y : X) => Ident x y).

Arguments IsIdentFrom {X} _.
(* endfrag *)

(* begfrag:2b1xb9ym *)
Definition IdentFrom : Type -> Type
  := fun (X : Type) => Sigma (fun (x : X) => IsIdentFrom x).
(* endfrag *)

(* begfrag:d2un85gz *)
Definition ident_from_start
  : forall (X : Type), IdentFrom X -> X
  := fun (X : Type) (s : IdentFrom X) => sigma1 s.

Arguments ident_from_start {X} _.
(* endfrag *)

(* begfrag:2baj0zlh *)
Definition ident_from_end
  : forall (X : Type), IdentFrom X -> X
  := fun (X : Type) (s : IdentFrom X)=> sigma1 (sigma2 s).

Arguments ident_from_end {X} _.
(* endfrag *)

(* begfrag:4d453em2 *)
Definition ident_from_identity
  : forall (X : Type) (s : IdentFrom X),
      Ident (ident_from_start s) (ident_from_end s)
  := fun (X : Type) (s : IdentFrom X) => sigma2 (sigma2 s).

Arguments ident_from_identity {X} s.
(* endfrag *)

(* begfrag:oyuimxk1 *)
Definition ident_from
  : forall (X : Type) (x y : X), Ident x y -> IdentFrom X
  := fun (X : Type) (x y : X) (p : Ident x y)
       =>
         let
           s : IsIdentFrom x
             := sigma (fun (y1: X) => Ident x y1) y p
         in
           sigma (fun (x1 : X) => IsIdentFrom x1) x s.

Arguments ident_from {X x y} _.
(* endfrag *)

(* begfrag:ru5sabn4 *)
Definition ident_from_ident_unit
  : forall (X : Type), X -> IdentFrom X
  := fun (X : Type) (x : X) => ident_from (ident_unit x).

Arguments ident_from_ident_unit {X} _.
(* endfrag *)

(* ================================================================ *)
(** ** Identities to elements                                       *)
(* ================================================================ *)

(* begfrag:kq088axt *)
Definition IsIdentTo : forall (X : Type), X -> Type
  := fun (X : Type) (y : X) => Sigma (fun (x : X) => Ident x y).

Arguments IsIdentTo {X} _.
(* endfrag *)

(* begfrag:m50mi51w *)
Definition IdentTo : Type -> Type
  := fun (X : Type) => Sigma (fun (y : X) => IsIdentTo y).
(* endfrag *)

(* begfrag:puxybaiy *)
Definition ident_to_end
  : forall (X : Type), IdentTo X -> X
  := fun (X : Type) (s : IdentTo X)=> sigma1 s.

Arguments ident_to_end {X} _.
(* endfrag *)

(* begfrag:uxh47lia *)
Definition ident_to_start
  : forall (X : Type), IdentTo X -> X
  := fun (X : Type) (s : IdentTo X) => sigma1 (sigma2 s).

Arguments ident_to_start {X} _.
(* endfrag *)

(* begfrag:sdjeebfe *)
Definition ident_to_identity
  : forall (X : Type) (s : IdentTo X),
      Ident (ident_to_start s) (ident_to_end s)
  := fun (X : Type) (s : IdentTo X) => sigma2 (sigma2 s).

Arguments ident_to_identity {X} s.
(* endfrag *)

(* begfrag:ttau83f7 *)
Definition ident_to
  : forall (X : Type) (x y : X), Ident x y -> IdentTo X
  := fun (X : Type) (x y : X) (p : Ident x y)
       =>
         let
           s : IsIdentTo y
             := sigma (fun (x1: X) => Ident x1 y) x p
         in
           sigma (fun (y1 : X) => IsIdentTo y1) y s.

Arguments ident_to {X x y} _.
(* endfrag *)

(* begfrag:zyffeio3 *)
Definition ident_to_ident_unit
  : forall (X : Type), X -> IdentTo X
  := fun (X : Type) (y : X) => ident_to (ident_unit y).

Arguments ident_to_ident_unit {X} _.
(* endfrag *)

(* ================================================================ *)
(** ** Left whiskers                                                *)
(* ================================================================ *)

(* begfrag:g6ql88po *)
Definition ident_left_whisker
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q q' : Ident y z),
      Ident q q' -> Ident (ident_compose p q) (ident_compose p q')
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q q' : Ident y z),
                       Ident q q'
                         -> Ident (ident_compose p q)
                                  (ident_compose p q')
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q q' : Ident x z)
                  => function_unit (Ident q q')
         in
           ident_induction x F base.

Arguments ident_left_whisker {X x y} p {z q q'} _.
(* endfrag *)

(* begfrag:xhpcydus *)
Example _ident_left_whisker_left_unit
  : forall (X : Type)
           (x z : X)
           (q q' : Ident x z)
           (v : Ident q q'),
      Ident v (ident_left_whisker (ident_unit x) v)
  := fun (X : Type)
         (x z : X)
         (q q' : Ident x z)
         (v : Ident q q')
       => ident_unit v.
(* endfrag *)

(* begfrag:zm6vhjq4 *)
Definition ident_left_whisker_right_unit
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident (ident_unit (ident_compose p q))
            (ident_left_whisker p (ident_unit q))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X) (q : Ident y z),
                       Ident (ident_unit (ident_compose p q))
                             (ident_left_whisker p (ident_unit q))
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z)
                  => ident_unit (ident_unit q)
         in
           ident_induction x F base.

Arguments ident_left_whisker_right_unit {X x y} p {z} q.
(* endfrag *)

(* begfrag:jnw5wumu *)
Definition ident_left_whisker_multiplicative
  : forall (X : Type)
           (w x : X)
           (n : Ident w x)
           (y : X)
           (p : Ident x y)
           (z : X)
           (q q' : Ident y z)
           (v : Ident q q'),
      Ident (ident_compose (ident_associative n p q)
                           (ident_left_whisker
                              n (ident_left_whisker p v)))
            (ident_compose
               (ident_left_whisker (ident_compose n p) v)
               (ident_associative n p q'))
  := fun (X : Type) (w : X)
       =>
         let
           F : forall (x : X), Ident w x -> Type
             := fun (x : X) (n : Ident w x)
                  => forall (y : X)
                            (p : Ident x y)
                            (z : X)
                            (q q' : Ident y z)
                            (v : Ident q q'),
                       Ident (ident_compose
                                (ident_associative n p q)
                                (ident_left_whisker
                                   n (ident_left_whisker p v)))
                             (ident_compose
                                (ident_left_whisker
                                   (ident_compose n p) v)
                                (ident_associative n p q'))
         in let
           base : F w (ident_unit w)
             := fun (y : X)
                    (p : Ident w y)
                    (z : X)
                    (q q' : Ident y z)
                    (v : Ident q q')
                  => ident_right_unit (ident_left_whisker p v)
         in
           ident_induction w F base.

Arguments ident_left_whisker_multiplicative
          {X w x} n {y} p {z} {q q'} v.
(* endfrag *)

(* begfrag:piv9dpah *)
Definition ident_left_whisker_distributive
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q q' : Ident y z)
           (v : Ident q q')
           (q'' : Ident y z)
           (v' : Ident q' q''),
      Ident (ident_left_whisker p (ident_compose v v'))
            (ident_compose (ident_left_whisker p v)
                           (ident_left_whisker p v'))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X)
                            (q q' : Ident y z)
                            (v : Ident q q')
                            (q'' : Ident y z)
                            (v' : Ident q' q''),
                       Ident (ident_left_whisker p
                                                 (ident_compose v v'))
                             (ident_compose (ident_left_whisker p v)
                                            (ident_left_whisker p v'))
         in let
           base : F x (ident_unit x)
             := fun (z : X)
                    (q q' : Ident x z)
                    (v : Ident q q')
                    (q'' : Ident x z)
                    (v' : Ident q' q'')
                  => ident_unit (ident_compose v v')
         in
           ident_induction x F base.

Arguments ident_left_whisker_distributive
          {X x y} p {z} {q q'} v {q''} v'.
(* endfrag *)

(* ================================================================ *)
(** ** Right whiskers                                               *)
(* ================================================================ *)

(* begfrag:smege15s *)
Definition ident_right_whisker
  : forall (X : Type) (x y : X) (p p' : Ident x y),
      Ident p p'
        -> forall (z : X) (q : Ident y z),
             Ident (ident_compose p q) (ident_compose p' q)
  := fun (X : Type) (x y : X) (p : Ident x y)
       => ident_recursion p
                          (fun (p' : Ident x y)
                             => forall (z : X) (q : Ident y z),
                                  Ident (ident_compose p q)
                                        (ident_compose p' q))
                          (fun (z : X) (q : Ident y z)
                             => ident_unit (ident_compose p q)).

Arguments ident_right_whisker {X x y p p'} _ {z} q.
(* endfrag *)

(* begfrag:44tg9h29 *)
Example _ident_right_whisker_left_unit
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident (ident_unit (ident_compose p q))
            (ident_right_whisker (ident_unit p) q)
  := fun (X : Type)
         (x y : X)
         (p : Ident x y)
         (z : X)
         (q : Ident y z)
       => ident_unit (ident_unit (ident_compose p q)).
(* endfrag *)

(* begfrag:q1oa49qd *)
Definition ident_right_whisker_right_unit
  : forall (X : Type) (x y : X) (p p' : Ident x y) (u : Ident p p'),
      Ident (ident_compose u (ident_right_unit p'))
            (ident_compose (ident_right_unit p)
                           (ident_right_whisker u (ident_unit y)))
  := fun (X : Type) (x y : X) (p : Ident x y)
       =>
         let
           F : forall (p' : Ident x y), Ident p p' -> Type
             := fun (p' : Ident x y) (u : Ident p p')
                  => Ident (ident_compose u (ident_right_unit p'))
                           (ident_compose
                              (ident_right_unit p)
                              (ident_right_whisker u (ident_unit y)))
         in let
           base : F p (ident_unit p)
             := ident_right_unit (ident_right_unit p)
         in
           ident_induction p F base.

Arguments ident_right_whisker_right_unit {X x y p p'} u.
(* endfrag *)

(* begfrag:9xxalp0u *)
Definition ident_right_whisker_multiplicative
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (u : Ident p p')
           (z : X)
           (q : Ident y z)
           (w : X)
           (r : Ident z w),
      Ident (ident_compose
               (ident_right_whisker (ident_right_whisker u q) r)
               (ident_associative p' q r))
            (ident_compose
               (ident_associative p q r)
               (ident_right_whisker u (ident_compose q r)))
  := fun (X : Type) (x y : X) (p : Ident x y)
       =>
         let
           F : forall (p' : Ident x y), Ident p p' -> Type
             := fun (p' : Ident x y) (u : Ident p p')
                  => forall (z : X)
                            (q : Ident y z)
                            (w : X)
                            (r : Ident z w),
                       Ident (ident_compose
                                (ident_right_whisker
                                   (ident_right_whisker u q) r)
                                (ident_associative p' q r))
                             (ident_compose
                                (ident_associative p q r)
                                (ident_right_whisker
                                   u (ident_compose q r)))

         in let
           base : F p (ident_unit p)
             := fun (z : X) (q : Ident y z) (w : X) (r : Ident z w)
                  => ident_right_unit (ident_associative p q r)
         in
           ident_induction p F base.

Arguments ident_right_whisker_multiplicative
          {X x y p p'} u {z} q {w} r.
(* endfrag *)

(* begfrag:mat6rb8r *)
Definition ident_right_whisker_distributive
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (u : Ident p p')
           (p'' : Ident x y)
           (u' : Ident p' p'')
           (z : X)
           (q : Ident y z),
      Ident (ident_right_whisker (ident_compose u u') q)
            (ident_compose (ident_right_whisker u q)
                           (ident_right_whisker u' q))
  := fun (X : Type) (x y : X) (p : Ident x y)
       =>
         let
           F : forall (p' : Ident x y), Ident p p' -> Type
             := fun (p' : Ident x y) (u : Ident p p')
                  => forall (p'' : Ident x y)
                            (u' : Ident p' p'')
                            (z : X)
                            (q : Ident y z),
                       Ident (ident_right_whisker
                                (ident_compose u u') q)
                             (ident_compose
                                (ident_right_whisker u q)
                                (ident_right_whisker u' q))
         in let
           base : F p (ident_unit p)
             := fun (p'' : Ident x y)
                    (u' : Ident p p'')
                    (z : X)
                    (q : Ident y z)
                  => ident_unit (ident_right_whisker u' q)
         in
           ident_induction p F base.

Arguments ident_right_whisker_distributive
          {X x y p p'} u {p''} u' {z} q.
(* endfrag *)

(* ================================================================ *)
(** ** Compatibility of left and right whiskers                     *)
(* ================================================================ *)

(* begfrag:yxgwpuum *)
Definition ident_left_right_whisker
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q q' : Ident y z)
           (u : Ident q q')
           (w : X)
           (r : Ident z w),
      Ident (ident_compose (ident_associative p q r)
                           (ident_left_whisker
                              p
                              (ident_right_whisker u r)))
            (ident_compose
               (ident_right_whisker (ident_left_whisker p u) r)
               (ident_associative p q' r))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                  => forall (z : X)
                            (q q' : Ident y z)
                            (u : Ident q q')
                            (w : X)
                            (r : Ident z w),
                       Ident (ident_compose
                                (ident_associative p q r)
                                (ident_left_whisker
                                   p
                                   (ident_right_whisker u r)))
                             (ident_compose
                                (ident_right_whisker
                                   (ident_left_whisker p u) r)
                                (ident_associative p q' r))
         in let
           base : F x (ident_unit x)
             := fun (z : X)
                    (q q' : Ident x z)
                    (u : Ident q q')
                    (w : X)
                    (r : Ident z w)
                  => ident_right_unit (ident_right_whisker u r)
         in
           ident_induction x F base.

Arguments ident_left_right_whisker {X x y} p {z q q'} u {w} r.
(* endfrag *)

(* ================================================================ *)
(** ** Horizontal composition of identities                         *)
(* ================================================================ *)

(* begfrag:3vb37e5t *)
Definition ident_compose_horizontal
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y),
      Ident p p'
        -> forall (z : X) (q q' : Ident y z),
             Ident q q'
               -> Ident (ident_compose p q) (ident_compose p' q')
  := fun (X : Type)
         (x y : X)
         (p p' : Ident x y)
         (u : Ident p p')
         (z : X)
         (q q' : Ident y z)
         (v : Ident q q')
       =>
         let
           e1 : Ident (ident_compose p q) (ident_compose p' q)
              := ident_right_whisker u q
         in let
           e2 : Ident (ident_compose p' q) (ident_compose p' q')
              := ident_left_whisker p' v
         in
           ident_compose e1 e2.

Arguments ident_compose_horizontal {X x y p p'} _ {z q q'} _.
(* endfrag *)

(* begfrag:npsmi0d4 *)
Definition ident_compose_horizontal2
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y),
      Ident p p'
        -> forall (z : X) (q q' : Ident y z),
             Ident q q'
               -> Ident (ident_compose p q) (ident_compose p' q')
  := fun (X : Type)
         (x y : X)
         (p p' : Ident x y)
         (u : Ident p p')
         (z : X)
         (q q' : Ident y z)
         (v : Ident q q')
       =>
         let
           e1 : Ident (ident_compose p q) (ident_compose p q')
              := ident_left_whisker p v
         in let
           e2 : Ident (ident_compose p q') (ident_compose p' q')
              := ident_right_whisker u q'
         in
           ident_compose e1 e2.

Arguments ident_compose_horizontal2 {X x y p p'} _ {z q q'} _.
(* endfrag *)

(* begfrag:zvsjksff *)
Definition ident_compose_horizontals_ident
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (u : Ident p p')
           (z : X)
           (q q' : Ident y z)
           (v : Ident q q'),
      Ident (ident_compose_horizontal u v)
            (ident_compose_horizontal2 u v)
  := fun (X : Type) (x y : X) (p : Ident x y)
       =>
         let
           F : forall (p' : Ident x y), Ident p p' -> Type
             := fun (p' : Ident x y) (u : Ident p p')
                  => forall (z : X)
                            (q q' : Ident y z)
                            (v : Ident q q'),
                       Ident (ident_compose_horizontal u v)
                             (ident_compose_horizontal2 u v)
         in let
           base : F p (ident_unit p)
             := fun (z : X) (q q' : Ident y z) (v : Ident q q')
                  => ident_right_unit (ident_left_whisker p v)
         in
           ident_induction p F base.

Arguments ident_compose_horizontals_ident {X x y p p'} u {z q q'} v.
(* endfrag *)

(* ================================================================ *)
(** ** The Eckmann-Hilton argument                                  *)
(* ================================================================ *)

(* begfrag:nyqxuym9 *)
Definition ident_eckmann_hilton1
  : forall (X : Type)
           (x : X)
           (u v : Ident (ident_unit x) (ident_unit x)),
      Ident (ident_compose u v)
            (ident_compose_horizontal u v)
  := fun (X : Type)
         (x : X)
         (u v : Ident (ident_unit x) (ident_unit x))
       =>
         let
           e1 : Ident u (ident_compose u (ident_unit (ident_unit x)))
              := ident_right_unit u
         in let
           e2 : Ident (ident_compose u (ident_unit (ident_unit x)))
                      (ident_right_whisker u (ident_unit x))
              := ident_right_whisker_right_unit u
         in let
           e3 : Ident u (ident_right_whisker u (ident_unit x))
              := ident_compose e1 e2
         in let
           f : Ident (ident_unit x) (ident_unit x)
                 -> Ident (ident_unit x) (ident_unit x)
             := fun t => ident_compose t v
         in
           ident_map f e3.

Arguments ident_eckmann_hilton1 {X x} u v.
(* endfrag *)

(* begfrag:mwabek2b *)
Definition ident_eckmann_hilton2
  : forall (X : Type)
           (x : X)
           (u v : Ident (ident_unit x) (ident_unit x)),
      Ident (ident_compose u v) (ident_compose v u)
  := fun (X : Type)
         (x : X)
         (u v : Ident (ident_unit x) (ident_unit x))
       =>
         let
           e1 : Ident (ident_compose u v)
                      (ident_compose_horizontal u v)
              := ident_eckmann_hilton1 u v
         in let
           e2 : Ident (ident_compose_horizontal u v)
                      (ident_compose_horizontal2 u v)
              := ident_compose_horizontals_ident u v
         in let
           e3 : Ident (ident_compose u v)
                      (ident_compose
                         v (ident_right_whisker u (ident_unit x)))
              := ident_compose e1 e2
         in let
           m1 : Ident u (ident_compose u (ident_unit (ident_unit x)))
              := ident_right_unit u
         in let
           m2 : Ident (ident_compose u (ident_unit (ident_unit x)))
                      (ident_right_whisker u (ident_unit x))
              := ident_right_whisker_right_unit u
         in let
           m3 : Ident u (ident_right_whisker u (ident_unit x))
              := ident_compose m1 m2
         in let
           m4 : Ident (ident_right_whisker u (ident_unit x)) u
              := ident_inverse m3
         in let
           f : Ident (ident_unit x) (ident_unit x)
                 -> Ident (ident_unit x) (ident_unit x)
             := fun t => ident_compose v t
         in let
           e4 : Ident (ident_compose_horizontal2 u v)
                      (ident_compose v u)
              := ident_map f m4
         in
           ident_compose e3 e4.

Arguments ident_eckmann_hilton2 {X x} u v.
(* endfrag *)

(* ================================================================ *)
(** ** Properties of horizontal composition                         *)
(* ================================================================ *)

(* begfrag:vrdp16nj *)
Example _ident_horizontal_left_unit
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q q' : Ident y z)
           (v : Ident q q'),
      Ident (ident_left_whisker p v)
            (ident_compose_horizontal (ident_unit p) v)
  := fun (X : Type)
         (x y : X)
         (p : Ident x y)
         (z : X)
         (q q' : Ident y z)
         (v : Ident q q')
       => ident_unit (ident_left_whisker p v).
(* endfrag *)

(* begfrag:jgfm6he2 *)
Definition ident_horizontal_units
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident (ident_unit (ident_compose p q))
            (ident_compose_horizontal (ident_unit p) (ident_unit q))
  := fun (X : Type) (x : X)
       =>
         let
           F : forall (y : X), Ident x y -> Type
             := fun (y : X) (p : Ident x y)
                => forall (z : X) (q : Ident y z),
                     Ident (ident_unit (ident_compose p q))
                           (ident_compose_horizontal (ident_unit p)
                                                     (ident_unit q))
         in let
           base : F x (ident_unit x)
             := fun (z : X) (q : Ident x z)
                  => ident_unit (ident_unit q)
         in
           ident_induction x F base.

Arguments ident_horizontal_units {X x y} p {z} q.
(* endfrag *)

(* begfrag:utaka100 *)
Definition ident_horizontal_right_unit
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (u : Ident p p')
           (z : X)
           (q : Ident y z),
      Ident (ident_right_whisker u q)
            (ident_compose_horizontal u (ident_unit q))
  := fun (X : Type) (x y : X) (p : Ident x y)
       =>
         let
           F : forall (p' : Ident x y), Ident p p' -> Type
             := fun (p' : Ident x y) (u : Ident p p')
                  => forall (z : X) (q : Ident y z),
                       Ident (ident_right_whisker u q)
                             (ident_compose_horizontal u
                                                       (ident_unit q))
         in let
           base : F p (ident_unit p)
             := fun (z : X) (q : Ident y z)
                  => ident_horizontal_units p q
         in
           ident_induction p F base.

Arguments ident_horizontal_right_unit {X x y p p'} u {z} q.
(* endfrag *)

(* begfrag:ylpcqk5j *)
Definition ident_horizontal_whisker1
  : forall (X : Type)
           (a b : X)
           (p : Ident a b)
           (c : X)
           (q q' : Ident b c)
           (v : Ident q q')
           (d : X)
           (r r' : Ident c d)
           (w : Ident r r'),
      Ident (ident_compose
               (ident_associative p q r)
               (ident_left_whisker p (ident_compose_horizontal v w)))
            (ident_compose
               (ident_compose_horizontal (ident_left_whisker p v) w)
               (ident_associative p q' r'))
  := fun (X : Type) (a : X)
       =>
         let
           F : forall (b : X), Ident a b -> Type
             := fun (b : X) (p : Ident a b)
                  => forall (c : X)
                            (q q' : Ident b c)
                            (v : Ident q q')
                            (d : X)
                            (r r' : Ident c d)
                            (w : Ident r r'),
                       Ident (ident_compose
                                (ident_associative p q r)
                                (ident_left_whisker
                                   p (ident_compose_horizontal v w)))
                             (ident_compose
                                (ident_compose_horizontal
                                   (ident_left_whisker p v) w)
                                (ident_associative p q' r'))
         in let
           base : F a (ident_unit a)
             := fun (c : X)
                    (q q' : Ident a c)
                    (v : Ident q q')
                    (d : X)
                    (r r' : Ident c d)
                    (w : Ident r r')
                  => ident_right_unit (ident_compose_horizontal v w)
         in
           ident_induction a F base.

Arguments ident_horizontal_whisker1
          {X a b} p {c q q'} v {d r r'} w.
(* endfrag *)

(* begfrag:wozp1da2 *)
Definition ident_horizontal_whisker2
  : forall (X : Type)
           (a b : X)
           (p p' : Ident a b)
           (u : Ident p p')
           (c : X)
           (q : Ident b c)
           (d : X)
           (r r' : Ident c d)
           (w : Ident r r'),
      Ident (ident_compose
               (ident_associative p q r)
               (ident_compose_horizontal u (ident_left_whisker q w)))
            (ident_compose
               (ident_compose_horizontal (ident_right_whisker u q) w)
               (ident_associative p' q r'))
  := fun (X : Type) (a b : X) (p : Ident a b)
       =>
         let
           F : forall (p' : Ident a b), Ident p p' -> Type
             := fun (p' : Ident a b) (u : Ident p p')
                  => forall (c : X)
                            (q : Ident b c)
                            (d : X)
                            (r r' : Ident c d)
                            (w : Ident r r'),
                       Ident (ident_compose
                                (ident_associative p q r)
                                (ident_compose_horizontal
                                   u (ident_left_whisker q w)))
                             (ident_compose
                                (ident_compose_horizontal
                                   (ident_right_whisker u q) w)
                                (ident_associative p' q r'))
         in let
           base : F p (ident_unit p)
             := fun (c : X)
                    (q : Ident b c)
                    (d : X)
                    (r r' : Ident c d)
                    (w : Ident r r')
                  => ident_left_whisker_multiplicative p q w
         in
           ident_induction p F base.

Arguments ident_horizontal_whisker2
  {X a b p p'} u {c} q {d r r'} w.
(* endfrag *)

(* begfrag:vfzz2ypj *)
Definition ident_horizontal_whisker3
  : forall (X : Type)
           (a b : X)
           (p p' : Ident a b)
           (u : Ident p p')
           (c : X)
           (q q' : Ident b c)
           (v : Ident q q')
           (d : X)
           (r : Ident c d),
      Ident (ident_compose
               (ident_associative p q r)
               (ident_compose_horizontal u (ident_right_whisker v r)))
            (ident_compose
               (ident_right_whisker (ident_compose_horizontal u v) r)
               (ident_associative p' q' r))
  := fun (X : Type) (a b : X) (p : Ident a b)
       =>
         let
           F : forall (p' : Ident a b), Ident p p' -> Type
             := fun (p' : Ident a b) (u : Ident p p')
                  => forall (c : X)
                            (q q' : Ident b c)
                            (v : Ident q q')
                            (d : X)
                            (r : Ident c d),
                       Ident (ident_compose
                                (ident_associative p q r)
                                (ident_compose_horizontal
                                   u (ident_right_whisker v r)))
                             (ident_compose
                                (ident_right_whisker
                                   (ident_compose_horizontal u v) r)
                                (ident_associative p' q' r))
         in let
           base : F p (ident_unit p)
             := fun (c : X)
                    (q q' : Ident b c)
                    (v : Ident q q')
                    (d : X)
                    (r : Ident c d)
                  => ident_left_right_whisker p v r
         in
           ident_induction p F base.

Arguments ident_horizontal_whisker3
  {X a b p p'} u {c} {q q'} v {d} r.
(* endfrag *)

(* begfrag:deqa7gao *)
Definition ident_horizontal_associative
  : forall (X : Type)
           (a b : X)
           (p p' : Ident a b)
           (u : Ident p p')
           (c : X)
           (q q' : Ident b c)
           (v : Ident q q')
           (d : X)
           (r r' : Ident c d)
           (w : Ident r r'),
      Ident (ident_compose
               (ident_associative p q r)
               (ident_compose_horizontal
                  u (ident_compose_horizontal v w)))
            (ident_compose
               (ident_compose_horizontal
                  (ident_compose_horizontal u v) w)
               (ident_associative p' q' r'))
  := fun (X : Type) (a b : X) (p : Ident a b)
     =>
       let
         F : forall (p' : Ident a b), Ident p p' -> Type
           := fun (p' : Ident a b) (u : Ident p p')
                => forall (c : X)
                          (q q' : Ident b c)
                          (v : Ident q q')
                          (d : X)
                          (r r' : Ident c d)
                          (w : Ident r r'),
                     Ident (ident_compose
                              (ident_associative p q r)
                              (ident_compose_horizontal
                                 u (ident_compose_horizontal v w)))
                           (ident_compose
                              (ident_compose_horizontal
                                 (ident_compose_horizontal u v) w)
                              (ident_associative p' q' r'))
       in let
         base : F p (ident_unit p)
           := fun (c : X)
                  (q q' : Ident b c)
                  (v : Ident q q')
                  (d : X)
                  (r r' : Ident c d)
                  (w : Ident r r')
                => ident_horizontal_whisker1 p v w
       in
         ident_induction p F base.

Arguments ident_horizontal_associative
  {X a b p p'} u {c q q'} v {d r r'} w.
(* endfrag *)

(* ================================================================ *)
(** ** The middle four interchange law                              *)
(* ================================================================ *)

(* begfrag:az57qffa *)
Example _ident_middle4_interchange_base_case
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (u : Ident p p')
           (z : X)
           (q q' : Ident y z)
           (v : Ident q q')
           (q'' : Ident y z)
           (v' : Ident q' q''),
      Ident (ident_compose_horizontal u (ident_compose v v'))
            (ident_compose (ident_left_whisker p v)
                           (ident_compose_horizontal u v'))
  := fun (X : Type) (x y : X) (p : Ident x y)
       =>
         let
           F : forall (p' : Ident x y), Ident p p' -> Type
             := fun (p' : Ident x y) (u : Ident p p')
                  => forall (z : X)
                            (q q' : Ident y z)
                            (v : Ident q q')
                            (q'' : Ident y z)
                            (v' : Ident q' q''),
                       Ident (ident_compose_horizontal
                                u (ident_compose v v'))
                             (ident_compose
                                (ident_left_whisker p v)
                                (ident_compose_horizontal u v'))
         in let
           base : F p (ident_unit p)
             := fun (z : X)
                    (q q' : Ident y z)
                    (v : Ident q q')
                    (q'' : Ident y z)
                    (v' : Ident q' q'')
                  => ident_left_whisker_distributive p v v'
         in
           ident_induction p F base.
(* endfrag *)

(* begfrag:lwix0r34 *)
Definition ident_middle4_interchange
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (u : Ident p p')
           (p'' : Ident x y)
           (u' : Ident p' p'')
           (z : X)
           (q q' : Ident y z)
           (v : Ident q q')
           (q'' : Ident y z)
           (v' : Ident q' q''),
      Ident (ident_compose_horizontal (ident_compose u u')
                                      (ident_compose v v'))
            (ident_compose (ident_compose_horizontal u v)
                           (ident_compose_horizontal u' v'))
  := fun (X : Type) (x y : X) (p : Ident x y)
       =>
         let
           F : forall (p' : Ident x y), Ident p p' -> Type
             := fun (p' : Ident x y) (u : Ident p p')
                  => forall (p'' : Ident x y)
                            (u' : Ident p' p'')
                            (z : X)
                            (q q' : Ident y z)
                            (v : Ident q q')
                            (q'' : Ident y z)
                            (v' : Ident q' q''),
                       Ident (ident_compose_horizontal
                                (ident_compose u u')
                                (ident_compose v v'))
                             (ident_compose
                                (ident_compose_horizontal u v)
                                (ident_compose_horizontal u' v'))
         in let
           base : F p (ident_unit p)
             := fun (p'' : Ident x y)
                    (u' : Ident p p'')
                    (z : X)
                    (q q' : Ident y z)
                    (v : Ident q q')
                    (q'' : Ident y z)
                    (v' : Ident q' q'')
                  => _ident_middle4_interchange_base_case
                       X x y p p'' u' z q q' v q'' v'
         in
           ident_induction p F base.

Arguments ident_middle4_interchange
  {X x y p p'} u {p''} u' {z q q'} v {q''} v'.
(* endfrag *)

(* End of file *)
