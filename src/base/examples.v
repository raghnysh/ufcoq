(* Some examples arising from other modules *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:909vtogz *)
Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.
Require Import ufcoq.base.ident.
(* endfrag *)

(* ================================================================ *)
(** ** Function types                                               *)
(* ================================================================ *)

(* begfrag:ryjyw5yo *)
Example _function_eta_conversion
  : forall (X : Type) (F : X -> Type) (f : forall (x : X), F x),
      Ident f (fun (x : X) => f x)
  := fun (X : Type) (F : X -> Type) (f : forall (x : X), F x)
      => ident_unit f.
(* endfrag *)

(* begfrag:r3y1kpvr *)
Example _function_compose_associative
  : forall (W : Type)
           (X : Type)
           (Y : Type)
           (G : Y -> Type)
           (g : forall (y : Y), G y)
           (f : X -> Y)
           (e : W -> X),
      Ident (function_compose (function_compose g f) e)
            (function_compose g (function_compose f e))
  := fun (W : Type)
         (X : Type)
         (Y : Type)
         (G : Y -> Type)
         (g : forall (y : Y), G y)
         (f : X -> Y)
         (e : W -> X)
       => ident_unit (function_compose (function_compose g f) e).
(* endfrag *)

(* begfrag:hso05la4 *)
Example _function_compose_left_unit
  : forall (X Y : Type) (f : X -> Y),
      Ident f (function_compose (function_unit Y) f)
  := fun (X Y : Type) (f : X -> Y)
       => ident_unit f.
(* endfrag *)

(* begfrag:ey5cl868 *)
Example _function_compose_right_unit
  : forall (X : Type)
           (G : X -> Type)
           (g : forall (x : X), G x),
      Ident g (function_compose  g (function_unit X))
  := fun (X : Type)
         (G : X -> Type)
         (g : forall (x : X), G x)
       => ident_unit g.
(* endfrag *)

(* ================================================================ *)
(** ** The true type                                                *)
(* ================================================================ *)

(* begfrag:tuh9sgix *)
Example _true_induction_only
  : forall (F : True -> Type) (x : F only),
      Ident x (true_induction F x only)
  := fun (F : True -> Type) (x : F only)
       => ident_unit x.
(* endfrag *)

(* begfrag:iww5ck0g *)
Example _true_recursion_only
  : forall (X : Type) (x : X), Ident x (true_recursion x only)
  := fun (X : Type) (x : X) => ident_unit x.
(* endfrag *)

(* begfrag:qgyqpcz3 *)
Example _to_true_only
  : forall (X : Type) (x : X), Ident only (to_true x)
  := fun (X : Type) (x : X) => ident_unit only.
(* endfrag *)

(* ================================================================ *)
(** ** The Boolean type                                             *)
(* ================================================================ *)

(* begfrag:ogo7jox4 *)
Example _boolean_induction_yes
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Ident y (boolean_induction F y n yes)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => ident_unit y.
(* endfrag *)

(* begfrag:6ly41ngr *)
Example _boolean_induction_no
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Ident n (boolean_induction F y n no)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => ident_unit n.
(* endfrag *)

(* begfrag:2wynnkw2 *)
Example _boolean_recursion_yes
  : forall (X : Type) (y n : X), Ident y (boolean_recursion y n yes)
  := fun (X : Type) (y n : X) => ident_unit y.
(* endfrag *)

(* begfrag:4cga60mp *)
Example _boolean_recursion_no
  : forall (X : Type) (y n : X), Ident n (boolean_recursion y n no)
  := fun (X : Type) (y n : X) => ident_unit n.
(* endfrag *)

(* ================================================================ *)
(** ** The type of natural numbers                                  *)
(* ================================================================ *)

(* begfrag:p33ig2te *)
Example _natural_induction_zero
  : forall (F : Natural -> Type)
           (z : F zero)
           (s : forall (n : Natural), F n -> F (successor n)),
      Ident z (natural_induction F z s zero)
  := fun (F : Natural -> Type)
         (z : F zero)
         (s : forall (n : Natural), F n -> F (successor n))
       => ident_unit z.
(* endfrag *)

(* begfrag:ojb7dh9z *)
Example _natural_induction_successor
  : forall (F : Natural -> Type)
           (z : F zero)
           (s : forall (n : Natural), F n -> F (successor n))
           (n : Natural),
      Ident (s n (natural_induction F z s n))
            (natural_induction F z s (successor n))
  := fun (F : Natural -> Type)
         (z : F zero)
         (s : forall (n : Natural), F n -> F (successor n))
         (n : Natural)
       => ident_unit (s n (natural_induction F z s n)).
(* endfrag *)

(* begfrag:rzfhv79d *)
Example _natural_recursion_zero
  : forall (X : Type) (z : X) (s : Natural -> X -> X),
      Ident z (natural_recursion z s zero)
  := fun (X : Type) (z : X) (s : Natural -> X -> X)
       => ident_unit z.
(* endfrag *)

(* begfrag:hrrncvpb *)
Example _natural_recursion_successor
  : forall (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural),
      Ident (s n (natural_recursion z s n))
            (natural_recursion z s (successor n))
  := fun (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural)
     => ident_unit (s n (natural_recursion z s n)).
(* endfrag *)

(* begfrag:upakg9n0 *)
Example _natural_recursion_simple_zero
  : forall (X : Type) (z : X) (s : X -> X),
      Ident z (natural_recursion_simple z s zero)
  := fun (X : Type) (z : X) (s : X -> X)
       => ident_unit z.
(* endfrag *)

(* begfrag:tsfievor *)
Example _natural_recursion_simple_successor
  : forall (X : Type) (z : X) (s : X -> X) (n : Natural),
      Ident (s (natural_recursion_simple z s n))
            (natural_recursion_simple z s (successor n))
  := fun (X : Type) (z : X) (s : X -> X) (n : Natural)
       => ident_unit (s (natural_recursion_simple z s n)).
(* endfrag *)

(* ================================================================ *)
(** ** Identity types                                               *)
(* ================================================================ *)

(* begfrag:fznk9p3u *)
Example _ident_induction_ident_unit
  : forall (X : Type)
           (x : X)
           (F : forall (y : X), Ident x y -> Type)
           (e : F x (ident_unit x)),
      Ident e (ident_induction x F e x (ident_unit x))
  := fun (X : Type)
         (x : X)
         (F : forall (y : X), Ident x y -> Type)
         (e : F x (ident_unit x))
       => ident_unit e.
(* endfrag *)

(* begfrag:obnor2k3 *)
Example _transport_ident_unit
  : forall (X : Type) (F : X -> Type) (x y : X),
      Ident (function_unit (F x)) (transport F (ident_unit x))
  := fun (X : Type) (F : X -> Type) (x y : X)
       => ident_unit (function_unit (F x)).
(* endfrag *)

(* begfrag:iqo3w2uh *)
Example _transport_inverse_ident_unit
  : forall (X : Type) (F : X -> Type) (x y : X),
      Ident (function_unit (F x))
            (transport_inverse F (ident_unit x))
  := fun (X : Type) (F : X -> Type) (x y : X)
       => ident_unit (function_unit (F x)).
(* endfrag *)

(* ================================================================ *)
(** ** Sigma types                                                  *)
(* ================================================================ *)

(* begfrag:qts05vtg *)
Example _sigma_type_eta_conversion
  : forall (X : Type) (F : X -> Type) (t : Sigma F),
      Ident t (sigma F (sigma1 t) (sigma2 t))
  := fun (X : Type) (F : X -> Type) (t : Sigma F)
       => ident_unit t.
(* endfrag *)

(* begfrag:mrl11i2o *)
Example _sigma_curry_uncurry
  : forall (X : Type)
           (F : X -> Type)
           (G : Sigma F -> Type)
           (f : forall (x : X) (y : F x), G (sigma F x y)),
      Ident f (sigma_curry (sigma_uncurry f))
  := fun (X : Type)
         (F : X -> Type)
         (G : Sigma F -> Type)
         (f : forall (x : X) (y : F x), G (sigma F x y))
       => ident_unit f.
(* endfrag *)

(* begfrag:4zlly4cd *)
Example _sigma_uncurry_curry
  : forall (X : Type)
           (F : X -> Type)
           (G : Sigma F -> Type)
           (g : forall (t : Sigma F), G t),
      Ident g (sigma_uncurry (sigma_curry g))
  := fun (X : Type)
         (F : X -> Type)
         (G : Sigma F -> Type)
         (g : forall (t : Sigma F), G t)
       => ident_unit g.
(* endfrag *)

(* ================================================================ *)
(** ** Product types                                                *)
(* ================================================================ *)

(* begfrag:wruha80w *)
Example _product_eta_conversion
  : forall (X Y : Type) (t : Product X Y),
      Ident t (pair (first t) (second t))
  := fun (X Y : Type) (t : Product X Y)
       => ident_unit t.
(* endfrag *)

(* begfrag:h1vgtr2g *)
Example _curry_uncurry
  : forall (X Y : Type)
           (F : Product X Y -> Type)
           (f : forall (x : X) (y : Y), F (pair x y)),
        Ident f (curry (uncurry f))
  := fun (X Y : Type)
         (F : Product X Y -> Type)
         (f : forall (x : X) (y : Y), F (pair x y))
       => ident_unit f.
(* endfrag *)

(* begfrag:u70g12vv *)
Example _uncurry_curry
  : forall (X Y : Type)
           (F : Product X Y -> Type)
           (g : forall (t : Product X Y), F t),
      Ident g (uncurry (curry g))
  := fun (X Y : Type)
         (F : Product X Y -> Type)
         (g : forall (t : Product X Y), F t)
       => ident_unit g.
(* endfrag *)

(* begfrag:rdugvrpr *)
Example _pair_function_first
  : forall (T : Type)
           (F : T -> Type)
           (G : T -> Type)
           (f : forall (t : T), F t)
           (g : forall (t : T), G t)
           (t : T),
      Ident (f t) (first (pair_function f g t))
  := fun (T : Type)
         (F : T -> Type)
         (G : T -> Type)
         (f : forall   (t : T), F t)
         (g : forall (t : T), G t)
         (t : T)
       => ident_unit (f t).
(* endfrag *)

(* begfrag:z30hsvte *)
Example _pair_function_second
  : forall (T : Type)
           (F : T -> Type)
           (G : T -> Type)
           (f : forall (t : T), F t)
           (g : forall (t : T), G t)
           (t : T),
      Ident (g t) (second (pair_function f g t))
  := fun (T : Type)
         (F : T -> Type)
         (G : T -> Type)
         (f : forall   (t : T), F t)
         (g : forall (t : T), G t)
         (t : T)
       => ident_unit (g t).
(* endfrag *)

(* begfrag:sh7mqmkt *)
Example _product_map_first
  : forall (X Y X' Y' : Type)
           (f : X -> X')
           (g : Y -> Y'),
      Ident (function_compose f first)
            (function_compose first (product_map f g))
  := fun (X Y X' Y' : Type)
         (f : X -> X')
         (g : Y -> Y')
       => ident_unit (function_compose f first).
(* endfrag *)

(* begfrag:2cjp777x *)
Example _product_map_second
  : forall (X Y X' Y' : Type)
           (f : X -> X')
           (g : Y -> Y'),
      Ident (function_compose g second)
            (function_compose second (product_map f g))
  := fun (X Y X' Y' : Type)
         (f : X -> X')
         (g : Y -> Y')
       => ident_unit (function_compose g second).
(* endfrag *)

(* ================================================================ *)
(** ** Sum types                                                    *)
(* ================================================================ *)

(* begfrag:hut1r4st *)
Example _sum_induction_left
  : forall (X Y : Type)
           (F : Sum X Y -> Type)
           (f : forall (x : X), F (left x))
           (g : forall (y : Y), F (right y)),
      Ident f (function_compose (sum_induction F f g) left)
  := fun (X Y : Type)
         (F : Sum X Y -> Type)
         (f : forall (x : X), F (left x))
         (g : forall (y : Y), F (right y))
       => ident_unit f.
(* endfrag *)

(* begfrag:w7zh5r1a *)
Example _sum_induction_right
  : forall (X Y : Type)
           (F : Sum X Y -> Type)
           (f : forall (x : X), F (left x))
           (g : forall (y : Y), F (right y)),
      Ident g (function_compose (sum_induction F f g) right)
  := fun (X Y : Type)
         (F : Sum X Y -> Type)
         (f : forall (x : X), F (left x))
         (g : forall (y : Y), F (right y))
       => ident_unit g.
(* endfrag *)

(* begfrag:jwfgf3zw *)
Example _sum_recursion_left
  : forall (X Y Z : Type)
           (f : X -> Z)
           (g : Y -> Z),
      Ident f (function_compose (sum_recursion f g) left)
  := fun (X Y Z : Type)
         (f : X -> Z)
         (g : Y -> Z)
       => ident_unit f.
(* endfrag *)

(* begfrag:ll3xza2h *)
Example _sum_recursion_right
  : forall (X Y Z : Type)
           (f : X -> Z)
           (g : Y -> Z),
      Ident g (function_compose (sum_recursion f g) right)
  := fun (X Y Z : Type)
         (f : X -> Z)
         (g : Y -> Z)
       => ident_unit g.
(* endfrag *)

(* begfrag:eb0iol83 *)
Example _sum_map_left
  : forall (X Y X' Y' : Type)
           (f : X -> X')
           (g : Y -> Y'),
      Ident (function_compose left f)
            (function_compose (sum_map f g) left)
  := fun (X Y X' Y' : Type)
         (f : X -> X')
         (g : Y -> Y')
       => ident_unit (function_compose left f).
(* endfrag *)

(* begfrag:minkb801 *)
Example _sum_map_right
  : forall (X Y X' Y' : Type)
           (f : X -> X')
           (g : Y -> Y'),
      Ident (function_compose right g)
            (function_compose (sum_map f g) right)
  := fun (X Y X' Y' : Type)
         (f : X -> X')
         (g : Y -> Y')
       => ident_unit (function_compose right g).
(* endfrag *)

(* ================================================================ *)
(** ** Identity types again                                         *)
(* ================================================================ *)

(* begfrag:7c62tbn3 *)
Example _ident_right_unit_ident_unit
  : forall (X : Type) (x : X),
      Ident (ident_unit (ident_unit x))
            (ident_right_unit (ident_unit x))
  := fun (X : Type) (x : X) => ident_unit (ident_unit (ident_unit x)).
(* endfrag *)

(* begfrag:i00h874x *)
Example _ident_associative_ident_unit
  : forall (X : Type) (x y z : X) (q : Ident x y) (r : Ident y z),
      Ident (ident_unit (ident_compose q r))
            (ident_associative (ident_unit x) q r)
  := fun (X : Type) (x y z : X) (q : Ident x y) (r : Ident y z)
       => ident_unit (ident_unit (ident_compose q r)).
(* endfrag *)

(* begfrag:qiu7nu2e *)
Example _ident_left_inverse_ident_unit
  : forall (X : Type) (x : X),
      Ident (ident_unit (ident_unit x))
            (ident_left_inverse (ident_unit x))
  := fun (X : Type) (x : X) => ident_unit (ident_unit (ident_unit x)).
(* endfrag *)

(* begfrag:1ysdcngb *)
Example _ident_right_inverse_ident_unit
  : forall (X : Type) (x : X),
      Ident (ident_unit (ident_unit x))
            (ident_right_inverse (ident_unit x))
  := fun (X : Type) (x : X) => ident_unit (ident_unit (ident_unit x)).
(* endfrag *)

(* begfrag:k8d40n87 *)
Example _ident_map_multiplicative_ident_unit
  : forall (X Y : Type) (f : X -> Y) (x y : X) (q : Ident x y),
      Ident (ident_unit (ident_map f q))
            (ident_map_multiplicative f (ident_unit x) q)
  := fun (X Y : Type) (f : X -> Y) (x y : X) (q : Ident x y)
       => ident_unit (ident_unit (ident_map f q)).
(* endfrag *)

(* begfrag:pp439rp8 *)
Example _ident_map_inverse_ident_unit
  : forall (X Y : Type) (f : X -> Y) (x : X),
      Ident (ident_unit (ident_unit (f x)))
            (ident_map_inverse f (ident_unit x))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       => ident_unit (ident_unit (ident_unit (f x))).
(* endfrag *)

(* begfrag:kr2uop9n *)
Example _ident_map_ident_ident_unit
  : forall (X Y : Type) (f : X -> Y) (x y : X) (p : Ident x y),
      Ident (ident_unit (ident_map f p))
            (ident_map_ident f (ident_unit p))
  := fun (X Y : Type) (f : X -> Y) (x y : X) (p : Ident x y)
       => ident_unit (ident_unit (ident_map f p)).
(* endfrag:kr2uop9n *)

(* begfrag:vh3jhxbw *)
Example _ident_map_function_unit_ident_unit
  : forall (X : Type) (x : X),
      Ident (ident_unit (ident_unit x))
            (ident_map_function_unit (ident_unit x))
  := fun (X : Type) (x : X) => ident_unit (ident_unit (ident_unit x)).
(* endfrag *)

(* begfrag:tubw30mh *)
Example _ident_map_function_compose_ident_unit
  : forall (X Y Z : Type) (g : Y -> Z) (f : X -> Y) (x : X),
      Ident (ident_unit (ident_unit (g (f x))))
            (ident_map_function_compose g f (ident_unit x))
  := fun (X Y Z : Type) (g : Y -> Z) (f : X -> Y) (x : X)
       => ident_unit (ident_unit (ident_unit (g (f x)))).
(* endfrag *)

(* begfrag:8d4ystf4 *)
Example _ident_map_constant_function_ident_unit
  : forall (X Y : Type) (y : Y) (x : X),
      Ident (ident_unit (ident_unit y))
            (ident_map_constant_function y (ident_unit x))
  := fun (X Y : Type) (y : Y) (x : X)
       => ident_unit (ident_unit (ident_unit y)).
(* endfrag *)

(* begfrag:o1fq5t5n *)
Example _ident_left_cancel_ident_unit
  : forall (X : Type) (x y : X) (q q' : Ident x y),
      Ident (function_unit (Ident q q'))
            (ident_left_cancel (ident_unit x) q q')
  := fun (X : Type) (x y : X) (q q' : Ident x y)
       => ident_unit (function_unit (Ident q q')).
(* endfrag *)

(* begfrag:benyiuaw *)
Example _ident_left_remove_ident_unit
  : forall (X : Type)
           (x y : X)
           (p : Ident x y)
           (z : X)
           (q q' : Ident y z),
      Ident (ident_left_cancel p q q')
            (ident_left_remove (ident_unit p) q q')
  := fun (X : Type)
         (x y : X)
         (p : Ident x y)
         (z : X)
         (q q' : Ident y z)
       => ident_unit (ident_left_cancel p q q').
(* endfrag *)

(* begfrag:6udh8p9g *)
Example _ident_right_cancel_ident_unit
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (u : Ident (ident_compose p (ident_unit y))
                      (ident_compose p' (ident_unit y))),
      Ident (ident_compose (ident_compose (ident_right_unit p) u)
                           (ident_inverse (ident_right_unit p')))
            (ident_right_cancel p p' (ident_unit y) u)
  := fun (X : Type)
         (x y : X)
         (p p' : Ident x y)
         (u : Ident (ident_compose p (ident_unit y))
                    (ident_compose p' (ident_unit y)))
       => ident_unit (ident_right_cancel p p' (ident_unit y) u).
(* endfrag *)

(* begfrag:6r77n5me *)
Example _ident_right_remove_ident_unit
  : forall (X : Type)
           (x y : X)
           (p p' : Ident x y)
           (z : X)
           (q : Ident y z),
      Ident (ident_right_cancel p p' q)
            (ident_right_remove p p' (ident_unit q))
  := fun (X : Type)
         (x y : X)
         (p p' : Ident x y)
         (z : X)
         (q : Ident y z)
       => ident_unit (ident_right_cancel p p' q).
(* endfrag *)

(* begfrag:4pwxwrcf *)
Example _ident_right_unit_unique_ident_unit
  : forall (X : Type) (x : X) (q : Ident x x),
      Ident (function_unit (Ident (ident_unit x) q))
            (ident_right_unit_unique q)
  := fun (X : Type) (x : X) (q : Ident x x)
       => ident_unit (function_unit (Ident (ident_unit x) q)).
(* endfrag *)

(* begfrag:kr5zr15p *)
Example _ident_left_inverse_unique_ident_unit
  : forall (X : Type) (x : X),
      Ident (fun (q : Ident x x) (e : Ident q (ident_unit x))
               => ident_inverse (ident_map ident_inverse e))
            (ident_left_inverse_unique (ident_unit x))
  := fun (X : Type) (x : X)
       => ident_unit (ident_left_inverse_unique (ident_unit x)).
(* endfrag:kr5zr15p *)

(* begfrag:kr5zw3bu *)
Example _ident_right_inverse_unique_ident_unit
  : forall (X : Type) (x : X),
      Ident (fun (q : Ident x x)
               => function_unit (Ident q (ident_unit x)))
            (ident_right_inverse_unique (ident_unit x))
  := fun (X : Type) (x : X)
       => ident_unit (ident_right_inverse_unique (ident_unit x)).
(* endfrag:kr5zw3bu *)

(* begfrag:kr60ne8y *)
Example _ident_inverse_antimultiplicative_ident_unit
  : forall (X : Type) (x : X),
      Ident (fun (z : X) (q : Ident x z)
               => ident_right_unit (ident_inverse q))
            (@ident_inverse_antimultiplicative X x x (ident_unit x))
  := fun (X : Type) (x : X)
       => ident_unit
            (@ident_inverse_antimultiplicative X x x (ident_unit x)).
(* endfrag:kr60ne8y *)

(* begfrag:kr60xeqv *)
Example _ident_inverse_involutive_ident_unit
  : forall (X : Type) (x : X),
      Ident (ident_unit (ident_unit x))
            (ident_inverse_involutive (ident_unit x))
  := fun (X : Type) (x : X)
       => ident_unit (ident_unit (ident_unit x)).
(* endfrag:kr60xeqv *)

(* begfrag:kr611bsz *)
Example _ident_put_inverse_ident_unit
  : forall (X : Type) (x y : X) (p : Ident x y),
      Ident (ident_unit (ident_inverse p))
            (ident_put_inverse (ident_unit p))
  := fun (X : Type) (x y : X) (p : Ident x y)
       => ident_unit (ident_unit (ident_inverse p)).
(* endfrag:kr611bsz *)

(* begfrag:a9yciaq6 *)
Example _ident_move_prefix_right_ident_unit
  : forall (X : Type) (x z : X) (q r : Ident x z),
      Ident (function_unit (Ident q r))
            (ident_move_prefix_right (ident_unit x) q)
  := fun (X : Type) (x z : X) (q r : Ident x z)
       => ident_unit (function_unit (Ident q r)).
(* endfrag *)

(* begfrag:r8vhvl7l *)
Example _ident_move_prefix_left_ident_unit
  : forall (X : Type) (x z : X) (q r : Ident x z),
      Ident (function_unit (Ident r q))
            (ident_move_prefix_left (ident_unit x) q)
  := fun (X : Type) (x z : X) (q r : Ident x z)
       => ident_unit (function_unit (Ident r q)).
(* endfrag *)

(* begfrag:sjeygzmw *)
Example _ident_left_whisker_ident_unit
  : forall (X : Type) (x z : X) (q q' : Ident x z),
      Ident (function_unit (Ident q q'))
            (ident_left_whisker (ident_unit x))
  := fun (X : Type) (x z : X) (q q' : Ident x z)
       => ident_unit (function_unit (Ident q q')).
(* endfrag *)

(* begfrag:2fxkvz8a *)
Example _ident_right_whisker_ident_unit
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

(* End of file *)
