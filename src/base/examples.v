(* Some examples arising from other modules *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:909vtogz *)
Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.
Require Import ufcoq.base.equal.
(* endfrag *)

(* ================================================================ *)
(** ** Function types                                               *)
(* ================================================================ *)

(* begfrag:ryjyw5yo *)
Example _function_eta_conversion
  : forall (X : Type) (F : X -> Type) (f : forall (x : X), F x),
      Equal f (fun (x : X) => f x)
  := fun (X : Type) (F : X -> Type) (f : forall (x : X), F x)
      => equal_unit f.
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
      Equal (function_compose (function_compose g f) e)
            (function_compose g (function_compose f e))
  := fun (W : Type)
         (X : Type)
         (Y : Type)
         (G : Y -> Type)
         (g : forall (y : Y), G y)
         (f : X -> Y)
         (e : W -> X)
       => equal_unit (function_compose (function_compose g f) e).
(* endfrag *)

(* begfrag:hso05la4 *)
Example _function_compose_left_unit
  : forall (X Y : Type) (f : X -> Y),
      Equal f (function_compose (@identity_function Y) f)
  := fun (X Y : Type) (f : X -> Y)
       => equal_unit f.
(* endfrag *)

(* begfrag:ey5cl868 *)
Example _function_compose_right_unit
  : forall (X : Type)
           (G : X -> Type)
           (g : forall (x : X), G x),
      Equal g (function_compose  g (@identity_function X))
  := fun (X : Type)
         (G : X -> Type)
         (g : forall (x : X), G x)
       => equal_unit g.
(* endfrag *)

(* ================================================================ *)
(** ** The true type                                                *)
(* ================================================================ *)

(* begfrag:tuh9sgix *)
Example _true_induction_only
  : forall (F : True -> Type) (x : F only),
      Equal x (true_induction F x only)
  := fun (F : True -> Type) (x : F only)
       => equal_unit x.
(* endfrag *)

(* begfrag:iww5ck0g *)
Example _true_recursion_only
  : forall (X : Type) (x : X), Equal x (true_recursion x only)
  := fun (X : Type) (x : X) => equal_unit x.
(* endfrag *)

(* begfrag:qgyqpcz3 *)
Example _to_true_only
  : forall (X : Type) (x : X), Equal only (to_true x)
  := fun (X : Type) (x : X) => equal_unit only.
(* endfrag *)

(* ================================================================ *)
(** ** The Boolean type                                             *)
(* ================================================================ *)

(* begfrag:ogo7jox4 *)
Example _boolean_induction_yes
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Equal y (boolean_induction F y n yes)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => equal_unit y.
(* endfrag *)

(* begfrag:6ly41ngr *)
Example _boolean_induction_no
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Equal n (boolean_induction F y n no)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => equal_unit n.
(* endfrag *)

(* begfrag:2wynnkw2 *)
Example _boolean_recursion_yes
  : forall (X : Type) (y n : X), Equal y (boolean_recursion y n yes)
  := fun (X : Type) (y n : X) => equal_unit y.
(* endfrag *)

(* begfrag:4cga60mp *)
Example _boolean_recursion_no
  : forall (X : Type) (y n : X), Equal n (boolean_recursion y n no)
  := fun (X : Type) (y n : X) => equal_unit n.
(* endfrag *)

(* ================================================================ *)
(** ** The type of natural numbers                                  *)
(* ================================================================ *)

(* begfrag:p33ig2te *)
Example _natural_induction_zero
  : forall (F : Natural -> Type)
           (z : F zero)
           (s : forall (n : Natural), F n -> F (successor n)),
      Equal z (natural_induction F z s zero)
  := fun (F : Natural -> Type)
         (z : F zero)
         (s : forall (n : Natural), F n -> F (successor n))
       => equal_unit z.
(* endfrag *)

(* begfrag:ojb7dh9z *)
Example _natural_induction_successor
  : forall (F : Natural -> Type)
           (z : F zero)
           (s : forall (n : Natural), F n -> F (successor n))
           (n : Natural),
      Equal (s n (natural_induction F z s n))
            (natural_induction F z s (successor n))
  := fun (F : Natural -> Type)
         (z : F zero)
         (s : forall (n : Natural), F n -> F (successor n))
         (n : Natural)
       => equal_unit (s n (natural_induction F z s n)).
(* endfrag *)

(* begfrag:rzfhv79d *)
Example _natural_recursion_zero
  : forall (X : Type) (z : X) (s : Natural -> X -> X),
      Equal z (natural_recursion z s zero)
  := fun (X : Type) (z : X) (s : Natural -> X -> X)
       => equal_unit z.
(* endfrag *)

(* begfrag:hrrncvpb *)
Example _natural_recursion_successor
  : forall (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural),
      Equal (s n (natural_recursion z s n))
            (natural_recursion z s (successor n))
  := fun (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural)
     => equal_unit (s n (natural_recursion z s n)).
(* endfrag *)

(* begfrag:upakg9n0 *)
Example _natural_recursion_simple_zero
  : forall (X : Type) (z : X) (s : X -> X),
      Equal z (natural_recursion_simple z s zero)
  := fun (X : Type) (z : X) (s : X -> X)
       => equal_unit z.
(* endfrag *)

(* begfrag:tsfievor *)
Example _natural_recursion_simple_successor
  : forall (X : Type) (z : X) (s : X -> X) (n : Natural),
      Equal (s (natural_recursion_simple z s n))
            (natural_recursion_simple z s (successor n))
  := fun (X : Type) (z : X) (s : X -> X) (n : Natural)
       => equal_unit (s (natural_recursion_simple z s n)).
(* endfrag *)

(* ================================================================ *)
(** ** Equality types                                               *)
(* ================================================================ *)

(* begfrag:fznk9p3u *)
Example _equal_induction_equal_unit
  : forall (X : Type)
           (x : X)
           (F : forall (y : X), Equal x y -> Type)
           (e : F x (equal_unit x)),
      Equal e (equal_induction x F e x (equal_unit x))
  := fun (X : Type)
         (x : X)
         (F : forall (y : X), Equal x y -> Type)
         (e : F x (equal_unit x))
       => equal_unit e.
(* endfrag *)

(* begfrag:obnor2k3 *)
Example _transport_equal_unit
  : forall (X : Type) (F : X -> Type) (x y : X),
      Equal (@identity_function (F x)) (transport F (equal_unit x))
  := fun (X : Type) (F : X -> Type) (x y : X)
       => equal_unit (@identity_function (F x)).
(* endfrag *)

(* begfrag:iqo3w2uh *)
Example _transport_inverse_equal_unit
  : forall (X : Type) (F : X -> Type) (x y : X),
      Equal (@identity_function (F x))
            (transport_inverse F (equal_unit x))
  := fun (X : Type) (F : X -> Type) (x y : X)
       => equal_unit (@identity_function (F x)).
(* endfrag *)

(* ================================================================ *)
(** ** Sigma types                                                  *)
(* ================================================================ *)

(* begfrag:qts05vtg *)
Example _sigma_type_eta_conversion
  : forall (X : Type) (F : X -> Type) (t : Sigma F),
      Equal t (sigma F (sigma1 t) (sigma2 t))
  := fun (X : Type) (F : X -> Type) (t : Sigma F)
       => equal_unit t.
(* endfrag *)

(* begfrag:mrl11i2o *)
Example _sigma_curry_uncurry
  : forall (X : Type)
           (F : X -> Type)
           (G : Sigma F -> Type)
           (f : forall (x : X) (y : F x), G (sigma F x y)),
      Equal f (sigma_curry (sigma_uncurry f))
  := fun (X : Type)
         (F : X -> Type)
         (G : Sigma F -> Type)
         (f : forall (x : X) (y : F x), G (sigma F x y))
       => equal_unit f.
(* endfrag *)

(* begfrag:4zlly4cd *)
Example _sigma_uncurry_curry
  : forall (X : Type)
           (F : X -> Type)
           (G : Sigma F -> Type)
           (g : forall (t : Sigma F), G t),
      Equal g (sigma_uncurry (sigma_curry g))
  := fun (X : Type)
         (F : X -> Type)
         (G : Sigma F -> Type)
         (g : forall (t : Sigma F), G t)
       => equal_unit g.
(* endfrag *)

(* ================================================================ *)
(** ** Product types                                                *)
(* ================================================================ *)

(* begfrag:wruha80w *)
Example _product_eta_conversion
  : forall (X Y : Type) (t : Product X Y),
      Equal t (pair (first t) (second t))
  := fun (X Y : Type) (t : Product X Y)
       => equal_unit t.
(* endfrag *)

(* begfrag:h1vgtr2g *)
Example _curry_uncurry
  : forall (X Y : Type)
           (F : Product X Y -> Type)
           (f : forall (x : X) (y : Y), F (pair x y)),
        Equal f (curry (uncurry f))
  := fun (X Y : Type)
         (F : Product X Y -> Type)
         (f : forall (x : X) (y : Y), F (pair x y))
       => equal_unit f.
(* endfrag *)

(* begfrag:u70g12vv *)
Example _uncurry_curry
  : forall (X Y : Type)
           (F : Product X Y -> Type)
           (g : forall (t : Product X Y), F t),
      Equal g (uncurry (curry g))
  := fun (X Y : Type)
         (F : Product X Y -> Type)
         (g : forall (t : Product X Y), F t)
       => equal_unit g.
(* endfrag *)

(* begfrag:rdugvrpr *)
Example _pair_function_first
  : forall (T : Type)
           (F : T -> Type)
           (G : T -> Type)
           (f : forall (t : T), F t)
           (g : forall (t : T), G t)
           (t : T),
      Equal (f t) (first (pair_function f g t))
  := fun (T : Type)
         (F : T -> Type)
         (G : T -> Type)
         (f : forall   (t : T), F t)
         (g : forall (t : T), G t)
         (t : T)
       => equal_unit (f t).
(* endfrag *)

(* begfrag:z30hsvte *)
Example _pair_function_second
  : forall (T : Type)
           (F : T -> Type)
           (G : T -> Type)
           (f : forall (t : T), F t)
           (g : forall (t : T), G t)
           (t : T),
      Equal (g t) (second (pair_function f g t))
  := fun (T : Type)
         (F : T -> Type)
         (G : T -> Type)
         (f : forall   (t : T), F t)
         (g : forall (t : T), G t)
         (t : T)
       => equal_unit (g t).
(* endfrag *)

(* begfrag:sh7mqmkt *)
Example _product_map_first
  : forall (X Y X' Y' : Type)
           (f : X -> X')
           (g : Y -> Y'),
      Equal (function_compose f first)
            (function_compose first (product_map f g))
  := fun (X Y X' Y' : Type)
         (f : X -> X')
         (g : Y -> Y')
       => equal_unit (function_compose f first).
(* endfrag *)

(* begfrag:2cjp777x *)
Example _product_map_second
  : forall (X Y X' Y' : Type)
           (f : X -> X')
           (g : Y -> Y'),
      Equal (function_compose g second)
            (function_compose second (product_map f g))
  := fun (X Y X' Y' : Type)
         (f : X -> X')
         (g : Y -> Y')
       => equal_unit (function_compose g second).
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
      Equal f (function_compose (sum_induction F f g) left)
  := fun (X Y : Type)
         (F : Sum X Y -> Type)
         (f : forall (x : X), F (left x))
         (g : forall (y : Y), F (right y))
       => equal_unit f.
(* endfrag *)

(* begfrag:w7zh5r1a *)
Example _sum_induction_right
  : forall (X Y : Type)
           (F : Sum X Y -> Type)
           (f : forall (x : X), F (left x))
           (g : forall (y : Y), F (right y)),
      Equal g (function_compose (sum_induction F f g) right)
  := fun (X Y : Type)
         (F : Sum X Y -> Type)
         (f : forall (x : X), F (left x))
         (g : forall (y : Y), F (right y))
       => equal_unit g.
(* endfrag *)

(* begfrag:jwfgf3zw *)
Example _sum_recursion_left
  : forall (X Y Z : Type)
           (f : X -> Z)
           (g : Y -> Z),
      Equal f (function_compose (sum_recursion f g) left)
  := fun (X Y Z : Type)
         (f : X -> Z)
         (g : Y -> Z)
       => equal_unit f.
(* endfrag *)

(* begfrag:ll3xza2h *)
Example _sum_recursion_right
  : forall (X Y Z : Type)
           (f : X -> Z)
           (g : Y -> Z),
      Equal g (function_compose (sum_recursion f g) right)
  := fun (X Y Z : Type)
         (f : X -> Z)
         (g : Y -> Z)
       => equal_unit g.
(* endfrag *)

(* begfrag:eb0iol83 *)
Example _sum_map_left
  : forall (X Y X' Y' : Type)
           (f : X -> X')
           (g : Y -> Y'),
      Equal (function_compose left f)
            (function_compose (sum_map f g) left)
  := fun (X Y X' Y' : Type)
         (f : X -> X')
         (g : Y -> Y')
       => equal_unit (function_compose left f).
(* endfrag *)

(* begfrag:minkb801 *)
Example _sum_map_right
  : forall (X Y X' Y' : Type)
           (f : X -> X')
           (g : Y -> Y'),
      Equal (function_compose right g)
            (function_compose (sum_map f g) right)
  := fun (X Y X' Y' : Type)
         (f : X -> X')
         (g : Y -> Y')
       => equal_unit (function_compose right g).
(* endfrag *)

(* ================================================================ *)
(** ** Equality types again                                         *)
(* ================================================================ *)

(* begfrag:7c62tbn3 *)
Example _equal_right_unit_equal_unit
  : forall (X : Type) (x : X),
      Equal (equal_unit (equal_unit x))
            (equal_right_unit (equal_unit x))
  := fun (X : Type) (x : X) => equal_unit (equal_unit (equal_unit x)).
(* endfrag *)

(* begfrag:i00h874x *)
Example _equal_associative_equal_unit
  : forall (X : Type) (x y z : X) (q : Equal x y) (r : Equal y z),
      Equal (equal_unit (equal_compose q r))
            (equal_associative (equal_unit x) q r)
  := fun (X : Type) (x y z : X) (q : Equal x y) (r : Equal y z)
       => equal_unit (equal_unit (equal_compose q r)).
(* endfrag *)

(* begfrag:qiu7nu2e *)
Example _equal_left_inverse_equal_unit
  : forall (X : Type) (x : X),
      Equal (equal_unit (equal_unit x))
            (equal_left_inverse (equal_unit x))
  := fun (X : Type) (x : X) => equal_unit (equal_unit (equal_unit x)).
(* endfrag *)

(* begfrag:1ysdcngb *)
Example _equal_right_inverse_equal_unit
  : forall (X : Type) (x : X),
      Equal (equal_unit (equal_unit x))
            (equal_right_inverse (equal_unit x))
  := fun (X : Type) (x : X) => equal_unit (equal_unit (equal_unit x)).
(* endfrag *)

(* begfrag:k8d40n87 *)
Example _equal_map_multiplicative_equal_unit
  : forall (X Y : Type) (f : X -> Y) (x y : X) (q : Equal x y),
      Equal (equal_unit (equal_map f q))
            (equal_map_multiplicative f (equal_unit x) q)
  := fun (X Y : Type) (f : X -> Y) (x y : X) (q : Equal x y)
       => equal_unit (equal_unit (equal_map f q)).
(* endfrag *)

(* begfrag:pp439rp8 *)
Example _equal_map_inverse_equal_unit
  : forall (X Y : Type) (f : X -> Y) (x : X),
      Equal (equal_unit (equal_unit (f x)))
            (equal_map_inverse f (equal_unit x))
  := fun (X Y : Type) (f : X -> Y) (x : X)
       => equal_unit (equal_unit (equal_unit (f x))).
(* endfrag *)

(* begfrag:kr2uop9n *)
Example _equal_map_equal_equal_unit
  : forall (X Y : Type) (f : X -> Y) (x y : X) (p : Equal x y),
      Equal (equal_unit (equal_map f p))
            (equal_map_equal f (equal_unit p))
  := fun (X Y : Type) (f : X -> Y) (x y : X) (p : Equal x y)
       => equal_unit (equal_unit (equal_map f p)).
(* endfrag:kr2uop9n *)

(* begfrag:vh3jhxbw *)
Example _equal_map_identity_function_equal_unit
  : forall (X : Type) (x : X),
      Equal (equal_unit (equal_unit x))
            (equal_map_identity_function (equal_unit x))
  := fun (X : Type) (x : X) => equal_unit (equal_unit (equal_unit x)).
(* endfrag *)

(* begfrag:tubw30mh *)
Example _equal_map_function_compose_equal_unit
  : forall (X Y Z : Type) (g : Y -> Z) (f : X -> Y) (x : X),
      Equal (equal_unit (equal_unit (g (f x))))
            (equal_map_function_compose g f (equal_unit x))
  := fun (X Y Z : Type) (g : Y -> Z) (f : X -> Y) (x : X)
       => equal_unit (equal_unit (equal_unit (g (f x)))).
(* endfrag *)

(* begfrag:8d4ystf4 *)
Example _equal_map_constant_function_equal_unit
  : forall (X Y : Type) (y : Y) (x : X),
      Equal (equal_unit (equal_unit y))
            (equal_map_constant_function y (equal_unit x))
  := fun (X Y : Type) (y : Y) (x : X)
       => equal_unit (equal_unit (equal_unit y)).
(* endfrag *)

(* begfrag:o1fq5t5n *)
Example _equal_left_cancel_equal_unit
  : forall (X : Type) (x y : X) (q q' : Equal x y),
      Equal (@identity_function (Equal q q'))
            (equal_left_cancel (equal_unit x) q q')
  := fun (X : Type) (x y : X) (q q' : Equal x y)
       => equal_unit (@identity_function (Equal q q')).
(* endfrag *)

(* begfrag:benyiuaw *)
Example _equal_left_remove_equal_unit
  : forall (X : Type)
           (x y : X)
           (p : Equal x y)
           (z : X)
           (q q' : Equal y z),
      Equal (equal_left_cancel p q q')
            (equal_left_remove (equal_unit p) q q')
  := fun (X : Type)
         (x y : X)
         (p : Equal x y)
         (z : X)
         (q q' : Equal y z)
       => equal_unit (equal_left_cancel p q q').
(* endfrag *)

(* begfrag:6udh8p9g *)
Example _equal_right_cancel_equal_unit
  : forall (X : Type)
           (x y : X)
           (p p' : Equal x y)
           (u : Equal (equal_compose p (equal_unit y))
                      (equal_compose p' (equal_unit y))),
      Equal (equal_compose (equal_compose (equal_right_unit p) u)
                           (equal_inverse (equal_right_unit p')))
            (equal_right_cancel p p' (equal_unit y) u)
  := fun (X : Type)
         (x y : X)
         (p p' : Equal x y)
         (u : Equal (equal_compose p (equal_unit y))
                    (equal_compose p' (equal_unit y)))
       => equal_unit (equal_right_cancel p p' (equal_unit y) u).
(* endfrag *)

(* begfrag:6r77n5me *)
Example _equal_right_remove_equal_unit
  : forall (X : Type)
           (x y : X)
           (p p' : Equal x y)
           (z : X)
           (q : Equal y z),
      Equal (equal_right_cancel p p' q)
            (equal_right_remove p p' (equal_unit q))
  := fun (X : Type)
         (x y : X)
         (p p' : Equal x y)
         (z : X)
         (q : Equal y z)
       => equal_unit (equal_right_cancel p p' q).
(* endfrag *)

(* begfrag:4pwxwrcf *)
Example _equal_right_unit_unique_equal_unit
  : forall (X : Type) (x : X) (q : Equal x x),
      Equal (@identity_function (Equal (equal_unit x) q))
            (equal_right_unit_unique q)
  := fun (X : Type) (x : X) (q : Equal x x)
       => equal_unit (@identity_function (Equal (equal_unit x) q)).
(* endfrag *)

(* begfrag:kr5zr15p *)
Example _equal_left_inverse_unique_equal_unit
  : forall (X : Type) (x : X),
      Equal (fun (q : Equal x x) (e : Equal q (equal_unit x))
               => equal_inverse (equal_map equal_inverse e))
            (equal_left_inverse_unique (equal_unit x))
  := fun (X : Type) (x : X)
       => equal_unit (equal_left_inverse_unique (equal_unit x)).
(* endfrag:kr5zr15p *)

(* begfrag:kr5zw3bu *)
Example _equal_right_inverse_unique_equal_unit
  : forall (X : Type) (x : X),
      Equal (fun (q : Equal x x)
               => @identity_function (Equal q (equal_unit x)))
            (equal_right_inverse_unique (equal_unit x))
  := fun (X : Type) (x : X)
       => equal_unit (equal_right_inverse_unique (equal_unit x)).
(* endfrag:kr5zw3bu *)

(* begfrag:kr60ne8y *)
Example _equal_inverse_antimultiplicative_equal_unit
  : forall (X : Type) (x : X),
      Equal (fun (z : X) (q : Equal x z)
               => equal_right_unit (equal_inverse q))
            (@equal_inverse_antimultiplicative
               X x x (equal_unit x))
  := fun (X : Type) (x : X)
       => equal_unit (@equal_inverse_antimultiplicative
                       X x x (equal_unit x)).
(* endfrag:kr60ne8y *)

(* begfrag:kr60xeqv *)
Example _equal_inverse_involutive_equal_unit
  : forall (X : Type) (x : X),
      Equal (equal_unit (equal_unit x))
            (equal_inverse_involutive (equal_unit x))
  := fun (X : Type) (x : X)
       => equal_unit (equal_unit (equal_unit x)).
(* endfrag:kr60xeqv *)

(* begfrag:kr611bsz *)
Example _equal_put_inverse_equal_unit
  : forall (X : Type) (x y : X) (p : Equal x y),
      Equal (equal_unit (equal_inverse p))
            (equal_put_inverse (equal_unit p))
  := fun (X : Type) (x y : X) (p : Equal x y)
       => equal_unit (equal_unit (equal_inverse p)).
(* endfrag:kr611bsz *)

(* begfrag:a9yciaq6 *)
Example _equal_move_prefix_right_equal_unit
  : forall (X : Type) (x z : X) (q r : Equal x z),
      Equal (@identity_function (Equal q r))
            (equal_move_prefix_right (equal_unit x) q)
  := fun (X : Type) (x z : X) (q r : Equal x z)
       => equal_unit (@identity_function (Equal q r)).
(* endfrag *)

(* begfrag:r8vhvl7l *)
Example _equal_move_prefix_left_equal_unit
  : forall (X : Type) (x z : X) (q r : Equal x z),
      Equal (@identity_function (Equal r q))
            (equal_move_prefix_left (equal_unit x) q)
  := fun (X : Type) (x z : X) (q r : Equal x z)
       => equal_unit (@identity_function (Equal r q)).
(* endfrag *)

(* begfrag:sjeygzmw *)
Example _equal_left_whisker_equal_unit
  : forall (X : Type) (x z : X) (q q' : Equal x z),
      Equal (@identity_function (Equal q q'))
            (equal_left_whisker (equal_unit x))
  := fun (X : Type) (x z : X) (q q' : Equal x z)
       => equal_unit (@identity_function (Equal q q')).
(* endfrag *)

(* begfrag:2fxkvz8a *)
Example _equal_right_whisker_equal_unit
  : forall (X : Type)
           (x y : X)
           (p : Equal x y)
           (z : X)
           (q : Equal y z),
      Equal (equal_unit (equal_compose p q))
            (equal_right_whisker (equal_unit p) q)
  := fun (X : Type)
         (x y : X)
         (p : Equal x y)
         (z : X)
         (q : Equal y z)
       => equal_unit (equal_unit (equal_compose p q)).
(* endfrag *)

(* End of file *)
