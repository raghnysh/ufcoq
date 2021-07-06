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
      => reflexive f.
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
       => reflexive (function_compose (function_compose g f) e).
(* endfrag *)

(* begfrag:hso05la4 *)
Example _function_compose_left_unit
  : forall (X Y : Type) (f : X -> Y),
      Equal f (function_compose (@identity_function Y) f)
  := fun (X Y : Type) (f : X -> Y)
       => reflexive f.
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
       => reflexive g.
(* endfrag *)

(* ================================================================ *)
(** ** The true type                                                *)
(* ================================================================ *)

(* begfrag:tuh9sgix *)
Example _true_induction_only
  : forall (F : True -> Type) (x : F only),
      Equal x (true_induction F x only)
  := fun (F : True -> Type) (x : F only)
       => reflexive x.
(* endfrag *)

(* begfrag:iww5ck0g *)
Example _true_recursion_only
  : forall (X : Type) (x : X), Equal x (true_recursion x only)
  := fun (X : Type) (x : X) => reflexive x.
(* endfrag *)

(* begfrag:qgyqpcz3 *)
Example _to_true_only
  : forall (X : Type) (x : X), Equal only (to_true x)
  := fun (X : Type) (x : X) => reflexive only.
(* endfrag *)

(* ================================================================ *)
(** ** The Boolean type                                             *)
(* ================================================================ *)

(* begfrag:ogo7jox4 *)
Example _boolean_induction_yes
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Equal y (boolean_induction F y n yes)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => reflexive y.
(* endfrag *)

(* begfrag:6ly41ngr *)
Example _boolean_induction_no
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Equal n (boolean_induction F y n no)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => reflexive n.
(* endfrag *)

(* begfrag:2wynnkw2 *)
Example _boolean_recursion_yes
  : forall (X : Type) (y n : X), Equal y (boolean_recursion y n yes)
  := fun (X : Type) (y n : X) => reflexive y.
(* endfrag *)

(* begfrag:4cga60mp *)
Example _boolean_recursion_no
  : forall (X : Type) (y n : X), Equal n (boolean_recursion y n no)
  := fun (X : Type) (y n : X) => reflexive n.
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
       => reflexive z.
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
       => reflexive (s n (natural_induction F z s n)).
(* endfrag *)

(* begfrag:rzfhv79d *)
Example _natural_recursion_zero
  : forall (X : Type) (z : X) (s : Natural -> X -> X),
      Equal z (natural_recursion z s zero)
  := fun (X : Type) (z : X) (s : Natural -> X -> X)
       => reflexive z.
(* endfrag *)

(* begfrag:hrrncvpb *)
Example _natural_recursion_successor
  : forall (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural),
      Equal (s n (natural_recursion z s n))
            (natural_recursion z s (successor n))
  := fun (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural)
     => reflexive (s n (natural_recursion z s n)).
(* endfrag *)

(* begfrag:upakg9n0 *)
Example _natural_recursion_simple_zero
  : forall (X : Type) (z : X) (s : X -> X),
      Equal z (natural_recursion_simple z s zero)
  := fun (X : Type) (z : X) (s : X -> X)
       => reflexive z.
(* endfrag *)

(* begfrag:tsfievor *)
Example _natural_recursion_simple_successor
  : forall (X : Type) (z : X) (s : X -> X) (n : Natural),
      Equal (s (natural_recursion_simple z s n))
            (natural_recursion_simple z s (successor n))
  := fun (X : Type) (z : X) (s : X -> X) (n : Natural)
       => reflexive (s (natural_recursion_simple z s n)).
(* endfrag *)

(* ================================================================ *)
(** ** Equality types                                               *)
(* ================================================================ *)

(* begfrag:fznk9p3u *)
Example _equal_induction_reflexive
  : forall (X : Type)
           (x : X)
           (F : forall (y : X), Equal x y -> Type)
           (e : F x (reflexive x)),
      Equal e (equal_induction x F e x (reflexive x))
  := fun (X : Type)
         (x : X)
         (F : forall (y : X), Equal x y -> Type)
         (e : F x (reflexive x))
       => reflexive e.
(* endfrag *)

(* begfrag:obnor2k3 *)
Example _transport_reflexive
  : forall (X : Type) (F : X -> Type) (x y : X),
      Equal (@identity_function (F x)) (transport F (reflexive x))
  := fun (X : Type) (F : X -> Type) (x y : X)
       => reflexive (@identity_function (F x)).
(* endfrag *)

(* begfrag:iqo3w2uh *)
Example _transport_inverse_reflexive
  : forall (X : Type) (F : X -> Type) (x y : X),
      Equal (@identity_function (F x))
            (transport_inverse F (reflexive x))
  := fun (X : Type) (F : X -> Type) (x y : X)
       => reflexive (@identity_function (F x)).
(* endfrag *)

(* ================================================================ *)
(** ** Sigma types                                                  *)
(* ================================================================ *)

(* begfrag:qts05vtg *)
Example _sigma_type_eta_conversion
  : forall (X : Type) (F : X -> Type) (t : Sigma (x : X), F x),
      Equal t (sigma F (sigma1 t) (sigma2 t))
  := fun (X : Type) (F : X -> Type) (t : Sigma (x : X), F x)
       => reflexive t.
(* endfrag *)

(* begfrag:mrl11i2o *)
Example _sigma_curry_uncurry
  : forall (X : Type)
           (F : X -> Type)
           (G : (Sigma (x : X), F x) -> Type)
           (f : forall (x : X) (y : F x), G (sigma F x y)),
      Equal f (sigma_curry (sigma_uncurry f))
  := fun (X : Type)
         (F : X -> Type)
         (G : (Sigma (x : X), F x) -> Type)
         (f : forall (x : X) (y : F x), G (sigma F x y))
       => reflexive f.
(* endfrag *)

(* begfrag:4zlly4cd *)
Example _sigma_uncurry_curry
  : forall (X : Type)
           (F : X -> Type)
           (G : (Sigma (x : X), F x) -> Type)
           (g : forall (t : Sigma (x : X), F x), G t),
      Equal g (sigma_uncurry (sigma_curry g))
  := fun (X : Type)
         (F : X -> Type)
         (G : (Sigma (x : X), F x) -> Type)
         (g : forall (t : Sigma (x : X), F x), G t)
       => reflexive g.
(* endfrag *)

(* ================================================================ *)
(** ** Product types                                                *)
(* ================================================================ *)

(* begfrag:wruha80w *)
Example _product_eta_conversion
  : forall (X Y : Type) (t : Product X Y),
      Equal t (pair (first t) (second t))
  := fun (X Y : Type) (t : Product X Y)
       => reflexive t.
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
       => reflexive f.
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
       => reflexive g.
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
       => reflexive (f t).
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
       => reflexive (g t).
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
       => reflexive (function_compose f first).
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
       => reflexive (function_compose g second).
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
       => reflexive f.
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
       => reflexive g.
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
       => reflexive f.
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
       => reflexive g.
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
       => reflexive (function_compose left f).
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
       => reflexive (function_compose right g).
(* endfrag *)

(* ================================================================ *)
(** ** Equality types again                                         *)
(* ================================================================ *)

(* begfrag:7c62tbn3 *)
Example _equal_right_unit_reflexive
  : forall (X : Type) (x : X),
      Equal (reflexive (reflexive x)) (equal_right_unit (reflexive x))
  := fun (X : Type) (x : X) => reflexive (reflexive (reflexive x)).
(* endfrag *)

(* begfrag:i00h874x *)
Example _equal_associative_reflexive
  : forall (X : Type) (x y z : X) (q : Equal x y) (r : Equal y z),
      Equal (reflexive (equal_compose q r))
            (equal_associative (reflexive x) q r)
  := fun (X : Type) (x y z : X) (q : Equal x y) (r : Equal y z)
       => reflexive (reflexive (equal_compose q r)).
(* endfrag *)

(* begfrag:2fxkvz8a *)
Example _equal_compose_left_equal_reflexive
  : forall (X : Type) (x y : X) (p : Equal x y) (z : X) (q : Equal y z),
      Equal (reflexive (equal_compose p q))
            (equal_compose_left_equal (reflexive p) q)
  := fun (X : Type) (x y : X) (p : Equal x y) (z : X) (q : Equal y z)
       => reflexive (reflexive (equal_compose p q)).
(* endfrag *)

(* begfrag:sjeygzmw *)
Example _equal_compose_right_equal_reflexive
  : forall (X : Type) (x y : X) (p : Equal x y) (z : X) (q : Equal y z),
      Equal (reflexive (equal_compose p q))
            (equal_compose_right_equal p (reflexive q))
  := fun (X : Type) (x y : X) (p : Equal x y) (z : X) (q : Equal y z)
       => reflexive (reflexive (equal_compose p q)).
(* endfrag *)

(* begfrag:zo8r3is0 *)
Example _equal_compose_equal_reflexive1
  : forall (X : Type)
           (x y z : X)
           (p : Equal x y)
           (q q' : Equal y z)
           (v : Equal q q'),
      Equal (equal_compose_right_equal p v)
            (equal_compose_equal (reflexive p) v)
  := fun (X : Type)
         (x y z : X)
         (p : Equal x y)
         (q q' : Equal y z)
         (v : Equal q q')
       => reflexive (equal_compose_right_equal p v).
(* endfrag *)

(* begfrag:d2ojj3vr *)
Example _equal_compose_equal_reflexive2
  : forall (X : Type)
           (x y z : X)
           (p p' : Equal x y)
           (q : Equal y z)
           (u : Equal p p'),
      Equal (equal_compose_left_equal u q)
            (equal_compose_equal u (reflexive q))
  := fun (X : Type)
         (x y z : X)
         (p p' : Equal x y)
         (q : Equal y z)
         (u : Equal p p')
       => equal_right_unit (equal_compose_left_equal u q).
(* endfrag *)

(* begfrag:zk4k7yn8 *)
Example _equal_compose_equal_reflexive12
  : forall (X : Type)
           (x y z : X)
           (p : Equal x y)
           (q : Equal y z),
      Equal (reflexive (equal_compose p q))
            (equal_compose_equal (reflexive p) (reflexive q))
  := fun (X : Type)
         (x y z : X)
         (p : Equal x y)
         (q : Equal y z)
       => reflexive (reflexive (equal_compose p q)).
(* endfrag *)

(* End of file *)