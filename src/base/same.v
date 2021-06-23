(* Some examples of sameness *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:base-same-dependencies *)
Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.
(* endfrag *)

(* ================================================================ *)
(** ** Function types                                               *)
(* ================================================================ *)

(* begfrag:function-eta-conversion *)
Example _function_eta_conversion
  : forall (X : Type) (F : X -> Type) (f : forall (x : X), F x),
      Equal f (fun (x : X) => f x)
  := fun (X : Type) (F : X -> Type) (f : forall (x : X), F x)
      => reflexive f.
(* endfrag *)

(* begfrag:function-compose-associative *)
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

(* begfrag:function-compose-left-unit *)
Example _function_compose_left_unit
  : forall (X Y : Type) (f : X -> Y),
      Equal f (function_compose (@identity_function Y) f)
  := fun (X Y : Type) (f : X -> Y)
       => reflexive f.
(* endfrag *)

(* begfrag:function-compose-right-unit *)
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

(* begfrag:true-induction-only *)
Example _true_induction_only
  : forall (F : True -> Type) (x : F only),
      Equal x (true_induction F x only)
  := fun (F : True -> Type) (x : F only)
       => reflexive x.
(* endfrag *)

(* begfrag:true-recursion-only *)
Example _true_recursion_only
  : forall (X : Type) (x : X), Equal x (true_recursion x only)
  := fun (X : Type) (x : X) => reflexive x.
(* endfrag *)

(* begfrag:to-true-only *)
Example _to_true_only
  : forall (X : Type) (x : X), Equal only (to_true x)
  := fun (X : Type) (x : X) => reflexive only.
(* endfrag *)

(* ================================================================ *)
(** ** The Boolean type                                             *)
(* ================================================================ *)

(* begfrag:boolean-induction-yes *)
Example _boolean_induction_yes
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Equal y (boolean_induction F y n yes)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => reflexive y.
(* endfrag *)

(* begfrag:boolean-induction-no *)
Example _boolean_induction_no
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Equal n (boolean_induction F y n no)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => reflexive n.
(* endfrag *)

(* begfrag:booolean-recursion-yes *)
Example _boolean_recursion_yes
  : forall (X : Type) (y n : X), Equal y (boolean_recursion y n yes)
  := fun (X : Type) (y n : X) => reflexive y.
(* endfrag *)

(* begfrag:boolean-recursion-no *)
Example _boolean_recursion_no
  : forall (X : Type) (y n : X), Equal n (boolean_recursion y n no)
  := fun (X : Type) (y n : X) => reflexive n.
(* endfrag *)

(* ================================================================ *)
(** ** The type of natural numbers                                  *)
(* ================================================================ *)

(* begfrag:natural-induction-zero *)
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

(* begfrag:natural-induction-successor *)
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

(* begfrag:natural-recursion-zero *)
Example _natural_recursion_zero
  : forall (X : Type) (z : X) (s : Natural -> X -> X),
      Equal z (natural_recursion z s zero)
  := fun (X : Type) (z : X) (s : Natural -> X -> X)
       => reflexive z.
(* endfrag *)

(* begfrag:natural-recursion-successor *)
Example _natural_recursion_successor
  : forall (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural),
      Equal (s n (natural_recursion z s n))
            (natural_recursion z s (successor n))
  := fun (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural)
     => reflexive (s n (natural_recursion z s n)).
(* endfrag *)

(* begfrag:natural-recursion-simple-zero *)
Example _natural_recursion_simple_zero
  : forall (X : Type) (z : X) (s : X -> X),
      Equal z (natural_recursion_simple z s zero)
  := fun (X : Type) (z : X) (s : X -> X)
       => reflexive z.
(* endfrag *)

(* begfrag:natural-recursion-simple-successor *)
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

(* begfrag:equal-induction-reflexive *)
Example _equal_induction_reflexive
  : forall (X : Type)
           (x : X)
           (F : forall (x' : X), Equal x x' -> Type)
           (e : F x (reflexive x)),
      Equal e (equal_induction x F e x (reflexive x))
  := fun (X : Type)
         (x : X)
         (F : forall (x' : X), Equal x x' -> Type)
         (e : F x (reflexive x))
       => reflexive e.
(* endfrag *)

(* begfrag:transport-reflexive *)
Example _transport_reflexive
  : forall (X : Type) (F : X -> Type) (x x' : X),
      Equal (@identity_function (F x)) (transport F (reflexive x))
  := fun (X : Type) (F : X -> Type) (x x' : X)
       => reflexive (@identity_function (F x)).
(* endfrag *)

(* ================================================================ *)
(** ** Sigma types                                                  *)
(* ================================================================ *)

(* begfrag:sigma-type-eta-conversion *)
Example _sigma_type_eta_conversion
  : forall (X : Type) (F : X -> Type) (t : Sigma (x : X), F x),
      Equal t (sigma F (sigma1 t) (sigma2 t))
  := fun (X : Type) (F : X -> Type) (t : Sigma (x : X), F x)
       => reflexive t.
(* endfrag *)

(* begfrag:sigma-curry-uncurry *)
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

(* begfrag:sigma-uncurry-curry *)
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

(* begfrag:product-eta-conversion *)
Example _product_eta_conversion
  : forall (X Y : Type) (t : Product X Y),
      Equal t (pair (first t) (second t))
  := fun (X Y : Type) (t : Product X Y)
       => reflexive t.
(* endfrag *)

(* begfrag:curry-uncurry *)
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

(* begfrag:uncurry-curry *)
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

(* begfrag:pair-function-first *)
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

(* begfrag:pair-function-second *)
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

(* begfrag:product-map-first *)
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

(* begfrag:product-map-second *)
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

(* begfrag:sum-induction-left *)
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

(* begfrag:sum-induction-right *)
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

(* begfrag:sum-recursion-left *)
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

(* begfrag:sum-recursion-right *)
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

(* begfrag:sum-map-left *)
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

(* begfrag:sum-map-right *)
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

(* End of file *)
