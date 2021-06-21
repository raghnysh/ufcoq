(* Some examples of sameness *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.

(* ================================================================ *)
(** ** Some examples of sameness                                    *)
(* ================================================================ *)

(* begfrag:function-eta-conversion *)
Example _function_eta_conversion
  : forall (X : Type) (F : X -> Type) (f : forall (x : X), F x),
      Equal f (fun (x : X) => f x)
  := fun (X : Type) (F : X -> Type) (f : forall (x : X), F x)
      => reflexive f.
(* endfrag:function-eta-conversion *)

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
(* endfrag:function-compose-associative *)

(* begfrag:function-compose-left-unit *)
Example _function_compose_left_unit
  : forall (X Y : Type) (f : X -> Y),
      Equal f (function_compose (@identity_function Y) f)
  := fun (X Y : Type) (f : X -> Y)
       => reflexive f.
(* endfrag:function-compose-left-unit *)

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
(* endfrag:function-compose-right-unit *)

(* begfrag:_true_things_only *)
Example _true_induction_only
  : forall (F : True -> Type) (x : F only),
      Equal x (true_induction F x only)
  := fun (F : True -> Type) (x : F only)
       => reflexive x.

Example _true_recursion_only
  : forall (X : Type) (x : X), Equal x (true_recursion x only)
  := fun (X : Type) (x : X) => reflexive x.

Example _to_true_only
  : forall (X : Type) (x : X), Equal only (to_true x)
  := fun (X : Type) (x : X) => reflexive only.
(* endfrag:_true_things_only *)

(* begfrag:boolean-things-yes-no *)
Example _boolean_induction_yes
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Equal y (boolean_induction F y n yes)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => reflexive y.

Example _boolean_induction_no
  : forall (F : Boolean -> Type) (y : F yes) (n : F no),
      Equal n (boolean_induction F y n no)
  := fun (F : Boolean -> Type) (y : F yes) (n : F no) => reflexive n.

Example _boolean_recursion_yes
  : forall (X : Type) (y n : X), Equal y (boolean_recursion y n yes)
  := fun (X : Type) (y n : X) => reflexive y.

Example _boolean_recursion_no
  : forall (X : Type) (y n : X), Equal n (boolean_recursion y n no)
  := fun (X : Type) (y n : X) => reflexive n.
(* endfrag:boolean-things-yes-no *)

(* begfrag:natural-things-zero-successor *)
Example _natural_induction_zero
  : forall (F : Natural -> Type)
           (z : F zero)
           (s : forall (n : Natural), F n -> F (successor n)),
      Equal z (natural_induction F z s zero)
  := fun (F : Natural -> Type)
         (z : F zero)
         (s : forall (n : Natural), F n -> F (successor n))
       => reflexive z.

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

Example _natural_recursion_zero
  : forall (X : Type) (z : X) (s : Natural -> X -> X),
      Equal z (natural_recursion z s zero)
  := fun (X : Type) (z : X) (s : Natural -> X -> X)
       => reflexive z.

Example _natural_recursion_successor
  : forall (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural),
      Equal (s n (natural_recursion z s n))
            (natural_recursion z s (successor n))
  := fun (X : Type) (z : X) (s : Natural -> X -> X) (n : Natural)
     => reflexive (s n (natural_recursion z s n)).

Example _natural_recursion_simple_zero
  : forall (X : Type) (z : X) (s : X -> X),
      Equal z (natural_recursion_simple z s zero)
  := fun (X : Type) (z : X) (s : X -> X)
       => reflexive z.

Example _natural_recursion_simple_successor
  : forall (X : Type) (z : X) (s : X -> X) (n : Natural),
      Equal (s (natural_recursion_simple z s n))
            (natural_recursion_simple z s (successor n))
  := fun (X : Type) (z : X) (s : X -> X) (n : Natural)
       => reflexive (s (natural_recursion_simple z s n)).
(* endfrag:natural-things-zero-successor *)

(* begfrag:equal-things-reflexive *)
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

Example _transport_reflexive
  : forall (X : Type) (F : X -> Type) (x x' : X),
      Equal (@identity_function (F x)) (transport F (reflexive x))
  := fun (X : Type) (F : X -> Type) (x x' : X)
       => reflexive (@identity_function (F x)).
(* endfrag:equal-things-reflexive *)

(* begfrag:sigma-type-eta-conversion *)
Example _sigma_type_eta_conversion
  : forall (X : Type) (F : X -> Type) (t : Sigma (x : X), F x),
      Equal t (sigma F (sigma1 t) (sigma2 t))
  := fun (X : Type) (F : X -> Type) (t : Sigma (x : X), F x)
       => reflexive t.
(* endfrag:sigma-type-eta-conversion *)

(* begfrag:product-eta-conversion *)
Example _product_eta_conversion
  : forall (X Y : Type) (t : Product X Y),
      Equal t (pair (first t) (second t))
  := fun (X Y : Type) (t : Product X Y)
       => reflexive t.
(* endfrag:product-eta-conversion *)

(* End of file *)
