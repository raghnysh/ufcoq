(* Basic constructions with primitive types *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:zf4f204h *)
Require Import ufcoq.base.primitive.
(* endfrag *)

(* ================================================================ *)
(** ** The type of a thing                                          *)
(* ================================================================ *)

(* begfrag:b5b085qn *)
Definition Kind : forall (X : Type), X -> Type
  := fun (X : Type) (x : X) => X.

Arguments Kind {X} _.
(* endfrag *)

(* ================================================================ *)
(** ** Some basic notions about functions                           *)
(* ================================================================ *)

(* begfrag:yrbfo0qa *)
Definition FunctionDomain
  : forall (X : Type) (F : X -> Type), (forall (x : X), F x) -> Type
  := fun (X : Type) (F : X -> Type) (f : forall (x : X), F x) => X.

Arguments FunctionDomain {X} {F} _.
(* endfrag *)

(* begfrag:qolnxg6a *)
Definition FunctionCodomain
  : forall (X : Type) (F : X -> Type),
      (forall (x : X), F x) -> X -> Type
  := fun (X : Type) (F : X -> Type)
       (f : forall (x : X), F x) (a : X) => F a.

Arguments FunctionCodomain {X} {F} _ _.
(* endfrag *)

(* begfrag:jezpb6sa *)
Definition function_value
  : forall (X : Type) (F : X -> Type) (a : X),
      (forall (x : X), F x) -> F a
  := fun (X : Type) (F : X -> Type) (a : X)
       (f : forall (x : X), F x) => f a.

Arguments function_value {X} {F} a _.
(* endfrag *)

(* begfrag:u4wjel9o *)
Definition function_compose
  : forall (X Y : Type)
           (G : Y -> Type)
           (g : forall (y : Y), G y)
           (f : X -> Y),
      forall (x : X), G (f x)
  := fun (X Y : Type)
         (G : Y -> Type)
         (g : forall (y : Y), G y)
         (f : X -> Y)
         (x : X)
       => g (f x).

Arguments function_compose {X Y G} g f _.
(* endfrag *)

(* begfrag:ct7rwcsm *)
Definition identity_function : forall (X : Type), X -> X
  := fun (X : Type) (x : X) => x.

Arguments identity_function {X} _.
(* endfrag *)

(* begfrag:q4yy6ynm *)
Definition constant_function : forall (X Y : Type), Y -> X -> Y
  := fun (X Y : Type) (y : Y) (_ : X) => y.

Arguments constant_function {X Y} _ _.
(* endfrag *)

(* begfrag:867thqwu *)
Definition functions_equal_values_equal
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x),
      Equal f g -> forall (x : X), Equal (f x) (g x)
  := fun (X : Type)
         (F : X -> Type)
         (f : forall (x : X), F x)
       =>
         let
           T : Type := forall (x : X), F x
         in let
           P : forall (t : T), Equal f t -> Type
             := fun (t : T)
                  => constant_function
                       (forall (x : X), Equal (f x) (t x))
         in let
           base : P f (reflexive f) := fun (x : X) => reflexive (f x)
         in
           equal_induction f P base.

Arguments functions_equal_values_equal {X F f g} _ x.
(* endfrag *)

(* ================================================================ *)
(** ** Some basic notions about the primitive types                 *)
(* ================================================================ *)

(* begfrag:gcfsyi93 *)
Definition false_recursion : forall (X : Type), False -> X
  := fun (X : Type)
       => false_induction (@constant_function False Type X).
(* endfrag *)

(* begfrag:kad6krsx *)
Definition true_recursion : forall (X : Type), X -> True -> X
  := fun (X : Type)
       => true_induction (@constant_function True Type X).

Arguments true_recursion {X} _ _.
(* endfrag *)

(* begfrag:cppabof7 *)
Definition to_true : forall (X : Type), X -> True
  := fun (X : Type) => constant_function only.

Arguments to_true {X} _.
(* endfrag *)

(* begfrag:tav7tpv0 *)
Definition boolean_recursion
  : forall (X : Type), X -> X -> Boolean -> X
  := fun (X : Type)
       => boolean_induction (@constant_function Boolean Type X).

Arguments boolean_recursion {X} _ _ _.
(* endfrag *)

(* begfrag:8m7c7dml *)
Definition natural_recursion
  : forall (X : Type), X -> (Natural -> X -> X) -> Natural -> X
  := fun (X : Type) =>
      natural_induction (@constant_function Natural Type X).

Arguments natural_recursion {X} _ _ _.
(* endfrag *)

(* begfrag:yhafxlw0 *)
Definition natural_recursion_simple
  : forall (X : Type), X -> (X -> X) -> Natural -> X
  := fun (X : Type) (x : X) (f : X -> X)
       => natural_recursion x (@constant_function Natural (X -> X) f).

Arguments natural_recursion_simple {X} _ _ _.
(* endfrag *)

(* begfrag:szbmydj4 *)
Definition transport
  : forall (X : Type) (F : X -> Type) (x y : X),
      Equal x y -> F x -> F y
  := fun (X : Type)
         (F : X -> Type)
         (x : X)
       =>
         let
           G : forall (a : X), Equal x a -> Type
             := fun (a : X) => constant_function (F x -> F a)
         in let
           base : G x (reflexive x)
             := @identity_function (F x)
         in
           equal_induction x G base.

Arguments transport {X} F {x y} _ _.
(* endfrag *)

(* begfrag:xsfz3fch *)
Definition transport_inverse
  : forall (X : Type) (F : X -> Type) (x y : X),
      Equal x y -> F y -> F x
  := fun (X : Type)
         (F : X -> Type)
         (x : X)
       =>
         let
           G : forall (a : X), Equal x a -> Type
             := fun (a : X) => constant_function (F a -> F x)
         in let
           base : G x (reflexive x)
             := @identity_function (F x)
         in
           equal_induction x G base.

Arguments transport_inverse {X} F {x y} _ _.
(* endfrag *)

(* begfrag:wlyu1bpv *)
Definition sigma_induction
  : forall (X : Type)
           (F : X -> Type)
           (G : (Sigma (x : X), F x) -> Type),
      (forall (x : X) (y : F x), G (sigma F x y))
        -> (forall (t : Sigma (x : X), F x), G t)
  := fun (X : Type)
         (F : X -> Type)
         (G : (Sigma (x : X), F x) -> Type)
         (f : forall (x : X) (y : F x), G (sigma F x y))
         (t : Sigma (x : X), F x)
    => f (sigma1 t) (sigma2 t).

Arguments sigma_induction {X F G} _ _.
(* endfrag *)

(* begfrag:dq9dzz6c *)
Definition sigma_uncurry
  : forall (X : Type)
           (F : X -> Type)
           (G : (Sigma (x : X), F x) -> Type),
      (forall (x : X) (y : F x), G (sigma F x y))
        -> forall (t : Sigma (x : X), F x), G t
  := @sigma_induction.

Arguments sigma_uncurry {X F G} _ _.
(* endfrag *)

(* begfrag:gewpttx0 *)
Definition sigma_curry
  : forall (X : Type)
           (F : X -> Type)
           (G : (Sigma (x : X), F x) -> Type),
      (forall (t : Sigma (x : X), F x), G t)
        -> forall (x : X) (y : F x), G (sigma F x y)
  := fun  (X : Type)
          (F : X -> Type)
          (G : (Sigma (x : X), F x) -> Type)
          (g : forall (t : Sigma (x : X), F x), G t)
          (x : X)
          (y : F x)
       => g (sigma F x y).

Arguments sigma_curry {X F G} _ _ _.
(* endfrag *)

(* begfrag:siygmnhf *)
Definition sigma_recursion
  : forall (X : Type)
           (F : X -> Type)
           (Y : Type),
      (forall (x : X), F x -> Y) -> (Sigma (x : X), F x) -> Y
  := fun (X : Type)
         (F : X -> Type)
         (Y : Type)
         (f : forall (x : X), F x -> Y)
         (t : Sigma (x : X), F x)
       => f (sigma1 t) (sigma2 t).

Arguments sigma_recursion {X F} Y _ _.
(* endfrag *)

(* ================================================================ *)
(** ** The product of two types                                     *)
(* ================================================================ *)

(* begfrag:9ia68b8n *)
Definition Product : Type -> Type -> Type
  := fun (X Y : Type) => Sigma (_ : X), Y.
(* endfrag *)

(* begfrag:c97wzdtw *)
Definition pair : forall (X Y : Type), X -> Y -> Product X Y
  := fun (X Y : Type) (x : X) (y : Y)
       => sigma (@constant_function X Type Y) x y.

Arguments pair {X Y} _ _.
(* endfrag *)

(* begfrag:9eptwq6k *)
Definition first : forall (X Y : Type), Product X Y -> X
  := fun (X Y : Type) (t : Product X Y) => sigma1 t.

Arguments first {X Y} _.
(* endfrag *)

(* begfrag:og9uqzhe *)
Definition second : forall (X Y : Type), Product X Y -> Y
  := fun (X Y : Type) (t : Product X Y) => sigma2 t.

Arguments second {X Y} _.
(* endfrag *)

(* begfrag:ww805vp5 *)
Definition product_induction
  : forall (X Y : Type) (F : Product X Y -> Type),
      (forall (x : X) (y : Y), F (pair x y))
        -> forall (t : Product X Y), F t
  := fun (X Y : Type)
         (F : Product X Y -> Type)
         (f : forall (x : X) (y : Y), F (pair x y))
         (t : Product X Y)
       => f (first t) (second t).

Arguments product_induction {X Y F} _ _.
(* endfrag *)

(* begfrag:e1hi7545 *)
Definition uncurry
  : forall (X Y : Type) (F : Product X Y -> Type),
      (forall (x : X) (y : Y), F (pair x y))
        -> forall (t : Product X Y), F t
  := @product_induction.

Arguments uncurry {X Y F} _ _.
(* endfrag *)

(* begfrag:g6p35mq1 *)
Definition curry
  : forall (X Y : Type) (F : Product X Y -> Type),
      (forall (t : Product X Y), F t)
        -> forall (x : X) (y : Y), F (pair x y)
  := fun (X Y : Type)
         (F : Product X Y -> Type)
         (g : forall (t : Product X Y), F t)
         (x : X)
         (y : Y)
       => g (pair x y).

Arguments curry {X Y F} _ _ _.
(* endfrag *)

(* begfrag:9cz79pdm *)
Definition product_recursion
  : forall (X Y Z : Type), (X -> Y -> Z) -> Product X Y -> Z
  := fun (X Y Z : Type)
         (f : X -> Y -> Z)
         (t : Product X Y)
       => f (first t) (second t).

Arguments product_recursion {X Y Z} _ _.
(* endfrag *)

(* begfrag:d0923l5s *)
Definition PairFamily
  : forall (T : Type), (T -> Type) -> (T -> Type) -> T -> Type
  := fun (T : Type) (F : T -> Type) (G : T -> Type) (t : T)
       => Product (F t) (G t).

Arguments PairFamily {T} _ _ _.
(* endfrag *)

(* begfrag:rgjbl4r2 *)
Definition pair_function
  : forall (T : Type)
           (F : T -> Type)
           (G : T -> Type),
      (forall (t : T), F t)
        -> (forall (t : T), G t)
          -> forall (t : T), Product (F t) (G t)
  := fun (T : Type)
         (F : T -> Type)
         (G : T -> Type)
         (f : forall (t : T), F t)
         (g : forall (t : T), G t)
         (t : T)
       => pair (f t) (g t).

Arguments  pair_function {T F G} _ _ _.
(* endfrag *)

(* begfrag:wqs9857v *)
Definition product_map
  : forall (X Y X' Y' : Type),
      (X -> X') -> (Y -> Y') -> Product X Y -> Product X' Y'
  := fun (X Y X' Y' : Type)
         (f : X -> X')
         (g : Y -> Y')
         (t : Product X Y)
       => pair (f (first t)) (g (second t)).

Arguments product_map {X Y X' Y'} _ _ _.
(* endfrag *)

(* ================================================================ *)
(** ** The sum of two types                                         *)
(* ================================================================ *)

(* begfrag:fp5x8226 *)
Definition Sum : Type -> Type -> Type
  := fun (X Y : Type)
       => let F : Boolean -> Type := boolean_recursion X Y
          in Sigma (b : Boolean), F b.
(* endfrag *)

(* begfrag:kknkg0c7 *)
Definition left : forall (X Y : Type), X -> Sum X Y
  := fun (X Y : Type) (x : X) => sigma (boolean_recursion X Y) yes x.

Arguments left {X Y} _.
(* endfrag *)

(* begfrag:ma104yei *)
Definition right : forall (X Y : Type), Y -> Sum X Y
  := fun (X Y : Type) (y : Y) => sigma (boolean_recursion X Y) no y.

Arguments right {X Y} _.
(* endfrag *)

(* begfrag:hrr9zb80 *)
Definition sum_induction
  : forall (X Y : Type) (F : Sum X Y -> Type),
      (forall (x : X), F (left x)) -> (forall (y : Y), F (right y))
        -> forall (s : Sum X Y), F s
  := fun (X Y : Type)
         (F : Sum X Y -> Type)
         (f : forall (x : X), F (left x))
         (g : forall (y : Y), F (right y))
         (s : Sum X Y)
       =>
         let
           P : Boolean -> Type := boolean_recursion X Y
         in let
           Q : Boolean -> Type
             := fun (b : Boolean)
                  => forall (e : P b), F (sigma P b e)
         in let
           q : forall (b : Boolean), Q b := boolean_induction Q f g
         in
           q (sigma1 s) (sigma2 s).

Arguments sum_induction {X Y} F _ _ s.
(* endfrag *)

(* begfrag:czz2aznf *)
Definition sum_recursion
  : forall (X Y Z : Type), (X -> Z) -> (Y -> Z) -> Sum X Y -> Z
  := fun (X Y Z : Type)
         (f : X -> Z)
         (g : Y -> Z)
         (s : Sum X Y)
       =>
         let
           P : Boolean -> Type := boolean_recursion X Y
         in let
           Q : Boolean -> Type := fun (b : Boolean) => P b -> Z
         in let
           q : forall (b : Boolean), Q b := boolean_induction Q f g
         in
           q (sigma1 s) (sigma2 s).

Arguments sum_recursion {X Y Z} _ _ s.
(* endfrag *)

(* begfrag:mrbbbxn0 *)
Definition sum_map
  : forall (X Y X' Y' : Type),
      (X -> X') -> (Y -> Y') -> Sum X Y -> Sum X' Y'
  := fun (X Y X' Y' : Type) (f : X -> X') (g : Y -> Y')
       =>
         let
           u : X -> Sum X' Y' := fun x => left (f x)
         in let
           v : Y -> Sum X' Y' := fun y => right (g y)
         in
           sum_recursion u v.

Arguments sum_map {X Y X' Y'} _ _ _.
(* endfrag *)

(* End of file *)
