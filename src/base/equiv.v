(* Equivalences of types *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:gc0bwfjt *)
Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.
Require Import ufcoq.base.ident.
Require Import ufcoq.base.elident.
Require Import ufcoq.base.transport.
(* endfrag *)

(* ================================================================ *)
(** ** The type of left inverses of a function                      *)
(* ================================================================ *)

(* begfrag:yb0mmsml *)
Definition LeftInverse
  : forall (X Y : Type), (X -> Y) -> Type
  := fun (X Y : Type) (f : X -> Y)
       => Sigma (fun (g : Y -> X) => ElIdent (function_unit X)
                                             (function_compose g f)).

Arguments LeftInverse {X Y} f.
(* endfrag *)

(* begfrag:v1y1sd7z *)
Definition left_inverse_function
  : forall (X Y : Type) (f : X -> Y), LeftInverse f -> Y -> X
  := fun (X Y : Type) (f : X -> Y) (u : LeftInverse f)
       => sigma1 u.

Arguments left_inverse_function {X Y} f _ _.
(* endfrag *)

(* begfrag:aw2c2xjb *)
Definition left_inverse_elident
  : forall (X Y : Type)
           (f : X -> Y)
           (u : LeftInverse f),
      ElIdent (function_unit X)
              (function_compose (left_inverse_function f u) f)
  := fun (X Y : Type) (f : X -> Y) (u : LeftInverse f)
       => sigma2 u.

Arguments left_inverse_elident {X Y} f u _.
(* endfrag *)

(* begfrag:bqnahtxh *)
Definition left_inverse
  : forall (X Y : Type) (f : X -> Y) (g : Y -> X),
      ElIdent (function_unit X) (function_compose g f)
        -> LeftInverse f
  := fun (X Y : Type) (f : X -> Y)
       => sigma (fun (g : Y -> X) => ElIdent (function_unit X)
                                             (function_compose g f)).

Arguments left_inverse {X Y} f g _.
(* endfrag *)

(* ================================================================ *)
(** ** The type of right inverses of a function                     *)
(* ================================================================ *)

(* begfrag:gwkups7z *)
Definition RightInverse
  : forall (X Y : Type), (X -> Y) -> Type
  := fun (X Y : Type) (f : X -> Y)
       => Sigma (fun (g : Y -> X) => ElIdent (function_unit Y)
                                             (function_compose f g)).

Arguments RightInverse {X Y} f.
(* endfrag *)

(* begfrag:n4ujbi0g *)
Definition right_inverse_function
  : forall (X Y : Type) (f : X -> Y), RightInverse f -> Y -> X
  := fun (X Y : Type) (f : X -> Y) (u : RightInverse f)
       => sigma1 u.

Arguments right_inverse_function {X Y} f _ _.
(* endfrag *)

(* begfrag:gvpbf13o *)
Definition right_inverse_elident
  : forall (X Y : Type)
           (f : X -> Y)
           (u : RightInverse f),
      ElIdent (function_unit Y)
              (function_compose f (right_inverse_function f u))
  := fun (X Y : Type) (f : X -> Y) (u : RightInverse f)
       => sigma2 u.

Arguments right_inverse_elident {X Y} f u _.
(* endfrag *)

(* begfrag:neyszrm7 *)
Definition right_inverse
  : forall (X Y : Type) (f : X -> Y) (g : Y -> X),
      ElIdent (function_unit Y) (function_compose f g)
        -> RightInverse f
  := fun (X Y : Type) (f : X -> Y)
       => sigma (fun (g : Y -> X) => ElIdent (function_unit Y)
                                             (function_compose f g)).

Arguments right_inverse {X Y} f g _.
(* endfrag *)

(* ================================================================ *)
(** ** The type of witnesses to a function being an equivalence     *)
(* ================================================================ *)

(* begfrag:9xrrof4a *)
Definition IsEquiv
  : forall (X Y : Type), (X -> Y) -> Type
  := fun (X Y : Type) (f : X -> Y)
       => Product (LeftInverse f) (RightInverse f).

Arguments IsEquiv {X Y} _.
(* endfrag *)

(* begfrag:e1c37gow *)
Definition is_equiv_left_inverse_function
  : forall (X Y : Type) (f : X -> Y), IsEquiv f -> Y -> X
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       => sigma1 (first u).

Arguments is_equiv_left_inverse_function {X Y} f _ _.
(* endfrag *)

(* begfrag:7h247058 *)
Definition is_equiv_left_inverse_elident
  : forall (X Y : Type) (f : X -> Y) (u : IsEquiv f),
      ElIdent (function_unit X)
              (function_compose (is_equiv_left_inverse_function f u)
                                f)
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       => sigma2 (first u).

Arguments is_equiv_left_inverse_elident {X Y} f u _.
(* endfrag *)

(* begfrag:j75fakvf *)
Definition is_equiv_right_inverse_function
  : forall (X Y : Type) (f : X -> Y), IsEquiv f -> Y -> X
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       => sigma1 (second u).

Arguments is_equiv_right_inverse_function {X Y} f _ _.
(* endfrag *)

(* begfrag:tdn8izfx *)
Definition is_equiv_right_inverse_elident
  : forall (X Y : Type) (f : X -> Y) (u : IsEquiv f),
      ElIdent (function_unit Y)
              (function_compose f
                                (is_equiv_right_inverse_function f u))
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       => sigma2 (second u).

Arguments is_equiv_right_inverse_elident {X Y} f u _.
(* endfrag *)

(* begfrag:9g0ac2o4 *)
Definition is_equiv
  : forall (X Y : Type) (f : X -> Y) (g h : Y -> X),
      ElIdent (function_unit X) (function_compose g f)
        -> ElIdent (function_unit Y) (function_compose f h)
          -> IsEquiv f
  := fun (X Y : Type)
         (f : X -> Y)
         (g h : Y -> X)
         (u : ElIdent (function_unit X) (function_compose g f))
         (v : ElIdent (function_unit Y) (function_compose f h))
       => pair (left_inverse f g u) (right_inverse f h v).

Arguments is_equiv {X Y} f g h _ _.
(* endfrag *)

(* ================================================================ *)
(** ** The type of quasi-inverses of a function                     *)
(* ================================================================ *)

(* begfrag:bw36fqif *)
Definition QuasiInverse
  : forall (X Y : Type), (X -> Y) -> Type
  := fun (X Y : Type) (f : X -> Y)
       => Sigma (fun (g : Y -> X)
                   => Product (ElIdent (function_unit X)
                                       (function_compose g f))
                              (ElIdent (function_unit Y)
                                       (function_compose f g))).

Arguments QuasiInverse {X Y} f.
(* endfrag *)

(* begfrag:4awq8jj4 *)
Definition quasi_inverse_function
  : forall (X Y : Type) (f : X -> Y), QuasiInverse f -> Y -> X
  := fun (X Y : Type) (f : X -> Y) (u : QuasiInverse f)
       => sigma1 u.

Arguments quasi_inverse_function {X Y} f _ _.
(* endfrag *)

(* begfrag:1k3wd0ih *)
Definition quasi_inverse_left_elident
  : forall (X Y : Type) (f : X -> Y) (u : QuasiInverse f),
      ElIdent (function_unit X)
              (function_compose (quasi_inverse_function f u) f)
  := fun (X Y : Type) (f : X -> Y) (u : QuasiInverse f)
       => first (sigma2 u).

Arguments quasi_inverse_left_elident {X Y} f u _.
(* endfrag *)

(* begfrag:wpbwzm0y *)
Definition quasi_inverse_right_elident
  : forall (X Y : Type) (f : X -> Y) (u : QuasiInverse f),
      ElIdent (function_unit Y)
              (function_compose f (quasi_inverse_function f u))
  := fun (X Y : Type) (f : X -> Y) (u : QuasiInverse f)
       => second (sigma2 u).

Arguments quasi_inverse_right_elident {X Y} f u _.
(* endfrag *)

(* begfrag:2zk5jtcb *)
Definition quasi_inverse
  : forall (X Y : Type) (f : X -> Y) (g : Y -> X),
      ElIdent (function_unit X) (function_compose g f)
        -> ElIdent (function_unit Y) (function_compose f g)
          -> QuasiInverse f
  := fun (X Y : Type)
         (f : X -> Y)
         (g : Y -> X)
         (u : ElIdent (function_unit X) (function_compose g f))
         (v : ElIdent (function_unit Y) (function_compose f g))
       => sigma (fun (t : Y -> X)
                   => Product (ElIdent (function_unit X)
                                       (function_compose t f))
                              (ElIdent (function_unit Y)
                                       (function_compose f t)))
                g
                (pair u v).

Arguments quasi_inverse {X Y} f g _ _.
(* endfrag *)

(* ================================================================ *)
(** ** Examples of quasi-inverses                                   *)
(* ================================================================ *)

(* begfrag:mrwwha8b *)
Definition quasi_inverse_function_unit
  : forall (X : Type), QuasiInverse (function_unit X)
  := fun (X : Type)
       =>
         let
           f : X -> X
             := function_unit X
         in let
           u : ElIdent f f
             := elident_unit f
         in
           quasi_inverse f f u u.
(* endfrag *)

(* begfrag:eiulalwg *)
Definition quasi_inverse_ident_compose_left
  : forall (X : Type) (x y : X) (p : Ident x y) (z : X),
      QuasiInverse (fun (q : Ident y z) => ident_compose p q)
  := fun (X : Type) (x y : X) (p : Ident x y) (z : X)
       => quasi_inverse
            (fun (q : Ident y z) => ident_compose p q)
            (fun (r : Ident x z) => ident_compose (ident_inverse p) r)
            (fun (q : Ident y z) => ident_expand2 p q)
            (fun (r : Ident x z) => ident_expand4 p r).

Arguments quasi_inverse_ident_compose_left {X x y} p z.
(* endfrag *)

(* begfrag:rwy9kak1 *)
Definition quasi_inverse_ident_compose_right
  : forall (X : Type) (x y : X) (p : Ident x y) (w : X),
      QuasiInverse (fun (n : Ident w x) => ident_compose n p)
  := fun (X : Type) (x y : X) (p : Ident x y) (w : X)
       => quasi_inverse
            (fun (n : Ident w x) => ident_compose n p)
            (fun (r : Ident w y) => ident_compose r (ident_inverse p))
            (fun (n : Ident w x) => ident_expand8 n p)
            (fun (r : Ident w y) => ident_expand6 r p).

Arguments quasi_inverse_ident_compose_right {X x y} p w.
(* endfrag *)

(* begfrag:7mnhpoep *)
Definition quasi_inverse_transport
  : forall (X : Type) (F : X -> Type) (x y : X) (p : Ident x y),
      QuasiInverse (transport F p)
  := fun (X : Type) (F : X -> Type) (x y : X) (p : Ident x y)
       => quasi_inverse
            (transport F p)
            (transport_inverse F p)
            (elident_of_ident (transport_left_inverse F p))
            (elident_of_ident (transport_right_inverse F p)).

Arguments quasi_inverse_transport {X} F {x y} p.
(* endfrag *)

(* ================================================================ *)
(** ** From quasi-inverses to equivalence witnesses and back        *)
(* ================================================================ *)

(* begfrag:btkdwz4r *)
Definition is_equiv_of_quasi_inverse
  : forall (X Y : Type) (f : X -> Y), QuasiInverse f -> IsEquiv f
  := fun (X Y : Type) (f : X -> Y) (u : QuasiInverse f)
       =>
         let
           g : Y -> X
             := quasi_inverse_function f u
         in
           is_equiv f
                    g
                    g
                    (quasi_inverse_left_elident f u)
                    (quasi_inverse_right_elident f u).

Arguments is_equiv_of_quasi_inverse {X Y} f _.
(* endfrag *)

(* begfrag:cyx98538 *)
Definition quasi_inverse_of_is_equiv
  : forall (X Y : Type) (f : X -> Y), IsEquiv f -> QuasiInverse f
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       =>
         let
           g : Y -> X
             := is_equiv_left_inverse_function f u
         in let
           l : ElIdent (function_unit X) (function_compose g f)
             := is_equiv_left_inverse_elident f u
         in let
           h : Y -> X
             := is_equiv_right_inverse_function f u
         in let
           r : ElIdent (function_unit Y) (function_compose f h)
             := is_equiv_right_inverse_elident f u
         in let
           a : ElIdent h (function_compose (function_compose g f) h)
             := elident_left_whisker h l
         in let
           b : ElIdent g (function_compose g (function_compose f h))
             := elident_right_whisker r g
         in let
           c : ElIdent h g
             := elident_compose a (elident_inverse b)
         in let
           d : ElIdent (function_compose f h) (function_compose f g)
             := elident_right_whisker c f
         in let
           e : ElIdent (function_unit Y) (function_compose f g)
             := elident_compose r d
         in
           quasi_inverse f g l e.

Arguments quasi_inverse_of_is_equiv {X Y} f _.
(* endfrag *)

(* End of file *)
