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

Arguments left_inverse_function {X Y f} _ _.
(* endfrag *)

(* begfrag:aw2c2xjb *)
Definition left_inverse_elident
  : forall (X Y : Type)
           (f : X -> Y)
           (u : LeftInverse f),
      ElIdent (function_unit X)
              (function_compose (left_inverse_function u) f)
  := fun (X Y : Type) (f : X -> Y) (u : LeftInverse f)
       => sigma2 u.

Arguments left_inverse_elident {X Y f} u _.
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

Arguments right_inverse_function {X Y f} _ _.
(* endfrag *)

(* begfrag:gvpbf13o *)
Definition right_inverse_elident
  : forall (X Y : Type)
           (f : X -> Y)
           (u : RightInverse f),
      ElIdent (function_unit Y)
              (function_compose f (right_inverse_function u))
  := fun (X Y : Type) (f : X -> Y) (u : RightInverse f)
       => sigma2 u.

Arguments right_inverse_elident {X Y f} u _.
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
(** ** Examples of left inverses and right inverses                 *)
(* ================================================================ *)

(* begfrag:pjpefw13 *)
Definition left_inverse_function_unit
  : forall (X : Type), LeftInverse (function_unit X)
  := fun (X : Type)
     =>
       let
         f : X -> X
           := function_unit X
       in
         left_inverse f f (elident_unit f).
(* endfrag *)

(* begfrag:nwz6tn8f *)
Definition right_inverse_function_unit
  : forall (X : Type), RightInverse (function_unit X)
  := fun (X : Type)
     =>
       let
         f : X -> X
           := function_unit X
       in
         right_inverse f f (elident_unit f).
(* endfrag *)

(* begfrag:ndp3m9eg *)
Definition left_inverse_of_right_inverse
  : forall (X Y : Type) (f : X -> Y) (u : RightInverse f),
      LeftInverse (right_inverse_function u)
  := fun (X Y : Type) (f : X -> Y) (u : RightInverse f)
       =>
         let g : Y -> X
               := right_inverse_function u
         in
           left_inverse g f (right_inverse_elident u).

Arguments left_inverse_of_right_inverse {X Y f} u.
(* endfrag *)

(* begfrag:6zdulbzx *)
Definition right_inverse_of_left_inverse
  : forall (X Y : Type) (f : X -> Y) (u : LeftInverse f),
      RightInverse (left_inverse_function u)
  := fun (X Y : Type) (f : X -> Y) (u : LeftInverse f)
       =>
         let g : Y -> X
               := left_inverse_function u
         in
           right_inverse g f (left_inverse_elident u).

Arguments right_inverse_of_left_inverse {X Y f} u.
(* endfrag *)

(* begfrag:nd5whc36 *)
Definition left_inverse_compose
  : forall (X Y : Type) (f : X -> Y),
      LeftInverse f
        -> forall (Z : Type) (g : Y -> Z),
             LeftInverse g -> LeftInverse (function_compose g f)
  := fun (X Y : Type)
         (f : X -> Y)
         (u : LeftInverse f)
         (Z : Type)
         (g : Y -> Z)
         (v : LeftInverse g)
       =>
         let
           h : X -> Z
             := function_compose g f
         in let
           f' : Y -> X
              := left_inverse_function u
         in let
           a : ElIdent (function_unit X) (function_compose f' f)
             := left_inverse_elident u
         in let
           g' : Z -> Y
              := left_inverse_function v
         in let
           b : ElIdent (function_unit Y) (function_compose g' g)
             := left_inverse_elident v
         in let
           h' : Z -> X
              := function_compose f' g'
         in let
           c : ElIdent f' (function_compose h' g)
             := elident_right_whisker b f'
         in let
           d : ElIdent (function_compose f' f) (function_compose h' h)
             := elident_left_whisker f c
         in let
           e : ElIdent (function_unit X) (function_compose h' h)
             := elident_compose a d
         in
           left_inverse h h' e.

Arguments left_inverse_compose {X Y f} _ {Z g} _.
(* endfrag *)

(* begfrag:fkqj3pan *)
Definition right_inverse_compose
  : forall (X Y : Type) (f : X -> Y),
      RightInverse f
        -> forall (Z : Type) (g : Y -> Z),
             RightInverse g -> RightInverse (function_compose g f)
  := fun (X Y : Type)
         (f : X -> Y)
         (u : RightInverse f)
         (Z : Type)
         (g : Y -> Z)
         (v : RightInverse g)
       =>
         let
           h : X -> Z
             := function_compose g f
         in let
           f' : Y -> X
              := right_inverse_function u
         in let
           a : ElIdent (function_unit Y) (function_compose f f')
             := right_inverse_elident u
         in let
           g' : Z -> Y
              := right_inverse_function v
         in let
           b : ElIdent (function_unit Z) (function_compose g g')
             := right_inverse_elident v
         in let
           h' : Z -> X
              := function_compose f' g'
         in let
           c : ElIdent g' (function_compose f h')
             := elident_left_whisker g' a
         in let
           d : ElIdent (function_compose g g') (function_compose h h')
             := elident_right_whisker c g
         in let
           e : ElIdent (function_unit Z) (function_compose h h')
             := elident_compose b d
         in
           right_inverse h h' e.

Arguments right_inverse_compose {X Y f} _ {Z g} _.
(* endfrag *)

(* begfrag:qldl59yt *)
Definition left_inverse_ident_compose_left
  : forall (X : Type) (x y : X) (p : Ident x y) (z : X),
      LeftInverse (fun (q : Ident y z) => ident_compose p q)
  := fun (X : Type) (x y : X) (p : Ident x y) (z : X)
       => left_inverse
            (fun (q : Ident y z) => ident_compose p q)
            (fun (r : Ident x z) => ident_compose (ident_inverse p) r)
            (fun (q : Ident y z) => ident_expand2 p q).

Arguments left_inverse_ident_compose_left {X x y} p z.
(* endfrag *)

(* begfrag:lx9jzjyu *)
Definition right_inverse_ident_compose_left
  : forall (X : Type) (x y : X) (p : Ident x y) (z : X),
      RightInverse (fun (q : Ident y z) => ident_compose p q)
  := fun (X : Type) (x y : X) (p : Ident x y) (z : X)
       => right_inverse
            (fun (q : Ident y z) => ident_compose p q)
            (fun (r : Ident x z) => ident_compose (ident_inverse p) r)
            (fun (r : Ident x z) => ident_expand4 p r).

Arguments right_inverse_ident_compose_left {X x y} p z.
(* endfrag *)

(* begfrag:txr5h67s *)
Definition left_inverse_ident_compose_right
  : forall (X : Type) (x y : X) (p : Ident x y) (z : X),
      LeftInverse (fun (q : Ident z x) => ident_compose q p)
  := fun (X : Type) (x y : X) (p : Ident x y) (z : X)
       => left_inverse
            (fun (q : Ident z x) => ident_compose q p)
            (fun (r : Ident z y) => ident_compose r (ident_inverse p))
            (fun (q : Ident z x) => ident_expand8 q p).

Arguments left_inverse_ident_compose_right {X x y} p z.
(* endfrag *)

(* begfrag:ro5ny9ms *)
Definition right_inverse_ident_compose_right
  : forall (X : Type) (x y : X) (p : Ident x y) (z : X),
      RightInverse (fun (q : Ident z x) => ident_compose q p)
  := fun (X : Type) (x y : X) (p : Ident x y) (z : X)
       => right_inverse
            (fun (q : Ident z x) => ident_compose q p)
            (fun (r : Ident z y) => ident_compose r (ident_inverse p))
            (fun (r : Ident z y) => ident_expand6 r p).

Arguments right_inverse_ident_compose_right {X x y} p z.
(* endfrag *)

(* begfrag:3kthivt0 *)
Definition left_inverse_transport
  : forall (X : Type) (F : X -> Type) (x y : X) (p : Ident x y),
      LeftInverse (transport F p)
  := fun (X : Type) (F : X -> Type) (x y : X) (p : Ident x y)
       => left_inverse
            (transport F p)
            (transport_inverse F p)
            (elident_of_ident (transport_left_inverse F p)).

Arguments left_inverse_transport {X} F {x y} p.
(* endfrag *)

(* begfrag:7qvd2qwt *)
Definition right_inverse_transport
  : forall (X : Type) (F : X -> Type) (x y : X) (p : Ident x y),
      RightInverse (transport F p)
  := fun (X : Type) (F : X -> Type) (x y : X) (p : Ident x y)
       => right_inverse
            (transport F p)
            (transport_inverse F p)
            (elident_of_ident (transport_right_inverse F p)).

Arguments right_inverse_transport {X} F {x y} p.
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

(* begfrag:hmcvvfnq *)
Definition is_equiv_left_inverse
  : forall (X Y : Type) (f : X -> Y), IsEquiv f -> LeftInverse f
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f) => first u.

Arguments is_equiv_left_inverse {X Y f} _.
(* endfrag *)

(* begfrag:e1c37gow *)
Definition is_equiv_left_inverse_function
  : forall (X Y : Type) (f : X -> Y), IsEquiv f -> Y -> X
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       => left_inverse_function (is_equiv_left_inverse u).

Arguments is_equiv_left_inverse_function {X Y f} _ _.
(* endfrag *)

(* begfrag:7h247058 *)
Definition is_equiv_left_inverse_elident
  : forall (X Y : Type) (f : X -> Y) (u : IsEquiv f),
      ElIdent (function_unit X)
              (function_compose (is_equiv_left_inverse_function u)
                                f)
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       => left_inverse_elident (is_equiv_left_inverse u).

Arguments is_equiv_left_inverse_elident {X Y f} u _.
(* endfrag *)

(* begfrag:k54u46k1 *)
Definition is_equiv_right_inverse
  : forall (X Y : Type) (f : X -> Y), IsEquiv f -> RightInverse f
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f) => second u.

Arguments is_equiv_right_inverse {X Y f} _.
(* endfrag *)

(* begfrag:j75fakvf *)
Definition is_equiv_right_inverse_function
  : forall (X Y : Type) (f : X -> Y), IsEquiv f -> Y -> X
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       => right_inverse_function (is_equiv_right_inverse u).

Arguments is_equiv_right_inverse_function {X Y f} _ _.
(* endfrag *)

(* begfrag:tdn8izfx *)
Definition is_equiv_right_inverse_elident
  : forall (X Y : Type) (f : X -> Y) (u : IsEquiv f),
      ElIdent (function_unit Y)
              (function_compose f
                                (is_equiv_right_inverse_function u))
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       => right_inverse_elident (is_equiv_right_inverse u).

Arguments is_equiv_right_inverse_elident {X Y f} u _.
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

(* begfrag:dff1cgc2 *)
Definition is_equiv_of_inverses
  : forall (X Y : Type) (f : X -> Y),
      LeftInverse f -> RightInverse f -> IsEquiv f
  := fun (X Y : Type)
         (f : X -> Y)
         (u : LeftInverse f)
         (v : RightInverse f)
       => pair u v.

Arguments is_equiv_of_inverses {X Y f} _ _.
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

Arguments quasi_inverse_function {X Y f} _ _.
(* endfrag *)

(* begfrag:1k3wd0ih *)
Definition quasi_inverse_left_elident
  : forall (X Y : Type) (f : X -> Y) (u : QuasiInverse f),
      ElIdent (function_unit X)
              (function_compose (quasi_inverse_function u) f)
  := fun (X Y : Type) (f : X -> Y) (u : QuasiInverse f)
       => first (sigma2 u).

Arguments quasi_inverse_left_elident {X Y f} u _.
(* endfrag *)

(* begfrag:wpbwzm0y *)
Definition quasi_inverse_right_elident
  : forall (X Y : Type) (f : X -> Y) (u : QuasiInverse f),
      ElIdent (function_unit Y)
              (function_compose f (quasi_inverse_function u))
  := fun (X Y : Type) (f : X -> Y) (u : QuasiInverse f)
       => second (sigma2 u).

Arguments quasi_inverse_right_elident {X Y f} u _.
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

(* begfrag:b3mvez2d *)
Definition quasi_inverse_inverse
  : forall (X Y : Type) (f : X -> Y) (u : QuasiInverse f),
      QuasiInverse (quasi_inverse_function u)
  := fun (X Y : Type) (f : X -> Y) (u : QuasiInverse f)
       => quasi_inverse
            (quasi_inverse_function u)
            f
            (quasi_inverse_right_elident u)
            (quasi_inverse_left_elident u).

Arguments quasi_inverse_inverse {X Y f} u.
(* endfrag *)

(* begfrag:ixbeovwn *)
Definition quasi_inverse_compose
  : forall (X Y : Type) (f : X -> Y),
      QuasiInverse f
        -> forall (Z : Type) (g : Y -> Z),
             QuasiInverse g -> QuasiInverse (function_compose g f)
  := fun (X Y : Type)
         (f : X -> Y)
         (u : QuasiInverse f)
         (Z : Type)
         (g : Y -> Z)
         (v : QuasiInverse g)
       => quasi_inverse
            (function_compose g f)
            (function_compose (quasi_inverse_function u)
                              (quasi_inverse_function v))
            (left_inverse_elident
               (left_inverse_compose
                  (left_inverse f
                                (quasi_inverse_function u)
                                (quasi_inverse_left_elident u))
                  (left_inverse g
                                (quasi_inverse_function v)
                                (quasi_inverse_left_elident v))))
            (right_inverse_elident
               (right_inverse_compose
                  (right_inverse f
                                 (quasi_inverse_function u)
                                 (quasi_inverse_right_elident u))
                  (right_inverse g
                                 (quasi_inverse_function v)
                                 (quasi_inverse_right_elident v)))).

Arguments quasi_inverse_compose {X Y f} _ {Z g} _.
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
  : forall (X : Type) (x y : X) (p : Ident x y) (z : X),
      QuasiInverse (fun (q : Ident z x) => ident_compose q p)
  := fun (X : Type) (x y : X) (p : Ident x y) (z : X)
       => quasi_inverse
            (fun (q : Ident z x) => ident_compose q p)
            (fun (r : Ident z y) => ident_compose r (ident_inverse p))
            (fun (q : Ident z x) => ident_expand8 q p)
            (fun (r : Ident z y) => ident_expand6 r p).

Arguments quasi_inverse_ident_compose_right {X x y} p z.
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
             := quasi_inverse_function u
         in
           is_equiv f
                    g
                    g
                    (quasi_inverse_left_elident u)
                    (quasi_inverse_right_elident u).

Arguments is_equiv_of_quasi_inverse {X Y f} _.
(* endfrag *)

(* begfrag:cyx98538 *)
Definition quasi_inverse_of_is_equiv
  : forall (X Y : Type) (f : X -> Y), IsEquiv f -> QuasiInverse f
  := fun (X Y : Type) (f : X -> Y) (u : IsEquiv f)
       =>
         let
           g : Y -> X
             := is_equiv_left_inverse_function u
         in let
           l : ElIdent (function_unit X) (function_compose g f)
             := is_equiv_left_inverse_elident u
         in let
           h : Y -> X
             := is_equiv_right_inverse_function u
         in let
           r : ElIdent (function_unit Y) (function_compose f h)
             := is_equiv_right_inverse_elident u
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

Arguments quasi_inverse_of_is_equiv {X Y f} _.
(* endfrag *)

(* ================================================================ *)
(** ** The type of equivalences between two types                   *)
(* ================================================================ *)

(* begfrag:z6fd4ma8 *)
Definition Equiv
  : Type -> Type -> Type
  := fun (X Y : Type) => Sigma (fun (f : X -> Y) => IsEquiv f).
(* endfrag *)

(* begfrag:qdried27 *)
Definition equiv_function
  : forall (X Y : Type), Equiv X Y -> X -> Y
  := fun (X Y : Type) (u : Equiv X Y) => sigma1 u.

Arguments equiv_function {X Y} _ _.
(* endfrag *)

(* begfrag:7k8df3oh *)
Definition equiv_is_equiv
  : forall (X Y : Type) (u : Equiv X Y), IsEquiv (equiv_function u)
  := fun (X Y : Type) (u : Equiv X Y) => sigma2 u.

Arguments equiv_is_equiv {X Y} u.
(* endfrag *)

(* begfrag:4elp9dy0 *)
Definition equiv_left_inverse
  : forall (X Y : Type) (u : Equiv X Y),
      LeftInverse (equiv_function u)
  := fun (X Y : Type) (u : Equiv X Y)
       => is_equiv_left_inverse (equiv_is_equiv u).

Arguments equiv_left_inverse {X Y} u.
(* endfrag *)

(* begfrag:ml3235nq *)
Definition equiv_left_inverse_function
  : forall (X Y : Type), Equiv X Y -> Y -> X
  := fun (X Y : Type) (u : Equiv X Y)
       => is_equiv_left_inverse_function (equiv_is_equiv u).

Arguments equiv_left_inverse_function {X Y} _ _.
(* endfrag *)

(* begfrag:93q3g6vq *)
Definition equiv_left_inverse_elident
  : forall (X Y : Type) (u : Equiv X Y),
      ElIdent (function_unit X)
              (function_compose (equiv_left_inverse_function u)
                                (equiv_function u))
  := fun (X Y : Type) (u : Equiv X Y)
       => is_equiv_left_inverse_elident (equiv_is_equiv u).

Arguments equiv_left_inverse_elident {X Y} u _.
(* endfrag *)

(* begfrag:24vq6b3w *)
Definition equiv_right_inverse
  : forall (X Y : Type) (u : Equiv X Y),
      RightInverse (equiv_function u)
  := fun (X Y : Type) (u : Equiv X Y)
       => is_equiv_right_inverse (equiv_is_equiv u).

Arguments equiv_right_inverse {X Y} u.
(* endfrag *)

(* begfrag:6djli00b *)
Definition equiv_right_inverse_function
  : forall (X Y : Type), Equiv X Y -> Y -> X
  := fun (X Y : Type) (u : Equiv X Y)
       => is_equiv_right_inverse_function (equiv_is_equiv u).

Arguments equiv_right_inverse_function {X Y} _ _.
(* endfrag *)

(* begfrag:3tu8y9iy *)
Definition equiv_right_inverse_elident
  : forall (X Y : Type) (u : Equiv X Y),
      ElIdent (function_unit Y)
              (function_compose (equiv_function u)
                                (equiv_right_inverse_function u))
  := fun (X Y : Type) (u : Equiv X Y)
       => is_equiv_right_inverse_elident (equiv_is_equiv u).

Arguments equiv_right_inverse_elident {X Y} u _.
(* endfrag *)

(* begfrag:bjkxqpwy *)
Definition equiv
  : forall (X Y : Type) (f : X -> Y) (g h : Y -> X),
      ElIdent (function_unit X) (function_compose g f)
        -> ElIdent (function_unit Y) (function_compose f h)
          -> Equiv X Y
  := fun (X Y : Type)
         (f : X -> Y)
         (g h : Y -> X)
         (u : ElIdent (function_unit X) (function_compose g f))
         (v : ElIdent (function_unit Y) (function_compose f h))
       => sigma (fun (t : X -> Y) => IsEquiv t)
                f
                (is_equiv f g h u v).

Arguments equiv {X Y} f g h _ _.
(* endfrag *)

(* begfrag:htfnzop9 *)
Definition equiv_of_inverses
  : forall (X Y : Type) (f : X -> Y),
      LeftInverse f -> RightInverse f -> Equiv X Y
  := fun (X Y : Type)
         (f : X -> Y)
         (u : LeftInverse f)
         (v : RightInverse f)
       => sigma (fun (t : X -> Y) => IsEquiv t)
                f
                (is_equiv_of_inverses u v).

Arguments equiv_of_inverses {X Y f} _ _.
(* endfrag *)

(* begfrag:88kq32yf *)
Definition equiv_of_quasi_inverse
  : forall (X Y : Type) (f : X -> Y), QuasiInverse f -> Equiv X Y
  := fun (X Y : Type) (f : X -> Y) (u : QuasiInverse f)
       => sigma (fun (t : X -> Y) => IsEquiv t)
                f
                (is_equiv_of_quasi_inverse u).

Arguments equiv_of_quasi_inverse {X Y f} _.
(* endfrag *)

(* begfrag:asxnqzuj *)
Definition quasi_inverse_of_equiv
  : forall (X Y : Type) (u : Equiv X Y),
      QuasiInverse (equiv_function u)
  := fun (X Y : Type) (u : Equiv X Y)
       => quasi_inverse_of_is_equiv (equiv_is_equiv u).

Arguments quasi_inverse_of_equiv {X Y} u.
(* endfrag *)

(* ================================================================ *)
(** ** Examples of equivalences                                     *)
(* ================================================================ *)

(* begfrag:olb15ber *)
Definition equiv_unit
  : forall (X : Type), Equiv X X
  := fun (X : Type)
       => equiv_of_quasi_inverse (quasi_inverse_function_unit X).
(* endfrag *)

(* begfrag:7pfy18vs *)
Definition equiv_inverse
  : forall (X Y : Type), Equiv X Y -> Equiv Y X
  := fun (X Y : Type) (u : Equiv X Y)
       => equiv_of_quasi_inverse
            (quasi_inverse_inverse (quasi_inverse_of_equiv u)).

Arguments equiv_inverse {X Y} _.
(* endfrag *)

(* begfrag:qjdzuyzi *)
Definition equiv_compose
  : forall (X Y : Type),
      Equiv X Y -> forall (Z : Type), Equiv Y Z -> Equiv X Z
  := fun (X Y : Type)
         (u : Equiv X Y)
         (Z : Type)
         (v : Equiv Y Z)
       => equiv_of_quasi_inverse
            (quasi_inverse_compose (quasi_inverse_of_equiv u)
                                   (quasi_inverse_of_equiv v)).

Arguments equiv_compose {X Y} _ {Z} _.
(* endfrag *)

(* End of file *)
