(* Element-wise identities *)

(* ================================================================ *)
(** ** Dependencies                                                 *)
(* ================================================================ *)

(* begfrag:6kd4trft *)
Require Import ufcoq.base.primitive.
Require Import ufcoq.base.construct.
Require Import ufcoq.base.ident.
(* endfrag *)

(* ================================================================ *)
(** ** The type of element-wise identities between two functions    *)
(* ================================================================ *)

(* begfrag:co56y2c4 *)
Definition ElIdent
  : forall (X : Type) (F : X -> Type),
      (forall (x : X), F x) -> (forall (x : X), F x) -> Type
  := fun (X : Type) (F : X -> Type) (f g : forall (x : X), F x)
       => forall (x : X), Ident (f x) (g x).

Arguments ElIdent {X F} _ _.
(* endfrag *)

(* ================================================================ *)
(** ** The composition of element-wise identities                   *)
(* ================================================================ *)

(* begfrag:y8meibm2 *)
Definition elident_compose
  : forall (X : Type) (F : X -> Type) (f g h : forall (x : X), F x),
      ElIdent f g -> ElIdent g h -> ElIdent f h
  := fun (X : Type)
         (F : X -> Type)
         (f g h : forall (x : X), F x)
         (u : ElIdent f g)
         (v : ElIdent g h)
         (x : X)
       => ident_compose (u x) (v x).

Arguments elident_compose {X F f g h} _ _ _.
(* endfrag *)

(* begfrag:71vv0fj5 *)
Definition elident_unit
  : forall (X : Type) (F : X -> Type) (f : forall (x : X), F x),
      ElIdent f f
  := fun (X : Type) (F : X -> Type) (f : forall (x : X), F x) (x : X)
       => ident_unit (f x).

Arguments elident_unit {X F} f _.
(* endfrag *)

(* begfrag:p37qw21f *)
Example _elident_left_unit
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g),
      Ident u (elident_compose (elident_unit f) u)
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
       => ident_unit u.
(* endfrag *)

(* begfrag:t3sjy81z *)
Definition elident_right_unit
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g),
      ElIdent u (elident_compose u (elident_unit g))
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (x : X)
       => ident_right_unit (u x).

Arguments elident_right_unit {X F f g} u _.
(* endfrag *)

(* begfrag:wtewrnwe *)
Definition elident_associative
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g)
           (h : forall (x : X), F x)
           (v : ElIdent g h)
           (k : forall (x : X), F x)
           (w : ElIdent h k),
      ElIdent (elident_compose (elident_compose u v) w)
              (elident_compose u (elident_compose v w))
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (h : forall (x : X), F x)
         (v : ElIdent g h)
         (k : forall (x : X), F x)
         (w : ElIdent h k)
         (x : X)
       => ident_associative (u x) (v x) (w x).

Arguments elident_associative {X F f g} u {h} v {k} w _.
(* endfrag *)

(* ================================================================ *)
(** ** The inverse of an element-wise identity                      *)
(* ================================================================ *)

(* begfrag:ik4ntli3 *)
Definition elident_inverse
  : forall (X : Type) (F : X -> Type) (f g : forall (x : X), F x),
      ElIdent f g -> ElIdent g f
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (x : X)
       => ident_inverse (u x).

Arguments elident_inverse {X F f g} _ _.
(* endfrag *)

(* begfrag:9m6otq6d *)
Example _elident_inverse_elident_unit
  : forall (X : Type) (F : X -> Type) (f : forall (x : X), F x),
      Ident (elident_unit f) (elident_inverse (elident_unit f))
  := fun (X : Type) (F : X -> Type) (f : forall (x : X), F x)
       => ident_unit (elident_unit f).
(* endfrag *)

(* begfrag:gid6rleh *)
Definition elident_left_inverse
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g),
      ElIdent (elident_unit g) (elident_compose (elident_inverse u) u)
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (x : X)
       => ident_left_inverse (u x).

Arguments elident_left_inverse {X F f g} u _.
(* endfrag *)

(* begfrag:lwgvtwjn *)
Definition elident_right_inverse
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g),
      ElIdent (elident_unit f) (elident_compose u (elident_inverse u))
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (x : X)
       => ident_right_inverse (u x).

Arguments elident_right_inverse {X F f g} u _.
(* endfrag *)

(* ================================================================ *)
(** ** Map between element-wise identities induced by a function    *)
(* ================================================================ *)

(* begfrag:txudl228 *)
Definition elident_map
  : forall (X : Type)
           (F G : X -> Type)
           (g : forall (x : X), F x -> G x)
           (f f' : forall (x : X), F x),
      ElIdent f f'
        -> ElIdent (function_compose_relative g f)
                   (function_compose_relative g f')
  := fun (X : Type)
         (F G : X -> Type)
         (g : forall (x : X), F x -> G x)
         (f f' : forall (x : X), F x)
         (u : ElIdent f f')
         (x : X)
       => ident_map (g x) (u x).

Arguments elident_map {X F G} g {f f'} _ _.
(* endfrag *)

(* begfrag:wgqe66z2 *)
Example _elident_map_unital
  : forall (X : Type)
           (F G : X -> Type)
           (g : forall (x : X), F x -> G x)
           (f : forall (x : X), F x),
      Ident (elident_unit (function_compose_relative g f))
            (elident_map g (elident_unit f))
  := fun (X : Type)
         (F G : X -> Type)
         (g : forall (x : X), F x -> G x)
         (f : forall (x : X), F x)
       => ident_unit (elident_unit (function_compose_relative g f)).
(* endfrag *)

(* begfrag:aamndm5e *)
Definition elident_map_multiplicative
  : forall (X : Type)
           (F G : X -> Type)
           (g : forall (x : X), F x -> G x)
           (f f' : forall (x : X), F x)
           (u : ElIdent f f')
           (f'' : forall (x : X), F x)
           (v : ElIdent f' f''),
      ElIdent (elident_map g (elident_compose u v))
              (elident_compose (elident_map g u) (elident_map g v))
  := fun (X : Type)
         (F G : X -> Type)
         (g : forall (x : X), F x -> G x)
         (f f' : forall (x : X), F x)
         (u : ElIdent f f')
         (f'' : forall (x : X), F x)
         (v : ElIdent f' f'')
         (x : X)
       => ident_map_multiplicative (g x) (u x) (v x).

Arguments elident_map_multiplicative {X F G} g {f f'} u {f''} v _.
(* endfrag *)

(* begfrag:g478il5g *)
Definition elident_map_inverse
  : forall (X : Type)
           (F G : X -> Type)
           (g : forall (x : X), F x -> G x)
           (f f' : forall (x : X), F x)
           (u : ElIdent f f'),
      ElIdent (elident_map g (elident_inverse u))
              (elident_inverse (elident_map g u))
  := fun (X : Type)
         (F G : X -> Type)
         (g : forall (x : X), F x -> G x)
         (f f' : forall (x : X), F x)
         (u : ElIdent f f')
         (x : X)
       => ident_map_inverse (g x) (u x).

Arguments elident_map_inverse {X F G} g {f f'} u _.
(* endfrag *)

(* begfrag:ds0ru742 *)
Definition elident_map_left_inverse
  : forall (X : Type)
           (F G : X -> Type)
           (g : forall (x : X), F x -> G x)
           (f f' : forall (x : X), F x)
           (u : ElIdent f f'),
      ElIdent (elident_unit (function_compose_relative g f'))
              (elident_compose (elident_map g (elident_inverse u))
                               (elident_map g u))
  := fun (X : Type)
         (F G : X -> Type)
         (g : forall (x : X), F x -> G x)
         (f f' : forall (x : X), F x)
         (u : ElIdent f f')
         (x : X)
       => ident_map_left_inverse (g x) (u x).

Arguments elident_map_left_inverse {X F G} g {f f'} u _.
(* endfrag *)

(* begfrag:zox7kj4e *)
Definition elident_map_right_inverse
  : forall (X : Type)
           (F G : X -> Type)
           (g : forall (x : X), F x -> G x)
           (f f' : forall (x : X), F x)
           (u : ElIdent f f'),
      ElIdent (elident_unit (function_compose_relative g f))
              (elident_compose (elident_map g u)
                               (elident_map g (elident_inverse u)))
  := fun (X : Type)
         (F G : X -> Type)
         (g : forall (x : X), F x -> G x)
         (f f' : forall (x : X), F x)
         (u : ElIdent f f')
         (x : X)
       => ident_map_right_inverse (g x) (u x).

Arguments elident_map_right_inverse {X F G} g {f f'} u _.
(* endfrag *)

(* begfrag:agii1l4k *)
Definition elident_map_elident
  : forall (X : Type)
           (F G : X -> Type)
           (g : forall (x : X), F x -> G x)
           (f f' : forall (x : X), F x)
           (u v : ElIdent f f'),
      ElIdent u v -> ElIdent (elident_map g u) (elident_map g v)
  := fun (X : Type)
         (F G : X -> Type)
         (g : forall (x : X), F x -> G x)
         (f f' : forall (x : X), F x)
         (u v : ElIdent f f')
         (t : ElIdent u v)
         (x : X)
       => ident_map_ident (g x) (t x).

Arguments elident_map_elident {X F G} g {f f' u v} _ _.
(* endfrag *)

(* ================================================================ *)
(** ** Functoriality of the induced map                             *)
(* ================================================================ *)

(* begfrag:27ueztnj *)
Definition elident_map_function_unit
  : forall (X : Type)
           (F : X -> Type)
           (f f' : forall (x : X), F x)
           (u : ElIdent f f'),
      ElIdent u (elident_map (fun x => function_unit (F x)) u)
  := fun (X : Type)
         (F : X -> Type)
         (f f' : forall (x : X), F x)
         (u : ElIdent f f')
         (x : X)
       => ident_map_function_unit (u x).

Arguments elident_map_function_unit {X F f f'} u _.
(* endfrag *)

(* begfrag:o2v5r993 *)
Definition elident_map_function_compose
  : forall (X : Type)
           (F G H : X -> Type)
           (h : forall (x : X), G x -> H x)
           (g : forall (x : X), F x -> G x)
           (f f' : forall (x : X), F x)
           (u : ElIdent f f'),
      ElIdent (elident_map (fun x => function_compose (h x) (g x)) u)
              (elident_map h (elident_map g u))
  := fun (X : Type)
         (F G H : X -> Type)
         (h : forall (x : X), G x -> H x)
         (g : forall (x : X), F x -> G x)
         (f f' : forall (x : X), F x)
         (u : ElIdent f f')
         (x : X)
       => ident_map_function_compose (h x) (g x) (u x).

Arguments elident_map_function_compose {X F G H} h g {f f'} u _.
(* endfrag *)

(* begfrag:m6n8ri5v *)
Definition elident_map_constant_function
  : forall (X : Type)
           (F G : X -> Type)
           (k : forall (x : X), G x)
           (f f' : forall (x : X), F x)
           (u : ElIdent f f'),
      ElIdent (elident_unit k)
              (elident_map (fun x => constant_function (k x)) u)
  := fun (X : Type)
         (F G : X -> Type)
         (k : forall (x : X), G x)
         (f f' : forall (x : X), F x)
         (u : ElIdent f f')
         (x : X)
       => ident_map_constant_function (k x) (u x).

Arguments elident_map_constant_function {X F G} k {f f'} u _.
(* endfrag *)

(* ================================================================ *)
(** ** Cancellation laws                                            *)
(* ================================================================ *)

(* begfrag:akyqj87a *)
Definition elident_left_cancel
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g)
           (h : forall (x : X), F x)
           (v v' : ElIdent g h),
      ElIdent (elident_compose u v) (elident_compose u v')
        -> ElIdent v v'
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (h : forall (x : X), F x)
         (v v' : ElIdent g h)
         (w : ElIdent (elident_compose u v) (elident_compose u v'))
         (x : X)
       => ident_left_cancel (u x) (v x) (v' x) (w x).

Arguments elident_left_cancel {X F f g} u {h} v v' _ _.
(* endfrag *)

(* begfrag:fmknw8ax *)
Definition elident_left_remove
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u u' : ElIdent f g),
      ElIdent u u'
        -> forall (h : forall (x : X), F x) (v v' : ElIdent g h),
             ElIdent (elident_compose u v) (elident_compose u' v')
               -> ElIdent v v'
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u u' : ElIdent f g)
         (m : ElIdent u u')
         (h : forall (x : X), F x)
         (v v' : ElIdent g h)
         (n : ElIdent (elident_compose u v) (elident_compose u' v'))
         (x : X)
       => ident_left_remove (m x) (v x) (v' x) (n x).

Arguments elident_left_remove {X F f g u u'} _ {h} v v' _ _.
(* endfrag *)

(* begfrag:60txpujy *)
Definition elident_right_cancel
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u u' : ElIdent f g)
           (h : forall (x : X), F x)
           (v : ElIdent g h),
      ElIdent (elident_compose u v) (elident_compose u' v)
        -> ElIdent u u'
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u u' : ElIdent f g)
         (h : forall (x : X), F x)
         (v : ElIdent g h)
         (m : ElIdent (elident_compose u v) (elident_compose u' v))
         (x : X)
       => ident_right_cancel (u x) (u' x) (v x) (m x).

Arguments elident_right_cancel {X F f g} u u' {h} v _ _.
(* endfrag *)

(* begfrag:q48dm070 *)
Definition elident_right_remove
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u u' : ElIdent f g)
           (h : forall (x : X), F x)
           (v v' : ElIdent g h),
      ElIdent v v'
        -> ElIdent (elident_compose u v) (elident_compose u' v')
             -> ElIdent u u'
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u u' : ElIdent f g)
         (h : forall (x : X), F x)
         (v v' : ElIdent g h)
         (m : ElIdent v v')
         (n : ElIdent (elident_compose u v) (elident_compose u' v'))
         (x : X)
       => ident_right_remove (u x) (u' x) (m x) (n x).

Arguments elident_right_remove {X F f g} u u' {h v v'} _ _ _.
(* endfrag *)

(* ================================================================ *)
(** ** Uniqueness of units                                          *)
(* ================================================================ *)

(* begfrag:j5dydai6 *)
Definition elident_left_unit_unique
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f f)
           (v : ElIdent f g),
      ElIdent v (elident_compose u v) -> ElIdent (elident_unit f) u
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f f)
         (v : ElIdent f g)
         (m : ElIdent v (elident_compose u v))
         (x : X)
       => ident_left_unit_unique (u x) (m x).

Arguments elident_left_unit_unique {X F f g} u {v} _ _.
(* endfrag *)

(* begfrag:fh0xo4ad *)
Definition elident_right_unit_unique
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g)
           (v : ElIdent g g),
      ElIdent u (elident_compose u v) -> ElIdent (elident_unit g) v
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (v : ElIdent g g)
         (m : ElIdent u (elident_compose u v))
         (x : X)
       => ident_right_unit_unique (v x) (m x).

Arguments elident_right_unit_unique {X F f g u} {v} _ _.
(* endfrag *)

(* ================================================================ *)
(** ** Uniqueness of inverses                                       *)
(* ================================================================ *)

(* begfrag:vs7tl4u9 *)
Definition elident_left_inverse_unique
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g)
           (v : ElIdent g f),
      ElIdent (elident_compose u v) (elident_unit f)
        -> ElIdent u (elident_inverse v)
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (v : ElIdent g f)
         (m : ElIdent (elident_compose u v) (elident_unit f))
         (x : X)
       => ident_left_inverse_unique (u x) (v x) (m x).

Arguments elident_left_inverse_unique {X F f g} u v _ _.
(* endfrag *)

(* begfrag:t1atd1l4 *)
Definition elident_right_inverse_unique
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g)
           (v : ElIdent g f),
      ElIdent (elident_compose u v) (elident_unit f)
        -> ElIdent v (elident_inverse u)
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (v : ElIdent g f)
         (m : ElIdent (elident_compose u v) (elident_unit f))
         (x : X)
       => ident_right_inverse_unique (u x) (v x) (m x).

Arguments elident_right_inverse_unique {X F f g} u v _ _.
(* endfrag *)

(* ================================================================ *)
(** ** Antimultiplicativity of inversion                            *)
(* ================================================================ *)

(* begfrag:6irt90jo *)
Definition elident_left_inverse_antimultiplicative
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g)
           (h : forall (x : X), F x)
           (v : ElIdent g h),
      ElIdent (elident_inverse (elident_compose u v))
              (elident_compose (elident_inverse v)
                               (elident_inverse u))
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (h : forall (x : X), F x)
         (v : ElIdent g h)
         (x : X)
       => ident_inverse_antimultiplicative (u x) (v x).

Arguments elident_left_inverse_antimultiplicative {X F f g} u {h} v _.
(* endfrag *)

(* ================================================================ *)
(** ** Involutivity of inversion                                    *)
(* ================================================================ *)

(* begfrag:sppcwq10 *)
Definition elident_inverse_involutive
  : forall (X : Type)
           (F : X -> Type)
           (f g : forall (x : X), F x)
           (u : ElIdent f g),
      ElIdent u (elident_inverse (elident_inverse u))
  := fun (X : Type)
         (F : X -> Type)
         (f g : forall (x : X), F x)
         (u : ElIdent f g)
         (x : X)
       => ident_inverse_involutive (u x).

Arguments elident_inverse_involutive {X F f g} u _.
(* endfrag *)

(* ================================================================ *)
(** ** Triviality of idempotent identities                          *)
(* ================================================================ *)

(* begfrag:az2c536p *)
Definition elident_idempotent_trivial
  : forall (X : Type)
           (F : X -> Type)
           (f : forall (x : X), F x)
           (u : ElIdent f f),
      ElIdent u (elident_compose u u) -> ElIdent (elident_unit f) u
  := fun (X : Type)
         (F : X -> Type)
         (f : forall (x : X), F x)
         (u : ElIdent f f)
         (m : ElIdent u (elident_compose u u))
         (x : X)
       => ident_idempotent_trivial (m x).

Arguments elident_idempotent_trivial {X F f u} _ _.
(* endfrag *)

(* ================================================================ *)
(** ** Left whiskers                                                *)
(* ================================================================ *)

(* begfrag:n9kthv7k *)
Definition elident_left_whisker
  : forall (X Y : Type)
           (f : X -> Y)
           (G : Y -> Type)
           (g g' : forall (y : Y), G y),
      ElIdent g g'
        -> ElIdent (function_compose g f) (function_compose g' f)
  := fun (X Y : Type)
         (f : X -> Y)
         (G : Y -> Type)
         (g g' : forall (y : Y), G y)
         (v : ElIdent g g')
       => function_compose v f.

Arguments elident_left_whisker {X Y} f {G g g'} _ _.
(* endfrag *)

(* begfrag:4dhofnge *)
Example _elident_left_whisker_left_unit
  : forall (Y : Type)
           (G : Y -> Type)
           (g g' : forall (y : Y), G y)
           (v : ElIdent g g'),
      Ident v (elident_left_whisker (function_unit Y) v)
  := fun (Y : Type)
         (G : Y -> Type)
         (g g' : forall (y : Y), G y)
         (v : ElIdent g g')
       => ident_unit v.
(* endfrag *)

(* begfrag:1ekr8yu5 *)
Example _elident_left_whisker_right_unit
  : forall (X Y : Type)
           (f : X -> Y)
           (G : Y -> Type)
           (g : forall (y : Y), G y),
      Ident (elident_unit (function_compose g f))
            (elident_left_whisker f (elident_unit g))
  := fun (X Y : Type)
         (f : X -> Y)
         (G : Y -> Type)
         (g : forall (y : Y), G y)
       => ident_unit (elident_unit (function_compose g f)).
(* endfrag *)

(* begfrag:r675qcui *)
Example _elident_left_whisker_multiplicative
  : forall (W X : Type)
           (e : W -> X)
           (Y : Type)
           (f : X -> Y)
           (G : Y -> Type)
           (g g' : forall (y : Y), G y)
           (v : ElIdent g g'),
      Ident (elident_left_whisker e (elident_left_whisker f v))
            (elident_left_whisker (function_compose f e) v)
  := fun (W X : Type)
         (e : W -> X)
         (Y : Type)
         (f : X -> Y)
         (G : Y -> Type)
         (g g' : forall (y : Y), G y)
         (v : ElIdent g g')
       => ident_unit (elident_left_whisker (function_compose f e) v).
(* endfrag *)

(* begfrag:ze3vq2sn *)
Example _elident_left_whisker_distributive
  : forall (X Y : Type)
           (f : X -> Y)
           (G : Y -> Type)
           (g g' : forall (y : Y), G y)
           (v : ElIdent g g')
           (g'' : forall (y :Y), G y)
           (v' : ElIdent g' g''),
      Ident (elident_left_whisker f (elident_compose v v'))
            (elident_compose (elident_left_whisker f v)
                             (elident_left_whisker f v'))
  := fun (X Y : Type)
         (f : X -> Y)
         (G : Y -> Type)
         (g g' : forall (y : Y), G y)
         (v : ElIdent g g')
         (g'' : forall (y :Y), G y)
         (v' : ElIdent g' g'')
       => ident_unit (elident_left_whisker f (elident_compose v v')).
(* endfrag *)

(* ================================================================ *)
(** ** Right whiskers                                               *)
(* ================================================================ *)

(* begfrag:arugrwdw *)
Definition elident_right_whisker
  : forall (X Y : Type)
           (f f' : X -> Y)
           (u : ElIdent f f')
           (Z : Type)
           (g : Y -> Z),
      ElIdent (function_compose g f) (function_compose g f')
  := fun (X Y : Type)
         (f f' : X -> Y)
         (u : ElIdent f f')
         (Z : Type)
         (g : Y -> Z)
         (x : X)
       => ident_map g (u x).

Arguments elident_right_whisker {X Y f f'} u {Z} g _.
(* endfrag *)

(* begfrag:11pr6htm *)
Example _elident_right_whisker_left_unit
  : forall (X Y : Type)
           (f : X -> Y)
           (Z : Type)
           (g : Y -> Z),
      Ident (elident_unit (function_compose g f))
            (elident_right_whisker (elident_unit f) g)
  := fun (X Y : Type)
         (f : X -> Y)
         (Z : Type)
         (g : Y -> Z)
       => ident_unit (elident_unit (function_compose g f)).
(* endfrag *)

(* begfrag:9r60tfyq *)
Definition elident_right_whisker_right_unit
  : forall (X Y : Type)
           (f f' : X -> Y)
           (u : ElIdent f f'),
      ElIdent u (elident_right_whisker u (function_unit Y))
  := fun (X Y : Type)
         (f f' : X -> Y)
         (u : ElIdent f f')
         (x : X)
       => ident_map_function_unit (u x).

Arguments elident_right_whisker_right_unit {X Y f f'} u _.
(* endfrag *)

(* begfrag:8zn6tmoq *)
Definition elident_right_whisker_multiplicative
  : forall (X Y : Type)
           (f f' : X -> Y)
           (u : ElIdent f f')
           (Z : Type)
           (g : Y -> Z)
           (W : Type)
           (h : Z -> W),
      ElIdent (elident_right_whisker u (function_compose h g))
              (elident_right_whisker (elident_right_whisker u g) h)
  := fun (X Y : Type)
         (f f' : X -> Y)
         (u : ElIdent f f')
         (Z : Type)
         (g : Y -> Z)
         (W : Type)
         (h : Z -> W)
         (x : X)
       => ident_map_function_compose h g (u x).

Arguments elident_right_whisker_multiplicative
  {X Y f f'} u {Z} g {W} h _.
(* endfrag *)

(* begfrag:g1hlctv4 *)
Definition elident_right_whisker_distributive
  : forall (X Y : Type)
           (f f' : X -> Y)
           (u : ElIdent f f')
           (f'' : X -> Y)
           (u' : ElIdent f' f'')
           (Z : Type)
           (g : Y -> Z),
      ElIdent (elident_right_whisker (elident_compose u u') g)
              (elident_compose (elident_right_whisker u g)
                               (elident_right_whisker u' g))
  := fun (X Y : Type)
         (f f' : X -> Y)
         (u : ElIdent f f')
         (f'' : X -> Y)
         (u' : ElIdent f' f'')
         (Z : Type)
         (g : Y -> Z)
         (x : X)
       => ident_map_multiplicative g (u x) (u' x).

Arguments elident_right_whisker_distributive
  {X Y f f'} u {f''} u' {Z} g _.
(* endfrag *)

(* ================================================================ *)
(** ** Compatibility of left and right whiskers                     *)
(* ================================================================ *)

(* begfrag:2orfma4h *)
Example _elident_left_right_whisker
  : forall (X Y : Type)
           (f : X -> Y)
           (Z : Type)
           (g g' : Y -> Z)
           (u : ElIdent g g')
           (W : Type)
           (h : Z -> W),
      Ident (elident_left_whisker f (elident_right_whisker u h))
            (elident_right_whisker (elident_left_whisker f u) h)
  := fun (X Y : Type)
         (f : X -> Y)
         (Z : Type)
         (g g' : Y -> Z)
         (u : ElIdent g g')
         (W : Type)
         (h : Z -> W)
       => ident_unit
            (elident_left_whisker f (elident_right_whisker u h)).
(* endfrag *)

(* ================================================================ *)
(** ** Naturality                                                   *)
(* ================================================================ *)

(* begfrag:9dorgp04 *)
Definition elident_natural
  : forall (X Y : Type)
           (f g : X -> Y)
           (u : ElIdent f g)
           (x x' : X)
           (p : Ident x x'),
      Ident (ident_compose (ident_map f p) (u x'))
            (ident_compose (u x) (ident_map g p))
  := fun (X Y : Type) (f g : X -> Y) (u : ElIdent f g) (x : X)
       =>
         let
           F : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => Ident (ident_compose (ident_map f p) (u x'))
                           (ident_compose (u x) (ident_map g p))
         in let
           base : F x (ident_unit x)
             := ident_right_unit (u x)
         in
           ident_induction x F base.

Arguments elident_natural {X Y f g} u {x x'} p.
(* endfrag *)

(* ================================================================ *)
(** ** Element-wise identities to unit functions                    *)
(* ================================================================ *)

(* begfrag:n82uc7fi *)
Definition elident_natural_function_unit
  : forall (X : Type)
           (f : X -> X)
           (u : ElIdent f (function_unit X))
           (x x' : X)
           (p : Ident x x'),
      Ident (ident_compose (ident_map f p) (u x'))
            (ident_compose (u x) p)
  := fun (X : Type)
         (f : X -> X)
         (u : ElIdent f (function_unit X))
         (x : X)
       =>
         let
           G : forall (x' : X), Ident x x' -> Type
             := fun (x' : X) (p : Ident x x')
                  => Ident (ident_compose (ident_map f p) (u x'))
                           (ident_compose (u x) p)
         in let
           base : G x (ident_unit x)
             := ident_right_unit (u x)
         in
           ident_induction x G base.

Arguments elident_natural_function_unit {X f} u {x x'} p.
(* endfrag *)

(* begfrag:f7ji65jy *)
Definition elident_function_unit
  : forall (X : Type)
           (f : X -> X)
           (u : ElIdent f (function_unit X))
           (x : X),
      Ident (ident_map f (u x))
            (u (f x))
  := fun (X : Type)
         (f : X -> X)
         (u : ElIdent f (function_unit X))
         (x : X)
       =>
         let
           r : Ident (ident_compose (ident_map f (u x)) (u x))
                     (ident_compose (u (f x)) (u x))
             := elident_natural_function_unit u (u x)
         in
           ident_right_cancel (ident_map f (u x)) (u (f x)) (u x) r.

Arguments elident_function_unit {X f} u x.
(* endfrag *)

(* ================================================================ *)
(** ** Horizontal composition of element-wise identities            *)
(* ================================================================ *)

(* begfrag:scjvqrb1 *)
Definition elident_compose_horizontal
  : forall (X Y : Type)
           (f f' : X -> Y),
      ElIdent f f'
        -> forall (Z : Type) (g g' : Y -> Z),
             ElIdent g g'
               -> ElIdent (function_compose g f)
                          (function_compose g' f')
  := fun (X Y : Type)
         (f f' : X -> Y)
         (u : ElIdent f f')
         (Z : Type)
         (g g' : Y -> Z)
         (v : ElIdent g g')
       =>
         let
           e1 : ElIdent (function_compose g f)
                        (function_compose g f')
              := elident_right_whisker u g
         in let
           e2 : ElIdent (function_compose g f')
                        (function_compose g' f')
              := elident_left_whisker f' v
         in
           elident_compose e1 e2.

Arguments elident_compose_horizontal {X Y f f'} _ {Z g g'} _ _.
(* endfrag *)

(* begfrag:l64pkoo3 *)
Definition elident_compose_horizontal2
  : forall (X Y : Type)
           (f f' : X -> Y),
      ElIdent f f'
        -> forall (Z : Type) (g g' : Y -> Z),
             ElIdent g g'
               -> ElIdent (function_compose g f)
                          (function_compose g' f')
  := fun (X Y : Type)
         (f f' : X -> Y)
         (u : ElIdent f f')
         (Z : Type)
         (g g' : Y -> Z)
         (v : ElIdent g g')
       =>
         let
           e1 : ElIdent (function_compose g f)
                        (function_compose g' f)
              := elident_left_whisker f v
         in let
           e2 : ElIdent (function_compose g' f)
                        (function_compose g' f')
              := elident_right_whisker u g'
         in
           elident_compose e1 e2.

Arguments elident_compose_horizontal2 {X Y f f'} _ {Z g g'} _ _.
(* endfrag *)

(* begfrag:zwqfgefo *)
Definition elident_compose_horizontals_elident
  : forall (X Y : Type)
           (f f' : X -> Y)
           (u : ElIdent f f')
           (Z : Type)
           (g g' : Y -> Z)
           (v : ElIdent g g'),
      ElIdent (elident_compose_horizontal u v)
              (elident_compose_horizontal2 u v)
  := fun (X Y : Type)
         (f f' : X -> Y)
         (u : ElIdent f f')
         (Z : Type)
         (g g' : Y -> Z)
         (v : ElIdent g g')
         (x : X)
       => elident_natural v (u x).

Arguments elident_compose_horizontals_elident
  {X Y f f'} u {Z g g'} v _.
(* endfrag *)

(* ================================================================ *)
(** ** The Eckmann-Hilton argument                                  *)
(* ================================================================ *)

(* begfrag:koiabxgc *)
Definition elident_eckmann_hilton1
  : forall (X : Type)
           (u v : ElIdent (function_unit X) (function_unit X)),
      ElIdent (elident_compose u v) (elident_compose_horizontal u v)
  := fun (X : Type)
         (u v : ElIdent (function_unit X) (function_unit X))
         (x : X)
       => ident_map (fun p => ident_compose p (v x))
                    (ident_map_function_unit (u x)).

Arguments elident_eckmann_hilton1 {X} u v _.
(* endfrag *)

(* begfrag:dn9a3hzp *)
Definition elident_eckmann_hilton2
  : forall (X : Type)
           (u v : ElIdent (function_unit X) (function_unit X)),
      ElIdent (elident_compose u v) (elident_compose v u)
  := fun (X : Type)
         (u v : ElIdent (function_unit X) (function_unit X))
       =>
         let
           e1 : ElIdent (elident_compose u v)
                        (elident_compose_horizontal u v)
              := elident_eckmann_hilton1 u v
         in let
           e2 : ElIdent (elident_compose_horizontal u v)
                        (elident_compose_horizontal2 u v)
              := elident_compose_horizontals_elident u v
         in let
           e3 : ElIdent (elident_compose u v)
                        (elident_compose_horizontal2 u v)
              := elident_compose e1 e2
         in let
           m : ElIdent (elident_compose v u)
                       (elident_compose_horizontal2 u v)
             := fun (x : X)
                  => ident_map (fun p => ident_compose (v x) p)
                               (ident_map_function_unit (u x))
         in let
           e4 : ElIdent (elident_compose_horizontal2 u v)
                        (elident_compose v u)
              := elident_inverse m
         in
           elident_compose e3 e4.

Arguments elident_eckmann_hilton2 {X} u v _.
(* endfrag *)

(* ================================================================ *)
(** ** Properties of horizontal composition                         *)
(* ================================================================ *)

(* begfrag:fv91hut3 *)
Example _elident_horizontal_left_unit
  : forall (X Y : Type)
           (f : X -> Y)
           (Z : Type)
           (g g' : Y -> Z)
           (v : ElIdent g g'),
      Ident (elident_left_whisker f v)
            (elident_compose_horizontal (elident_unit f) v)
  := fun (X Y : Type)
         (f : X -> Y)
         (Z : Type)
         (g g' : Y -> Z)
         (v : ElIdent g g')
       => ident_unit (elident_left_whisker f v).
(* endfrag *)

(* begfrag:uhfwa9n3 *)
Example _elident_horizontal_units
  : forall (X Y : Type)
           (f : X -> Y)
           (Z : Type)
           (g : Y -> Z),
      Ident (elident_unit (function_compose g f))
            (elident_compose_horizontal (elident_unit f)
                                        (elident_unit g))
  := fun (X Y : Type)
         (f : X -> Y)
         (Z : Type)
         (g : Y -> Z)
       => ident_unit (elident_unit (function_compose g f)).
(* endfrag *)

(* begfrag:2fg6iw8w *)
Definition elident_horizontal_right_unit
  : forall (X Y : Type)
           (f f' : X -> Y)
           (u : ElIdent f f')
           (Z : Type)
           (g : Y -> Z),
      ElIdent (elident_right_whisker u g)
              (elident_compose_horizontal u (elident_unit g))
  := fun (X Y : Type)
         (f f' : X -> Y)
         (u : ElIdent f f')
         (Z : Type)
         (g : Y -> Z)
         (x : X)
       => ident_right_unit (ident_map g (u x)).

Arguments elident_horizontal_right_unit {X Y f f'} u {Z} g _.
(* endfrag *)

(* begfrag:8vatl8dn *)
Example _elident_horizontal_whisker1
  : forall (A B : Type)
           (f : A -> B)
           (C : Type)
           (g g' : B -> C)
           (v : ElIdent g g')
           (D : Type)
           (h h' : C -> D)
           (w : ElIdent h h'),
      Ident (elident_left_whisker f (elident_compose_horizontal v w))
            (elident_compose_horizontal (elident_left_whisker f v) w)
  := fun (A B : Type)
         (f : A -> B)
         (C : Type)
         (g g' : B -> C)
         (v : ElIdent g g')
         (D : Type)
         (h h' : C -> D)
         (w : ElIdent h h')
       => ident_unit
            (elident_left_whisker f (elident_compose_horizontal v w)).
(* endfrag *)

(* begfrag:hsca04vt *)
Definition elident_horizontal_whisker2
  : forall (A B : Type)
           (f f' : A -> B)
           (u : ElIdent f f')
           (C : Type)
           (g : B -> C)
           (D : Type)
           (h h' : C -> D)
           (w : ElIdent h h'),
      ElIdent
        (elident_compose_horizontal u (elident_left_whisker g w))
        (elident_compose_horizontal (elident_right_whisker u g) w)
  := fun (A B : Type)
         (f f' : A -> B)
         (u : ElIdent f f')
         (C : Type)
         (g : B -> C)
         (D : Type)
         (h h' : C -> D)
         (w : ElIdent h h')
         (x : A)
       => ident_map (fun p => ident_compose p (w (g (f' x))))
                    (ident_map_function_compose h g (u x)).

Arguments elident_horizontal_whisker2 {A B f f'} u {C} g {D h h'} w _.
(* endfrag *)

(* begfrag:kba07aid *)
Definition elident_horizontal_whisker3
  : forall (A B : Type)
           (f f' : A -> B)
           (u : ElIdent f f')
           (C : Type)
           (g g' : B -> C)
           (v : ElIdent g g')
           (D : Type)
           (h : C -> D),
      ElIdent
        (elident_right_whisker (elident_compose_horizontal u v) h)
        (elident_compose_horizontal u (elident_right_whisker v h))
  := fun (A B : Type)
           (f f' : A -> B)
           (u : ElIdent f f')
           (C : Type)
           (g g' : B -> C)
           (v : ElIdent g g')
           (D : Type)
           (h : C -> D)
           (x : A)
       =>
         let
           e1 : Ident (elident_right_whisker
                         (elident_compose_horizontal u v) h x)
                      (ident_compose (ident_map h (ident_map g (u x)))
                                     (ident_map h (v (f' x))))
              := ident_map_multiplicative h
                                         (ident_map g (u x))
                                         (v (f' x))
         in let
           e2 : Ident (elident_compose_horizontal
                         u (elident_right_whisker v h) x)
                      (ident_compose (ident_map h (ident_map g (u x)))
                                     (ident_map h (v (f' x))))
              := ident_map
                   (fun p => ident_compose p (ident_map h (v (f' x))))
                   (ident_map_function_compose h g (u x))
         in
           ident_compose e1 (ident_inverse e2).

Arguments elident_horizontal_whisker3 {A B f f'} u {C g g'} v {D} h _.
(* endfrag *)

(* begfrag:28so8564 *)
Definition elident_horizontal_associative
  : forall (A B : Type)
           (f f' : A -> B)
           (u : ElIdent f f')
           (C : Type)
           (g g' : B -> C)
           (v : ElIdent g g')
           (D : Type)
           (h h' : C -> D)
           (w : ElIdent h h'),
      ElIdent (elident_compose_horizontal
                 (elident_compose_horizontal u v) w)
              (elident_compose_horizontal
                 u (elident_compose_horizontal v w))
  := fun (A B : Type)
         (f f' : A -> B)
         (u : ElIdent f f')
         (C : Type)
         (g g' : B -> C)
         (v : ElIdent g g')
         (D : Type)
         (h h' : C -> D)
         (w : ElIdent h h')
         (x : A)
       =>
         let
           e1 : Ident (elident_compose_horizontal
                         (elident_compose_horizontal u v) w x)
                      (ident_compose
                         (ident_compose
                            (ident_map h (ident_map g (u x)))
                            (ident_map h (v (f' x))))
                         (w (g' (f' x))))
              := ident_map
                   (fun p => ident_compose p (w (g' (f' x))))
                   (ident_map_multiplicative h
                                             (ident_map g (u x))
                                             (v (f' x)))
         in let
           e2 : Ident (ident_compose
                         (ident_compose
                            (ident_map h (ident_map g (u x)))
                            (ident_map h (v (f' x))))
                         (w (g' (f' x))))
                      (ident_compose
                         (ident_map h (ident_map g (u x)))
                         (ident_compose (ident_map h (v (f' x)))
                                        (w (g' (f' x)))))
              := ident_associative (ident_map h (ident_map g (u x)))
                                   (ident_map h (v (f' x)))
                                   (w (g' (f' x)))
         in let
           e3 : Ident (elident_compose_horizontal
                         u (elident_compose_horizontal v w) x)
                      (ident_compose
                         (ident_map h (ident_map g (u x)))
                         (ident_compose (ident_map h (v (f' x)))
                                        (w (g' (f' x)))))
              := ident_map
                   (fun p => ident_compose
                               p
                               (ident_compose (ident_map h (v (f' x)))
                                              (w (g' (f' x)))))
                   (ident_map_function_compose h g (u x))
         in
           ident_compose (ident_compose e1 e2)
                         (ident_inverse e3).

Arguments elident_horizontal_associative
  {A B f f'} u {C g g'} v {D h h'} w _.
(* endfrag *)

(* ================================================================ *)
(** ** The middle four interchange law                              *)
(* ================================================================ *)

(* begfrag:am5zcqt8 *)
Definition elident_middle4_interchange
  : forall (A B : Type)
           (f f' : A -> B)
           (u : ElIdent f f')
           (f'' : A -> B)
           (u' : ElIdent f' f'')
           (C : Type)
           (g g' : B -> C)
           (v : ElIdent g g')
           (g'' : B -> C)
           (v' : ElIdent g' g''),
      ElIdent (elident_compose_horizontal (elident_compose u u')
                                          (elident_compose v v'))
              (elident_compose (elident_compose_horizontal u v)
                               (elident_compose_horizontal u' v'))
  := fun (A B : Type)
         (f f' : A -> B)
         (u : ElIdent f f')
         (f'' : A -> B)
         (u' : ElIdent f' f'')
         (C : Type)
         (g g' : B -> C)
         (v : ElIdent g g')
         (g'' : B -> C)
         (v' : ElIdent g' g'')
         (x : A)
       =>
         let
           e1 : Ident (elident_compose_horizontal
                         (elident_compose u u')
                         (elident_compose v v') x)
                      (ident_compose
                         (ident_compose (ident_map g (u x))
                                        (ident_map g (u' x)))
                         (ident_compose (v (f'' x)) (v' (f'' x))))
              := ident_map
                   (fun p => (ident_compose
                                p (ident_compose (v (f'' x))
                                                 (v' (f'' x)))))
                   (ident_map_multiplicative g (u x) (u' x))
         in let
           e2 : Ident (ident_compose
                         (ident_compose (ident_map g (u x))
                                        (ident_map g (u' x)))
                         (ident_compose (v (f'' x)) (v' (f'' x))))
                      (ident_compose
                         (ident_compose
                            (ident_map g (u x))
                            (ident_compose (ident_map g (u' x))
                                           (v (f'' x))))
                         (v' (f'' x)))
              := ident_compose (ident_inverse
                                  (ident_associative41
                                     (ident_map g (u x))
                                     (ident_map g (u' x))
                                     (v (f'' x))
                                     (v' (f'' x))))
                               (ident_associative43
                                  (ident_map g (u x))
                                  (ident_map g (u' x))
                                  (v (f'' x))
                                  (v' (f'' x)))
         in let
           e3 : Ident (ident_compose
                         (ident_compose
                            (ident_map g (u x))
                            (ident_compose (ident_map g (u' x))
                                           (v (f'' x))))
                         (v' (f'' x)))
                      (ident_compose
                         (ident_compose
                            (ident_map g (u x))
                            (ident_compose (v (f' x))
                                           (ident_map g' (u' x))))
                         (v' (f'' x)))
              := ident_map (fun p
                              => (ident_compose
                                    (ident_compose
                                       (ident_map g (u x)) p)
                                    (v' (f'' x))))
                           (elident_natural v (u' x))
         in let
           e4 : Ident (ident_compose
                         (ident_compose
                            (ident_map g (u x))
                            (ident_compose (v (f' x))
                                           (ident_map g' (u' x))))
                         (v' (f'' x)))
                      (elident_compose
                         (elident_compose_horizontal u v)
                         (elident_compose_horizontal u' v') x)
              := ident_compose (ident_inverse
                                  (ident_associative43
                                     (ident_map g (u x))
                                     (v (f' x))
                                     (ident_map g' (u' x))
                                     (v' (f'' x))))
                               (ident_associative41
                                  (ident_map g (u x))
                                  (v (f' x))
                                  (ident_map g' (u' x))
                                  (v' (f'' x)))
         in
           ident_compose (ident_compose (ident_compose e1 e2) e3) e4.

Arguments elident_middle4_interchange
  {A B f f'} u {f''} u' {C g g'} v {g''} v' _.
(* endfrag *)

(* ================================================================ *)
(** ** Element-wise identities from identities                      *)
(* ================================================================ *)

(* begfrag:ybi5etby *)
Definition elident_of_ident
  : forall (X : Type) (F : X -> Type) (f g : forall (x : X), F x),
      Ident f g -> ElIdent f g
  := fun (X : Type) (F : X -> Type) (f : forall (x : X), F x)
       => ident_recursion f (ElIdent f) (elident_unit f).

Arguments elident_of_ident {X F f g} _ _.
(* endfrag *)

(* End of file *)
