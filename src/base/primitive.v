(* The primitive types *)

(* ================================================================ *)
(** ** Notation for builtin function types with constant codomain   *)
(* ================================================================ *)

(** begfrag:notation-function-type *)
Notation "X -> Y" := (forall (_ : X), Y)
  (at level 99, right associativity, Y at level 200).
(** endfrag:notation-function-type *)

(* ================================================================ *)
(** ** The false type                                               *)
(* ================================================================ *)

(** begfrag:false-type *)
Inductive False@{l} : Type@{l} := .
(** endfrag:false-type *)

(** begfrag:false-induction *)
Definition false_induction@{l m}
  : forall (F : False@{l} -> Type@{m}) (x : False@{l}), F x
  := False_rect@{l m}.
(** endfrag:false-induction *)

(* ================================================================ *)
(** ** The true type                                                *)
(* ================================================================ *)

(** begfrag:true-type *)
Inductive True@{l} : Type@{l} := only : True.
(** endfrag:true-type *)

(** begfrag:true-induction *)
Definition true_induction@{l m}
  : forall (F : True@{l} -> Type@{m}),
      F only@{l} -> forall (x : True@{l}), F x
  := True_rect@{l m}.
(** endfrag:true-induction *)

(* ================================================================ *)
(** ** The boolean type                                             *)
(* ================================================================ *)

(** begfrag:boolean-type *)
Inductive Boolean@{l} : Type@{l} := yes : Boolean | no : Boolean.
(** endfrag:boolean-type *)

(** begfrag:boolean-induction *)
Definition boolean_induction@{l m}
  : forall (F : Boolean@{l} -> Type@{m}),
      F yes@{l} -> F no@{l} -> forall (x : Boolean@{l}), F x
  := Boolean_rect@{l m}.
(** endfrag:boolean-induction *)

(* ================================================================ *)
(** ** The type of natural numbers                                  *)
(* ================================================================ *)

(** begfrag:natural-type *)
Inductive Natural@{l} : Type@{l}
  := zero : Natural | successor : Natural -> Natural.
(** endfrag:natural-type *)

(** begfrag:natural-induction *)
Definition natural_induction@{l m}
  : forall (F : Natural@{l} -> Type@{m}),
      F zero@{l}
        -> (forall (n : Natural@{l}), F n -> F (successor@{l} n))
            -> forall (n : Natural@{l}), F n
  := Natural_rect@{l m}.
(** endfrag:natural-induction *)

(* ================================================================ *)
(** ** Equality types                                               *)
(* ================================================================ *)

(** begfrag:equal-type *)
Inductive Equal@{l} (X : Type@{l}) (x : X) : X -> Type@{l}
  := reflexive : Equal X x x.
(** endfrag:equal-type *)

(** begfrag:equal-induction *)
Definition equal_induction@{l m}
  : forall (X : Type@{l})
           (x : X)
           (F : forall (x' : X), Equal@{l} X x x' -> Type@{m}),
      F x (reflexive@{l} X x)
        -> forall (x' : X) (p : Equal@{l} X x x'), F x' p
  := Equal_rect@{l m}.
(** endfrag:equal-induction *)

(* ================================================================ *)
(* Sigma types                                                      *)
(* ================================================================ *)

(** begfrag:sigma-type *)
Record _Sigma@{l m} (X : Type@{l}) (F : X -> Type@{m})
  : Type@{max(l, m)}
  := pair {
       first : X;
       second : F first;
     }.

Arguments _Sigma {X} F.
(** endfrag:sigma-type *)

(** begfrag:notation-sigma-type *)
Notation "'Sigma' x .. y , P"
  := (_Sigma (fun x => .. (_Sigma (fun y => P)) ..))
       (at level 200, x binder, y binder, right associativity).
(** endfrag:notation-sigma-type *)

(* End of file *)
