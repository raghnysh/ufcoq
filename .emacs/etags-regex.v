(* Test file for Emacs tags *)

(* ================================================================ *)
(* Definition                                                       *)
(* ================================================================ *)

Definition foo_definition etc
  etc
  etc

Definition bar_definition@{etc etc | etc} etc
  etc
  etc

Local Definition baz_definition etc
  etc
  etc

Local Definition quux_definition@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Inductive                                                        *)
(* ================================================================ *)

Inductive foo_inductive etc
  etc
  etc

Inductive bar_inductive@{etc etc | etc} etc
  etc
  etc

Local Inductive baz_inductive etc
  etc
  etc

Local Inductive quux_inductive@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Record                                                           *)
(* ================================================================ *)

Record foo_record etc
  etc
  etc

Record bar_record@{etc etc | etc} etc
  etc
  etc

Local Record baz_record etc
  etc
  etc

Local Record quux_record@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Theorem                                                          *)
(* ================================================================ *)

Theorem foo_theorem etc
  etc
  etc

Theorem bar_theorem@{etc etc | etc} etc
  etc
  etc

Local Theorem baz_theorem etc
  etc
  etc

Local Theorem quux_theorem@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Proposition                                                      *)
(* ================================================================ *)

Proposition foo_proposition etc
  etc
  etc

Proposition bar_proposition@{etc etc | etc} etc
  etc
  etc

Local Proposition baz_proposition etc
  etc
  etc

Local Proposition quux_proposition@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Lemma                                                            *)
(* ================================================================ *)

Lemma foo_lemma etc
  etc
  etc

Lemma bar_lemma@{etc etc | etc} etc
  etc
  etc

Local Lemma baz_lemma etc
  etc
  etc

Local Lemma quux_lemma@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Corollary                                                        *)
(* ================================================================ *)

Corollary foo_corollary etc
  etc
  etc

Corollary bar_corollary@{etc etc | etc} etc
  etc
  etc

Local Corollary baz_corollary etc
  etc
  etc

Local Corollary quux_corollary@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Remark                                                           *)
(* ================================================================ *)

Remark foo_remark etc
  etc
  etc

Remark bar_remark@{etc etc | etc} etc
  etc
  etc

Local Remark baz_remark etc
  etc
  etc

Local Remark quux_remark@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Fact                                                             *)
(* ================================================================ *)

Fact foo_fact etc
  etc
  etc

Fact bar_fact@{etc etc | etc} etc
  etc
  etc

Local Fact baz_fact etc
  etc
  etc

Local Fact quux_fact@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Property                                                         *)
(* ================================================================ *)

Property foo_property etc
  etc
  etc

Property bar_property@{etc etc | etc} etc
  etc
  etc

Local Property baz_property etc
  etc
  etc

Local Property quux_property@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Axiom                                                            *)
(* ================================================================ *)

Axiom foo_axiom etc
  etc
  etc

Axiom bar_axiom@{etc etc | etc} etc
  etc
  etc

Local Axiom baz_axiom etc
  etc
  etc

Local Axiom quux_axiom@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Coercion                                                         *)
(* ================================================================ *)

Coercion foo_coercion etc
  etc
  etc

Coercion bar_coercion@{etc etc | etc} etc
  etc
  etc

Local Coercion baz_coercion etc
  etc
  etc

Local Coercion quux_coercion@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Identity Coercion                                                *)
(* ================================================================ *)

Identity Coercion foo_identity_coercion etc
  etc
  etc

Identity Coercion bar_identity_coercion@{etc etc | etc} etc
  etc
  etc

Local Identity Coercion baz_identity_coercion etc
  etc
  etc

Local Identity Coercion quux_identity_coercion@{etc etc | etc} etc
  etc
  etc

(* ================================================================ *)
(* Reserved Notation                                                *)
(* ================================================================ *)

Reserved Notation "foo bar baz" etc
  etc
  etc

(* ================================================================ *)
(* Notation                                                         *)
(* ================================================================ *)

Reserved Notation "foo bar baz" etc
  etc
  etc

(* ================================================================ *)
(* Declare Scope                                                    *)
(* ================================================================ *)

Declare Scope FooScope.

(* ================================================================ *)
(* Delimit Scope                                                    *)
(* ================================================================ *)

Delimit Scope FooScope with foo.

(* ================================================================ *)
(* Bind Scope                                                       *)
(* ================================================================ *)

Bind Scope FooScope with Foo.

(* ================================================================ *)
(* Module                                                           *)
(* ================================================================ *)

Module Foo.

(* ================================================================ *)
(* Section                                                          *)
(* ================================================================ *)

Section Foo.

(* ================================================================ *)
(* Code delimiters                                                  *)
(* ================================================================ *)

(** begfrag:foo-bar *)
Definition baz_quux@{etc etc | etc} etc
  etc
  etc
(** endfrag:foo-bar *)

(* End of file *)
