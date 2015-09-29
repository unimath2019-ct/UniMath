(** * Definition of non-negative rational numbers *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.RationalNumbers.

Opaque hq.

Open Scope hq_scope.

(** ** Non-negative rational numbers *)

Definition hnnq_def := total2 (hqleh 0).

Definition hnnq_def_to_hq (r : hnnq_def) : hq := pr1 r.
Coercion hnnq_def_to_hq : hnnq_def >-> pr1hSet.
Definition hq_to_hnnq_def (r : hq) (Hr : hqleh 0 r) : hnnq_def :=
  tpair (fun x : hq => hqleh 0 x) r Hr.

Lemma isincl_hnnq_to_hq : isincl hnnq_def_to_hq. 
Proof. 
  apply (isinclpr1 (fun x : hq => hqleh 0 x) (fun x : hq => isapropneg (hqgth 0 x))).
Qed.
Definition hnnq_set : hSet := 
  hSetpair _ (isasetsubset hnnq_def_to_hq isasethq isincl_hnnq_to_hq).

(** ** Equality and order on [ hnnq ] *)

(** *** Equality *)

Definition hnnq_eq ( x y : hnnq_set) : hProp := 
  hqeq (pr1 x) (pr1 y).
Lemma isdecrel_hnnq_eq : isdecrel hnnq_eq.
Proof.
  intros (r1,H1) (r2,H2).
  apply isdecrelhqeq.
Qed.
Definition hnnq_deceq : decrel hnnq_def :=
  tpair _ hnnq_eq isdecrel_hnnq_eq.

Definition hnnq_booleq := decreltobrel hnnq_deceq.

Definition hnnq_neq ( x y : hnnq_def ) : hProp := hProppair ( neg (hnnq_eq  x y ) ) ( isapropneg _  )  .
Definition isdecrel_hnnq_neq : isdecrel hnnq_neq  := isdecnegrel _ isdecrel_hnnq_eq . 
Definition hnnq_decneq : decrel hnnq_def := decrelpair isdecrel_hnnq_neq . 

Definition hnnq_boolneq := decreltobrel hnnq_decneq .

(** *** Order *)

Definition hnnq_le (x y : hnnq_set) : hProp := hqleh (pr1 x) (pr1 y).
Definition hnnq_ge (x y : hnnq_set) : hProp := hqgeh (pr1 x) (pr1 y).
Definition hnnq_lt (x y : hnnq_set) : hProp := hqlth (pr1 x) (pr1 y).
Definition hnnq_gt (x y : hnnq_set) : hProp := hqgth (pr1 x) (pr1 y).

(** ** [hnnq] is an abelian monoid *)

Lemma hq0lehandplus:
  forall n m : hq,
    hqleh 0 n -> hqleh 0 m -> hqleh 0 (n + m).
Proof.
  intros n m Hn Hm.
  eapply istranshqleh, hqlehandplusl, Hm.
  now rewrite hqplusr0.
Qed.
Definition hnnq_plus_def (x y : hnnq_set) : hnnq_set :=
  hq_to_hnnq_def ((pr1 x) + (pr1 y)) (hq0lehandplus (pr1 x) (pr1 y) (pr2 x) (pr2 y)).

Definition hnnq_setwithbinop : setwithbinop :=
  tpair _ hnnq_set hnnq_plus_def.

Lemma isassoc_hnnq_plus_def : isassoc hnnq_plus_def.
Proof.
  intros x y z.
  apply total2_paths_isaprop.
  intro.
  now destruct (hqleh 0 a).
  apply (hqplusassoc (pr1 x) (pr1 y) (pr1 z)).
Qed.

Definition hnnq_0 : hnnq_set :=
  hq_to_hnnq_def 0 (isreflhqleh 0).
Lemma islunit_hnnq_plus_def_hnnq_0 :
  islunit hnnq_plus_def hnnq_0.
Proof.
  intros x.
  apply total2_paths_isaprop.
  intro.
  now destruct (hqleh 0 a).
  apply (hqplusl0 (pr1 x)).
Qed.
Lemma isrunit_hnnq_plus_def_hnnq_0 :
  isrunit hnnq_plus_def hnnq_0.
Proof.
  intros x.
  apply total2_paths_isaprop.
  intro.
  now destruct (hqleh 0 a).
  apply (hqplusr0 (pr1 x)).
Qed.

Lemma iscomm_hnnq_plus_def : iscomm hnnq_plus_def.
Proof.
  intros x y.
  apply total2_paths_isaprop.
  intro.
  now destruct (hqleh 0 a).
  now apply (hqpluscomm (pr1 x) (pr1 y)).
Qed.

Definition hnnq_abmonoid : abmonoid.
Proof.
  exists hnnq_setwithbinop.
  simpl.
  split.
  split.
  exact isassoc_hnnq_plus_def.
  exists hnnq_0.
  split.
  exact islunit_hnnq_plus_def_hnnq_0.
  exact isrunit_hnnq_plus_def_hnnq_0.
  exact iscomm_hnnq_plus_def.
Defined.

Close Scope hq_scope.

(** * Notations and remarks *)

Notation hnnq := hnnq_abmonoid.

Bind Scope hnnq_scope with hnnq.

(** [hnnq] is an ordered set *)

Notation "x <= y" := (hnnq_le x y) : hnnq_scope.
Notation "x < y" := (hnnq_lt x y) : hnnq_scope.
Notation "x >= y" := (hnnq_ge x y) : hnnq_scope.
Notation "x > y" := (hnnq_gt x y) : hnnq_scope.

(** [hnnq] is an abelian monoid *)

Notation "0" := (unel hnnq_abmonoid) : hnnq_scope.
Notation "x + y" := (@op hnnq_abmonoid x y) : hnnqscope.

Delimit Scope hnnq_scope with hnnq.

(* End of the file hnnq.v *)