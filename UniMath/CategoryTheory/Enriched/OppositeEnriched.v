(** * The opposite enriched category *)

(** ** Contents

  - Definition
 *)

(** ** References

       - https://ncatlab.org/nlab/show/opposite+category#in_enriched_category_theory

*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.BraidedMonoidalPrecategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.Enriched.Enriched.

Local Open Scope cat.

Section OppositeEnrichedPrecategory.

  Context {V : braided_monoidal_precat}.
  Let pV       := monoidal_precat_precat V.
  Let γ        := braided_monoidal_precat_braiding V.
  Let I        := monoidal_precat_unit V.
  Let tensor   := monoidal_precat_tensor V.
  Let α        := monoidal_precat_associator V.
  Let l_unitor := monoidal_precat_left_unitor V.
  Let r_unitor := monoidal_precat_right_unitor V.

  Context (C : enriched_precat_data V).

  Notation "X ⊗ Y"  := (tensor (X , Y)) : enriched.
  Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31) : enriched.
  Local Open Scope enriched.

  (** The braided structure is needed in the definition of composition. We construct it as
        C(z,y) ⊗ C(y,x) -> C(y,x) ⊗ C(z,y) -> C(z,x). *)
  Definition opposite_enriched_precat_data : enriched_precat_data V.
  Proof.
    use (mk_enriched_precat_data V).
    * exact (enriched_cat_ob V C).
    * intros a b. exact (enriched_cat_mor V b a).
    * intro a. exact (enriched_cat_id V a).
    * intros x y z. simpl.
      exact ((pr1 γ (enriched_cat_mor V z y , enriched_cat_mor V y x)) · (enriched_cat_comp V z y x)).
  Defined.

  (** We check the identity axioms for the enriched category. *)
  (* First identity axiom. *)
  Lemma opposite_enriched_id_ax_holds : enriched_id_ax V opposite_enriched_precat_data.
  Proof.
    unfold enriched_id_ax.
    intros a b. simpl. split.
    * symmetry.
      Check (!(units_commute_with_braiding V (enriched_cat_mor V a b))).
  Admitted.

  Lemma opposite_enriched_assoc_ax_holds : enriched_assoc_ax V opposite_enriched_precat_data.
  Proof.
    unfold enriched_assoc_ax.
    intros a b. simpl.
  Admitted.

  Definition opposite_enriched_precat : enriched_precat V.
  Proof.
    use mk_enriched_precat.
    * exact opposite_enriched_precat_data.
    * apply opposite_enriched_id_ax_holds.
    * apply opposite_enriched_assoc_ax_holds.
  Defined.

End OppositeEnrichedPrecategory.
