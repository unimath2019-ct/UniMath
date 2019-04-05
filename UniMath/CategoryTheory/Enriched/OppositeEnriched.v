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
  Let γ        := pr1 (braided_monoidal_precat_braiding V).
  Let I        := monoidal_precat_unit V.
  Let tensor   := monoidal_precat_tensor V.
  Let α        := monoidal_precat_associator V.
  Let l        := pr1 (monoidal_precat_left_unitor V).
  Let ρ        := pr1 (monoidal_precat_right_unitor V).

  Context (C : enriched_precat V).
  Let dC   := pr1 C.
  Let Vhom := enriched_cat_mor (d := dC) V.
  Let Vid  := enriched_cat_id (d := dC) V.
  Let Vcomp  := enriched_cat_comp (d := dC) V.

  Notation "X ⊗ Y"  := (tensor (X , Y)) : enriched.
  Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31) : enriched.
  Local Open Scope enriched.

  (** The braided structure is needed in the definition of composition. We construct it as
        C(z,y) ⊗ C(y,x) -> C(y,x) ⊗ C(z,y) -> C(z,x). *)
  Definition opposite_enriched_precat_data : enriched_precat_data V.
  Proof.
    use (mk_enriched_precat_data V).
    * exact (enriched_cat_ob V C).
    * intros a b. exact (Vhom b a).
    * intro a. exact (enriched_cat_id V a).
    * intros x y z. simpl.
      exact ((pr1 γ (Vhom z y , Vhom y x)) · (Vcomp z y x)).
  Defined.

  (** We check the identity axioms for the enriched category. *)
  Lemma opposite_enriched_id_ax_holds : enriched_id_ax V opposite_enriched_precat_data.
  Proof.
    unfold enriched_id_ax.
    intros b a. simpl in *. split.

    (* First identity axiom. *)
    * apply pathsinv0.
      etrans. { apply (!(units_commute_with_braiding_l _ _)). }
      etrans. { apply (maponpaths (fun f => _ · f) (!(pr2 (pr1 (pr2 C) _ _)))). }
      etrans. { apply (assoc _ _ _). }
      etrans. { apply (maponpaths (fun f => f · _) (!(pr2 γ _ _ (enriched_cat_id V a #, id (Vhom a b))))). }
      etrans. { apply (!(assoc _ _ _)). }
      apply idpath.

    (* Second identity axiom. *)
    * apply pathsinv0.
      etrans. { apply ((!(units_commute_with_braiding_r _ _))). }
      etrans. { apply (maponpaths (fun f => _ · f) (!(pr1 (pr1 (pr2 C) _ _)))). }
      etrans. { apply ((assoc _ _ _)). }
      etrans. { apply (maponpaths (fun f => f · _) (!(pr2 γ _ _ (id (Vhom a b) #, Vid b)))). }
      etrans. { apply (!(assoc _ _ _)). }
      apply idpath.
  Defined.

  Lemma opposite_enriched_assoc_ax_holds : enriched_assoc_ax V opposite_enriched_precat_data.
  Proof.
    unfold enriched_assoc_ax.
    intros a b c d. simpl.
  Admitted.

  Definition opposite_enriched_precat : enriched_precat V.
  Proof.
    use mk_enriched_precat.
    * exact opposite_enriched_precat_data.
    * apply opposite_enriched_id_ax_holds.
    * apply opposite_enriched_assoc_ax_holds.
  Defined.

End OppositeEnrichedPrecategory.
