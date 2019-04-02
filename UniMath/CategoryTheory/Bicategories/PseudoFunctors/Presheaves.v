
(** * Presheaves. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OpMorBicat.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.

Local Open Scope bicategory_scope.
Local Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Presheaves                                                                      *)
(* ----------------------------------------------------------------------------------- *)

Section Representable.

Variable (C : bicat) (C_is_univalent_2_1 : is_univalent_2_1 C).

Definition pspsh := psfunctor (op1_bicat C) bicat_of_cats.

Definition inv2cell_to_iso {a b : C} (f g : hom a b) : invertible_2cell f g → iso f g.
Proof.
  intro i.
  destruct i as [η ηinv].
  destruct ηinv as [φ eqs].
  destruct eqs as [eq1 eq2].
  use mk_iso.
  - exact η.
  - intro h.
    use isweq_iso.
    + intro ψ.
      exact (φ • ψ).
    + intro ψ.
      simpl.
      unfold precomp_with.
      refine ((_@_)@_).
      * apply vassocr.
      * exact (maponpaths (λ x, x • ψ) eq2).
      * apply id2_left.
    + intro ψ.
      simpl.
      unfold precomp_with.
      refine ((_@_)@_).
      * apply vassocr.
      * exact (maponpaths (λ x, x • ψ) eq1).
      * apply id2_left.
Defined.

Definition iso_to_inv2cell {a b : C} (f g : hom a b) : iso f g → invertible_2cell f g.
Proof.
  intro i.
  use tpair.
    + exact (morphism_from_iso i).
    + use mk_is_invertible_2cell.
      * exact (inv_from_iso i).
      * exact (iso_inv_after_iso i).
      * exact (iso_after_iso_inv i).
Defined.

Definition inv2cell_to_iso_isweq {a b : C} (f g : hom a b) : isweq (inv2cell_to_iso f g).
Proof.
  use isweq_iso.
  - exact (iso_to_inv2cell f g).
  - intro i.
    apply cell_from_invertible_2cell_eq.
    apply idpath.
  - intro i.
    apply eq_iso.
    apply idpath.
Defined.

Definition inv2cell_to_iso_weq {a b : C} (f g : hom a b) : invertible_2cell f g ≃ iso f g.
Proof.
  use weqpair.
  - exact (inv2cell_to_iso f g).
  - exact (inv2cell_to_iso_isweq f g).
Defined.

Definition idtoiso_alt_weq {a b : C} (f g : hom a b) : f = g ≃ iso f g.
Proof.
  refine (inv2cell_to_iso_weq f g ∘ _)%weq.
  use weqpair.
  - exact (idtoiso_2_1 f g).
  - apply C_is_univalent_2_1.
Defined.

Definition idtoiso_weq {a b : C} (f g : hom a b) : isweq (λ p : f = g, idtoiso p).
Proof.
  use weqhomot.
  + exact (idtoiso_alt_weq f g).
  + intro p.
    apply eq_iso.
    induction p.
    apply idpath.
Defined.

Definition representable_data_cat (X Y : C) : univalent_category.
Proof.
  use mk_category.
  + exact (hom Y X).
  + split.
    exact idtoiso_weq.
    exact (pr2 C Y X).
Defined.

Definition representable_data_fun (X Y Z : C) (f : op1_bicat C ⟦ Y, Z ⟧)
  : bicat_of_cats ⟦ representable_data_cat X Y, representable_data_cat X Z ⟧.
Proof.
  simpl in f.
  use mk_functor.
  - use mk_functor_data.
    + intro g.
      exact (f · g).
    + intros g h.
      exact (lwhisker f).
  - split.
    + exact (lwhisker_id2 f).
    + intros g h k η φ.
      exact (! (lwhisker_vcomp f η φ)).
Defined.

Definition representable_data_nat (X Y Z : C) (f g : op1_bicat C ⟦ Y, Z ⟧)
  : f ==> g → representable_data_fun X Y Z f ==> representable_data_fun X Y Z g.
Proof.
  intro η.
  use mk_nat_trans.
  - intro h.
    exact (rwhisker h η).
  - intros h k φ.
    exact (! (@vcomp_whisker C Z Y X f g h k η φ)).
Defined.

Definition representable_data (X : C) : psfunctor_data (op1_bicat C) bicat_of_cats.
Proof.
  use mk_psfunctor_data.
  - exact (representable_data_cat X).
  - exact (representable_data_fun X).
  - exact (representable_data_nat X).
  - intro Y.
    use mk_nat_trans.
    + exact linvunitor.
    + abstract (intros f g η ;
                simpl in * ;
                rewrite lwhisker_hcomp ;
                apply linvunitor_natural).
  - intros Y Z W f g.
    use mk_nat_trans.
    + intro h. simpl.
      cbn in *.
      apply lassociator.
    + intros h k η.
      simpl.
      apply lwhisker_lwhisker.
Defined.

Definition representable_laws (X : C) : psfunctor_laws (representable_data X).
Proof.
  repeat split; cbn.
  - intros Y Z f.
    use nat_trans_eq.
    + exact (pr2 C Z X).
    + intro g. cbn.
      apply id2_rwhisker.
  - intros Y Z f g h η φ.
    use nat_trans_eq.
    + exact (pr2 C Z X).
    + intro k. cbn.
      symmetry.
      apply rwhisker_vcomp.
  - intros Y Z f.
    use nat_trans_eq.
    + exact (pr2 C Z X).
    + intro g. cbn.
      rewrite <- vassocr.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      symmetry.
      apply lwhisker_id2.
  - intros Y Z f.
    use nat_trans_eq.
    + exact (pr2 C Z X).
    + intro g. cbn.
      rewrite linvunitor_assoc.
      refine (!(_@ _)).
      {
        apply maponpaths_2.
        rewrite <- vassocr.
        rewrite rassociator_lassociator.
        apply id2_right.
      }
      rewrite rwhisker_vcomp.
      rewrite linvunitor_lunitor.
      apply id2_rwhisker.
  - intros Y Z W V f g h.
    use nat_trans_eq.
    + exact (pr2 C V X).
    + intro k.
      cbn in *.
      rewrite id2_left.
      pose (pentagon_2 k f g h) as p.
      rewrite lwhisker_hcomp,rwhisker_hcomp.
      rewrite <- vassocr.
      exact (! p).
  - intros Y Z W f g h η.
    use nat_trans_eq.
    + exact (pr2 C W X).
    + intro k.
      cbn in *.
      apply rwhisker_rwhisker.
  - intros Y Z W f g h η.
    use nat_trans_eq.
    + exact (pr2 C W X).
    + intro k.
      cbn in *.
      symmetry.
      apply rwhisker_lwhisker.
Qed.

Definition representable (X : C) : pspsh.
Proof.
  use mk_psfunctor.
  - exact (representable_data X).
  - exact (representable_laws X).
  - split.
    + simpl.

    Definition is_univalent_2_1_lem : ∏ (X Y : C) (f g : C⟦a,b⟧), isweq (idtoiso_2_1 f g).