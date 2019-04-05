
(** Action on morphisms of representables **)

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
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Presheaves.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Section Representable1.

Context {C : bicat}{X Y : C}.
Variable (C_is_univalent_2_1 : is_univalent_2_1 C) (f : X --> Y).

Definition representable1_data :
  pstrans_data (representable C_is_univalent_2_1 X) (representable C_is_univalent_2_1 Y).
Proof.
  use mk_pstrans_data.
  - intro Z.
    cbn.
    use mk_functor.
    + use mk_functor_data.
      -- intro g.
         exact (g · f).
      -- intros g h η.
         exact (rwhisker f η).
    + split.
      -- intro g.
         apply id2_rwhisker.
      -- intros g h k η φ.
         symmetry.
         apply rwhisker_vcomp.
  - intros Z W h.
    cbn.
    use mk_invertible_2cell.
    + use mk_nat_trans.
      -- intro k.
         apply lassociator.
      -- intros k l η.
         cbn in *.
         apply rwhisker_lwhisker.
    + use is_nat_iso_to_is_invertible_2cell.
      intro g.
      apply is_inv2cell_to_is_iso.
      simpl.
      is_iso.
Defined.

Definition representable1_is_pstrans : is_pstrans representable1_data.
Proof.
  repeat (apply tpair).
  - intros Z W g h η.
    use nat_trans_eq.
    { exact (pr2 C W Y). }
    intro k.
    simpl.
    symmetry.
    apply rwhisker_rwhisker.
  - intro Z.
    use nat_trans_eq.
    { exact (pr2 C Z Y). }
    intro h.
    cbn in *.
    rewrite !id2_left.
    rewrite linvunitor_assoc.
    rewrite <- vassocr.
    rewrite rassociator_lassociator.
    apply id2_right.
  - intros Z W V g h.
    use nat_trans_eq.
    { exact (pr2 C V Y). }
    intro k.
    cbn in *.
    rewrite id2_left , ! id2_right.
    symmetry.
    apply lassociator_lassociator.
Qed.

Definition representable1 :
  pstrans (representable C_is_univalent_2_1 X) (representable C_is_univalent_2_1 Y).
Proof.
  use mk_pstrans.
  - exact representable1_data.
  - exact representable1_is_pstrans.
Defined.

End Representable1.

Section Representable2.

Context {C : bicat}{X Y : C}{f g : X --> Y}.
Variable (C_is_univalent_2_1 : is_univalent_2_1 C) (η : f ==> g).

Definition representable2_data
  : modification_data (representable1 C_is_univalent_2_1 f)
                      (representable1 C_is_univalent_2_1 g).
Proof.
  intro Z.
  use mk_nat_trans.
  - intro h.
    simpl.
    exact (h ◃ η).
  - intros h k φ.
    simpl.
    apply vcomp_whisker.
Defined.

Definition representable2_is_modification
  : is_modification (σ := representable1 C_is_univalent_2_1 f) representable2_data.
Proof.
  intros Z W h.
  use nat_trans_eq.
  { exact (pr2 C W Y). }
  intro k.
  cbn in *.
  symmetry.
  apply lwhisker_lwhisker.
Qed.

Definition representable2 :
  modification (representable1 C_is_univalent_2_1 f) (representable1 C_is_univalent_2_1 g).
Proof.
  use mk_modification.
  - apply representable2_data.
  - apply representable2_is_modification.
Defined.

End Representable2.