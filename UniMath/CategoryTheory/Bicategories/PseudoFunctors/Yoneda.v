
(** * Yoneda. *)

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

Local Open Scope bicategory_scope.
Local Open Scope cat.

Section Yoneda.

Context {C : bicat}.
Variable (C_is_univalent_2_1 : is_univalent_2_1 C).

Definition y_data : psfunctor_data C (psfunctor_bicat (op1_bicat C) bicat_of_cats).
Proof.
  use mk_psfunctor_data.
  - apply representable.
    apply C_is_univalent_2_1.
  - intros X Y f.
    Opaque psfunctor_bicat.
    cbn.

Definition y : psfunctor C (psfunctor_bicat (op1_bicat C) bicat_of_cats).
Proof.
  use mk_psfunctor.
  -
