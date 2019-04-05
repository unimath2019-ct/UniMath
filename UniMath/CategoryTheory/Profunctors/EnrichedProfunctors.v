(** * Enriched Profunctors *)

(* V-enriched profunctors. *)

(** References:
    - https://link.springer.com/content/pdf/10.1007/BFb0060443.pdf
    - https://bartoszmilewski.com/2017/03/29/ends-and-coends/
    - https://arxiv.org/abs/1501.02503
 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.Enriched.Enriched.

Local Open Scope cat.

(** *** E-valued V-enriched profunctors. *)
Section EnrichedProfunctors.
  Context (Mon_V : monoidal_precat).
  Let V        := monoidal_precat_precat Mon_V.
  Let I        := monoidal_precat_unit Mon_V.
  Let tensor   := monoidal_precat_tensor Mon_V.
  Let α        := monoidal_precat_associator Mon_V.
  Let l_unitor := monoidal_precat_left_unitor Mon_V.
  Let r_unitor := monoidal_precat_right_unitor Mon_V.
  Notation "X ⊗ Y"  := (tensor (X , Y)) : enriched.
  Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31) : enriched.
  Local Open Scope enriched.

  Context (E : enriched_precat Mon_V).

  Definition enriched_profunctor (C D : enriched_precat Mon_V) : UU :=
    enriched_functor (precategory_binproduct (opp_precat D) C) E.
End EnrichedProfunctors.
