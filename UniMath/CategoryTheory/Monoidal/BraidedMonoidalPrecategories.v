(**
   Braided monoidal precategories.

   Based on an implementation by Anthony Bordg.
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Local Open Scope cat.

Section Braiding.

(** In this section, fix a monoidal category. *)
Context (Mon_V : monoidal_precat).
Let V        := monoidal_precat_precat Mon_V.
Let I        := monoidal_precat_unit Mon_V.
Let tensor   := monoidal_precat_tensor Mon_V.
Let α        := monoidal_precat_associator Mon_V.
Let l_unitor := monoidal_precat_left_unitor Mon_V.
Let r_unitor := monoidal_precat_right_unitor Mon_V.

Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

(* This could be defined at the end of PrecatgeoryBinProduct.v *)
Definition swap_functor {C D : precategory} :
  functor (precategory_binproduct C D) (precategory_binproduct D C) :=
  pair_functor (pr2_functor C D) (pr1_functor C D) □ bindelta_functor (precategory_binproduct C D).

(* A braiding is a natural isomorphism from (- ⊗ =) to (= ⊗ -). *)
Definition swappedtensor : (V ⊠ V) ⟶ V := tensor □ swap_functor.
Definition braiding : UU := nat_iso tensor swappedtensor.

(* Hexagon equations. *)
Section HexagonEquations.

Context (braid : braiding).
Let γ := pr1 braid.
Let α₁ := pr1 α.
Let α₂ := pr1 (nat_iso_inv α).

Definition first_hexagon_eq : UU :=
  ∏ (a b c : V) ,
  (α₁ ((a , b) , c)) · (γ (a , (b ⊗ c))) · (α₁ ((b , c) , a))  =
  (γ (a , b) #⊗ (identity c)) · (α₁ ((b , a) , c)) · ((identity b) #⊗ γ (a , c)).

Definition second_hexagon_eq : UU :=
  ∏ (a b c : V) ,
  α₂ ((a , b) , c) · (γ (a ⊗ b , c)) · α₂ ((c , a) , b)  =
  ((identity a) #⊗ γ (b , c)) · α₂ ((a , c) , b) · (γ (a , c) #⊗ (identity b)).

End HexagonEquations.

End Braiding.

Definition braided_monoidal_precat : UU :=
  ∑ M : monoidal_precat ,
  ∑ γ : braiding M ,
  (first_hexagon_eq M γ) × (second_hexagon_eq M γ).

Section Braided_Monoidal_Precat_Acessors.

Context (M : braided_monoidal_precat).

Definition braided_monoidal_precat_monoidal_precat := pr1 M.

End Braided_Monoidal_Precat_Acessors.
