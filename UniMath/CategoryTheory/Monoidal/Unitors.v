Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFromBicategory.


Local Open Scope cat.

Section unitors.

  Context (M : monoidal_precat).
  Let B := prebicat_from_monoidal M.


  Let Mp := monoidal_precat_precat M.
  Let tensor   := monoidal_precat_tensor M.
  Let α        := pr1 (monoidal_precat_associator M).
  Let ρ        := pr1 (monoidal_precat_right_unitor M).
  Let l        := pr1 (monoidal_precat_left_unitor M).
  Let i        := monoidal_precat_unit M.

  (* Lemmas about the monoidal structure *)
  Notation "X ⊗ Y" := (tensor (X, Y)).
  Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

  Lemma left_unitor_tensored_is_left_unitor_of_tensor :
    ∏ (a : Mp), (id i #⊗ l a) = l (i ⊗ a).
  Proof.
    intro a.
    apply (Isos.post_comp_with_iso_is_inj _ _ _ _ (pr2 (monoidal_precat_left_unitor M) a) _ _ _).
    exact (pr2 l _ _ _).
  Defined.

  Lemma right_unitor_tensored_is_right_unitor_of_tensor :
    ∏ (a : Mp), (ρ a #⊗ id i) = ρ (a ⊗ i).
  Proof.
    intro a.
    apply (Isos.post_comp_with_iso_is_inj _ _ _ _ (pr2 (monoidal_precat_right_unitor M) a) _ _ _).
    exact (pr2 ρ _ _ _).
  Defined.

  Lemma rtensor_id_inj
    : ∏ (a b : Mp) (f g : a --> b),  (f #⊗ (identity i)) = (g #⊗ (identity i)) -> (f = g).
  Proof.
    intros a b f g.
    intros H.
    apply (Isos.pre_comp_with_iso_is_inj _ _ _ _ _ (pr2 (monoidal_precat_right_unitor M) a) _ _).
    etrans.
    - apply (!(pr2 ρ a b f)).
    - etrans.
      + apply (maponpaths (fun f => f · ρ b) H).
      + etrans.
        * apply (pr2 ρ a b g).
        * apply idpath.
  Defined.

  Lemma ltensor_id_inj
    : ∏ (a b : Mp) (f g : a --> b),  ((identity i) #⊗ f) = ((identity i) #⊗ g) -> (f = g).
  Proof.
    intros a b f g.
    intros H.
    apply (Isos.pre_comp_with_iso_is_inj _ _ _ _ _ (pr2 (monoidal_precat_left_unitor M) a) _ _).
    etrans.
    - apply (!(pr2 l a b f)).
    - etrans.
      + apply (maponpaths (fun f => f · l b) H).
      + etrans.
        * apply (pr2 l a b g).
        * apply idpath.
  Defined.

  Lemma right_unitor_triangle :
    ∏ (a : Mp), α ((a,i),i) · (id a #⊗ ρ i) = ρ (a ⊗ i).
  Proof.
  Admitted.

  Lemma double_right_unitor :
    ∏ (a : Mp) , α ((a , i) , i) · (id a #⊗ (ρ i)) = (ρ (a ⊗ i)).
  Proof.
    intro a.
  Admitted.

  Lemma unitors_coincide_in_unit :
    ρ i = l i.
  Proof.
    apply (lunitor_runitor_identity ).
  Admitted.

End unitors.
