

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.EquivToAdjequiv.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Presheaves.
Require Import UniMath.CategoryTheory.catiso.

Local Open Scope bicategory_scope.
Local Open Scope cat.


Definition univ_hom
           {C : bicat}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
           (X Y : C)
  : univalent_category.
Proof.
  use mk_category.
  - exact (hom X Y).
  - split.
    + apply idtoiso_weq.
      exact C_is_univalent_2_1.
    + exact (pr2 C X Y).
Defined.

Definition inv_of_invertible_2cell
           {C : bicat}
           {X Y : C}
           {f g : X --> Y}
  : invertible_2cell f g → invertible_2cell g f.
Proof.
  intro α.
  use mk_invertible_2cell.
  - exact (α^-1).
  - is_iso.
Defined.

Definition comp_of_invertible_2cell
           {C : bicat}
           {X Y : C}
           {f g h : X --> Y}
  : invertible_2cell f g → invertible_2cell g h → invertible_2cell f h.
Proof.
  intros α β.
  use mk_invertible_2cell.
  - exact (α • β).
  - is_iso.
    + apply α.
    + apply β.
Defined.

Definition inv_adjoint_equivalence
           {C : bicat}
           {X Y : C}
  : adjoint_equivalence X Y → adjoint_equivalence Y X.
Proof.
  intro f.
  use equiv_to_adjequiv.
  - exact (left_adjoint_right_adjoint f).
  - simpl.
    use tpair.
    + repeat (use tpair).
      * exact f.
      * exact ((left_equivalence_counit_iso f)^-1).
      * exact ((left_equivalence_unit_iso f)^-1).
    + split ; cbn ; is_iso.
Defined.

Definition isweq_isinj
           {A B : UU}
           {f : A → B}
           (Hf : isweq f)
  : ∏ {x y : A}, f x = f y → x = y.
Proof.
  intros x y p.
  refine (!_ @ maponpaths (invmap (_ ,, Hf)) p @ _).
  - apply homotinvweqweq.
  - apply homotinvweqweq.
Defined.

Section Initial.

  Context {C : bicat}.
  Variable (C_is_univalent_2_1 : is_univalent_2_1 C).

  Definition is_biinitial (X : C) : UU
    := ∏ (Y : C),
       @left_adjoint_equivalence
         bicat_of_cats
         _ _
         (functor_to_unit (univ_hom C_is_univalent_2_1 X Y)).


  Definition BiInitial : UU := ∑ (X : C), is_biinitial X.

  Definition has_biinitial : hProp := ∥ BiInitial ∥.

  Definition isaprop_is_biinitial (X : C) : isaprop (is_biinitial X).
  Proof.
    use impred.
    intros Y.
    apply isaprop_left_adjoint_equivalence.
    exact univalent_cat_is_univalent_2_1.
  Qed.

  Definition biinitial_1cell_property (X : C) : UU
    := ∏ (Y : C), X --> Y.

  Definition biinitial_1cell
             {X : C}
             (HX : is_biinitial X)
    : biinitial_1cell_property X
    := λ Y, (left_adjoint_right_adjoint (HX Y) : functor _ _) tt.

  Definition biinitial_2cell_property
             (X Y : C)
    : UU
    := ∏ (f g : X --> Y), invertible_2cell f g.

  Definition biinitial_2cell
             {X : C}
             (HX : is_biinitial X)
             {Y : C}
    : biinitial_2cell_property X Y.
  Proof.
    intros f g.
    pose (L := functor_to_unit (univ_hom C_is_univalent_2_1 X Y)).
    pose (R := (left_adjoint_right_adjoint (HX Y) : functor _ _)).
    pose (θ₁ := iso_to_inv2cell
                  _ _
                  (CompositesAndInverses.nat_iso_to_pointwise_iso
                     (invertible_2cell_to_nat_iso
                        _ _
                        (left_equivalence_unit_iso (HX Y)))
                     f)).
    pose (θ₃ := iso_to_inv2cell
                  _ _
                  (CompositesAndInverses.nat_iso_to_pointwise_iso
                     (invertible_2cell_to_nat_iso
                        _ _
                        (inv_of_invertible_2cell
                           (left_equivalence_unit_iso (HX Y))))
                     g)).
    pose (θ₂ := iso_to_inv2cell
                  _ _
                  (functor_on_iso R (idtoiso (idpath _ : L f = L g)))).
    exact (comp_of_invertible_2cell θ₁ (comp_of_invertible_2cell θ₂ θ₃)).
  Defined.

  Definition biinitial_eq_property (X Y : C) : UU
    := ∏ (f g : X --> Y) (α β : f ==> g), α = β.

  Definition biinitial_eq
             {X : C}
             (HX : is_biinitial X)
             {Y : C}
    : biinitial_eq_property X Y.
  Proof.
    intros f g α β.
    pose (L := functor_to_unit (univ_hom C_is_univalent_2_1 X Y)).
    pose (R := (left_adjoint_right_adjoint (HX Y) : functor _ _)).
    assert (#R(#L α) = #R(#L β)) as p.
    {
      reflexivity.
    }
    pose (pr1 (left_adjoint_equivalence_to_is_catiso _ (HX Y))) as HL.
    pose (pr1 (left_adjoint_equivalence_to_is_catiso
                 _
                 (@inv_adjoint_equivalence bicat_of_cats _ _ (_ ,, HX Y))))
      as HR.
    exact (isweq_isinj (HL _ _) (isweq_isinj (HR _ _) p)).
  Qed.

  Definition is_biinitial'
             (X : C)
    := (biinitial_1cell_property X)
         × ∏ (Y : C), (biinitial_2cell_property X Y)
                        ×
                        biinitial_eq_property X Y.

  Definition is_biinitial_to_is_biinitial'
             (X : C)
    : is_biinitial X → is_biinitial' X.
  Proof.
    intros HX.
    repeat split.
    - exact (biinitial_1cell HX).
    - exact (biinitial_2cell HX).
    - exact (biinitial_eq HX).
  Defined.

  Definition biinitial_inv_d
             {X : C}
             (HX : is_biinitial' X)
    : ∏ (Y : C),
      functor_data
        unit_category
        (univ_hom C_is_univalent_2_1 X Y).
  Proof.
    intros Y.
    use mk_functor_data.
    - intro.
      exact (pr1 HX Y).
    - intros ; simpl.
      exact (id₂ _).
  Defined.

  Definition biinitial_inv_is_functor
             {X : C}
             (HX : is_biinitial' X)
    : ∏ (Y : C),
      is_functor (biinitial_inv_d HX Y).
  Proof.
    intros Y.
    split ; simpl.
    - intro.
      reflexivity.
    - intros ? ? ? ? ?.
      cbn.
      rewrite id2_left.
      reflexivity.
  Qed.

  Definition biinitial_inv
             {X : C}
             (HX : is_biinitial' X)
    : ∏ (Y : C),
      unit_category ⟶ univ_hom C_is_univalent_2_1 X Y.
  Proof.
    intros Y.
    use mk_functor.
    - exact (biinitial_inv_d HX Y).
    - exact (biinitial_inv_is_functor HX Y).
  Defined.

  Definition biinitial_inv_unit_d
             {X : C}
             (HX : is_biinitial' X)
             (Y : C)
    : nat_trans_data
        (functor_identity (hom X Y))
        (functor_composite
           (functor_to_unit (hom X Y))
           (biinitial_inv HX Y)).
  Proof.
    intros f.
    simpl.
    exact (pr1 (pr2 HX Y) f (pr1 HX Y)).
  Defined.

  Definition biinitial_inv_unit_is_nat_trans
             {X : C}
             (HX : is_biinitial' X)
             (Y : C)
    : is_nat_trans _ _ (biinitial_inv_unit_d HX Y).
  Proof.
    intros f g α.
    simpl in * ; cbn.
    rewrite id2_right.
    apply (pr2 (pr2 HX Y)).
  Qed.

  Definition biinitial_inv_unit
             {X : C}
             (HX : is_biinitial' X)
             (Y : C)
    : (functor_identity (hom X Y))
        ⟹
        functor_composite
        (functor_to_unit (hom X Y))
        (biinitial_inv HX Y).
  Proof.
    use mk_nat_trans.
    - exact (biinitial_inv_unit_d HX Y).
    - exact (biinitial_inv_unit_is_nat_trans HX Y).
  Defined.

  Definition biinitial_inv_counit_d
             {X : C}
             (HX : is_biinitial' X)
             (Y : C)
    : nat_trans_data
        (functor_composite
           (biinitial_inv HX Y)
           (functor_to_unit (hom X Y)))
        (functor_identity _).
  Proof.
    intros f.
    apply isapropunit.
  Defined.

  Definition biinitial_inv_counit_is_nat_trans
             {X : C}
             (HX : is_biinitial' X)
             (Y : C)
    : is_nat_trans _ _ (biinitial_inv_counit_d HX Y).
  Proof.
    intros f g α.
    apply isasetunit.
  Qed.

  Definition biinitial_inv_counit
             {X : C}
             (HX : is_biinitial' X)
             (Y : C)
    : (functor_composite
         (biinitial_inv HX Y)
         (functor_to_unit (hom X Y)))
        ⟹
        (functor_identity _).
  Proof.
    use mk_nat_trans.
    - exact (biinitial_inv_counit_d HX Y).
    - exact (biinitial_inv_counit_is_nat_trans HX Y).
  Defined.

  Definition is_biinitial'_to_is_biinitial
             (X : C)
    : is_biinitial' X → is_biinitial X.
  Proof.
    intros HX Y.
    use equiv_to_adjequiv.
    use tpair.
    - use tpair.
      + exact (biinitial_inv HX Y).
      + split.
        * exact (biinitial_inv_unit HX Y).
        * exact (biinitial_inv_counit HX Y).
    - split.
      + apply is_nat_iso_to_is_invertible_2cell.
        intro g.
        cbn in * ; unfold biinitial_inv_unit_d.
        apply inv2cell_to_iso.
      + apply is_nat_iso_to_is_invertible_2cell.
        intro g.
        cbn.
        apply path_univalent_groupoid.
  Defined.

  Definition isaprop_is_biinitial'
             (X : C)
    : isaprop (is_biinitial' X).
  Proof.
    apply invproofirrelevance.
    intros x y.
    induction x as [f x].
    induction y as [g y].
    apply pathsdirprod.
    -
End Initial.