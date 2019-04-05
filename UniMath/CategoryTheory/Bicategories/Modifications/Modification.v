(** Modifications between pseudo transformations. *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
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
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.

Local Open Scope cat.

Definition modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           (σ τ : pstrans F G)
  : UU
  := prebicat_cells (psfunctor_bicat B B') σ τ.

Definition modcomponent_of
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
  : ∏ (X : B), σ X ==> τ X
  := pr111 m.

Coercion modcomponent_of : modification >-> Funclass.

Definition modnaturality_of
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
  : ∏ (X Y : B) (f : X --> Y),
    psnaturality_of σ f • (m Y ▻ #F f)
    =
    #G f ◅ m X • psnaturality_of τ f
  := pr211 m.

Definition mk_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : ∏ (X : B), σ X ==> τ X)
           (Hm : ∏ (X Y : B) (f : X --> Y),
                 psnaturality_of σ f • (m Y ▻ #F f)
                 =
                 #G f ◅ m X • psnaturality_of τ f)
  : modification σ τ
  := (((m ,, Hm) ,, (tt ,, tt ,, tt)),, tt).

Definition modification_eq
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           {m m' : modification σ τ}
           (p : ∏ (X : B), m X = m' X)
  : m = m'.
Proof.
  use subtypeEquality.
  { intro. simpl.
    exact isapropunit.
  }
  use subtypeEquality.
  { intro. simpl.
    repeat (apply isapropdirprod) ; apply isapropunit.
  }
  use subtypeEquality.
  { intro. simpl.
    repeat (apply impred ; intro).
    apply B'.
  }
  use funextsec.
  exact p.
Qed.

Definition isaset_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           (σ τ : pstrans F G)
  : isaset (modification σ τ).
Proof.
  repeat (apply isaset_total2).
  - apply impred_isaset ; intro.
    apply B'.
  - intro.
    repeat (apply impred_isaset ; intro).
    apply isasetaprop.
    apply B'.
  - intro ; simpl.
    repeat (apply isaset_dirprod) ; apply isasetunit.
  - intro ; apply isasetunit.
Qed.

Definition is_invertible_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
  : UU
  := @is_invertible_2cell (psfunctor_bicat B B') _ _ _ _ m.

Definition invertible_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           (σ τ : pstrans F G)
  : UU
  := @invertible_2cell (psfunctor_bicat B B') _ _ σ τ.

Definition modcomponent_eq
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           {m m' : modification σ τ}
           (p : m = m')
  : ∏ (X : B), m X = m' X.
Proof.
  intro X.
  induction p.
  apply idpath.
Qed.

Definition is_invertible_modcomponent_of
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
           (Hm : is_invertible_modification m)
  : ∏ (X : B), is_invertible_2cell (m X).
Proof.
  intro X.
  use mk_is_invertible_2cell.
  - exact ((Hm^-1 : modification _ _) X).
  - exact (modcomponent_eq (vcomp_rinv Hm) X).
  - exact (modcomponent_eq (vcomp_lid Hm) X).
Defined.

Definition mk_is_invertible_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : modification σ τ)
           (Hm : ∏ (X : B), is_invertible_2cell (m X))
  : is_invertible_modification m.
Proof.
  use mk_is_invertible_2cell.
  - use mk_modification.
    + exact (λ X, (Hm X)^-1).
    + intros.
      simpl.
      use vcomp_move_R_Mp.
      { is_iso. }
      simpl.
      rewrite <- vassocr.
      use vcomp_move_L_pM.
      { is_iso. }
      symmetry.
      simpl.
      apply (modnaturality_of m).
  - use modification_eq.
    intro X.
    cbn.
    exact (vcomp_rinv (Hm X)).
  - use modification_eq.
    intro X.
    cbn.
    exact (vcomp_lid (Hm X)).
Defined.

Definition invertible_modcomponent_of
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : invertible_modification σ τ)
  : ∏ (X : B), invertible_2cell (σ X) (τ X).
Proof.
  intro X.
  use mk_invertible_2cell.
  - exact ((cell_from_invertible_2cell m : modification _ _) X).
  - apply is_invertible_modcomponent_of.
    exact (property_from_invertible_2cell m).
Defined.

Definition mk_invertible_modification
           {B B' : bicat}
           {F G : psfunctor B B'}
           {σ τ : pstrans F G}
           (m : ∏ (X : B), invertible_2cell (σ X) (τ X))
           (Hm : ∏ (X Y : B) (f : X --> Y),
                 psnaturality_of σ f • (m Y ▻ #F f)
                 =
                 #G f ◅ m X • psnaturality_of τ f)
  : invertible_modification σ τ.
Proof.
  use mk_invertible_2cell.
  - use mk_modification.
    + apply m.
    + exact Hm.
  - apply mk_is_invertible_modification.
    intro.
    apply m.
Defined.