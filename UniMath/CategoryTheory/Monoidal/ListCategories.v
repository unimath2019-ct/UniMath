Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.Combinatorics.Lists.

Local Open Scope cat.

(** This is essentially a lifting of the free monoid monad from Set to Cat, but
    we unwind everything into elementary terms.*)

Section ListPrecategory.

  Variable (C : precategory).

  Definition list_precategory_obj_mor (n : nat) : precategory_ob_mor.
  Proof.
    induction n as [|n Cn].
    - exists unit. intros.
      exact unit.
    - exists (ob C × ob Cn).
      intros xs ys.
      exact (C⟦pr1 xs, pr1 ys⟧ × Cn⟦pr2 xs, pr2 ys⟧).
  Defined.

  Definition list_precategory_id_comp (n : nat)
    : precategory_id_comp (list_precategory_obj_mor n).
  Proof.
    induction n as [| n Cn].
    - apply dirprodpair.
      + intros ; exact tt.
      + intros ; exact tt.
    - apply dirprodpair.
      + intro xs ; exact (@identity C (pr1 xs) ,, (pr1 Cn) (pr2 xs)).
      + intros xs ys zs fs gs ;
        exact (compose (pr1 fs) (pr1 gs) ,, (pr2 Cn) _ _ _ (pr2 fs) (pr2 gs)).
  Defined.

  Definition list_precategory_data (n : nat) :=
    (list_precategory_obj_mor n ,, list_precategory_id_comp n).

  Definition is_precategory_list_precategory (n : nat)
    : is_precategory (list_precategory_data n).
  Proof.
    induction n as [|n isprecatCn].
    - apply mk_is_precategory ; cbn ; intros ; apply iscontrpathsinunit.
    - pose (isprecatC := pr2 C).
      unfold is_precategory.
      apply mk_is_precategory ; simpl ; intros ; apply dirprodeq.
      + apply (pr1 (pr1 isprecatC)).
      + apply (pr1 (pr1 isprecatCn)).
      + apply (pr2 (pr1 isprecatC)).
      + apply (pr2 (pr1 isprecatCn)).
      + apply (pr1 (pr2 isprecatC)).
      + apply (pr1 (pr2 isprecatCn)).
      + apply (pr2 (pr2 isprecatC)).
      + apply (pr2 (pr2 isprecatCn)).
  Defined.

  Definition list_precategory (n : nat) : precategory :=
    mk_precategory (list_precategory_data n) (is_precategory_list_precategory n).

End ListPrecategory.

Section ListCategory.

  Variable (C : category).

  Definition list_precategory_has_homsets (n : nat) : has_homsets (list_precategory_obj_mor C n).
  Proof.
    unfold has_homsets.
    induction n as [| n has_homsets_Cn]; simpl ; intros.
    - apply isasetunit.
    - apply isaset_dirprod.
      + apply (homset_property C).
      + apply has_homsets_Cn.
  Defined.

  Definition list_category (n : nat) : category :=
    (list_precategory C n ,, list_precategory_has_homsets n).

End ListCategory.

Section UnivalentListCategory.

  (* To prove things about idtoiso we factor the two relevant cases.

     For n=0, a=b --> iso a b
                \     ^
                 |   /
                 v  |
                 unit

     For S n, la = lb -------------> iso la lb
                 |                       ^
                 |                       |
                 v                       |
           a = b × as = bs --> (iso a b) × (iso as bs)

    and then we show that the long composites are equivalences, and that these
   diagrams commute, so that the arrows of interest are equivalences.
   *)

  Variable (C : univalent_category).

  Section factor_zero.
    Definition unit_to_iso (x y : list_category C 0) : unit -> iso x y.
    Proof.
      intro.
      exists tt.
      Search is_iso.
      use is_iso_qinv.
      - exact tt.
      - apply dirprodpair ; cbn.
        + apply idpath.
        + apply idpath.
    Defined.

    Definition unit_to_iso_isequiv (x y : list_category C 0) : isweq (unit_to_iso x y).
    Proof.
      unfold isweq.
      intros.
      use tpair.
      - unfold hfiber.
        exists tt.
        apply (subtypeEquality (isaprop_is_iso x y)).
        cbn. apply isapropunit.
      - simpl.
        intro.
        use subtypeEquality.
        { Search isaset iso.
          intro.
          apply isaset_iso.
          apply (list_precategory_has_homsets C 0).
        } simpl. apply isapropunit.
    Defined.

    Definition unit_to_iso_weq (x y : list_category C 0) : unit ≃ iso x y.
    Proof.
      use weqpair.
      - exact (unit_to_iso x y).
      - exact (unit_to_iso_isequiv x y).
    Defined.

    Definition uniteq_to_unit (a b : unit) : a = b -> unit := fun _ => tt.

    Definition uniteq_to_unit_is_weq (a b : unit) : isweq (uniteq_to_unit a b).
    Proof.
      use isweqcontrcontr.
      - apply iscontrpathsinunit.
      - apply iscontrunit.
    Defined.

    Definition uniteq_to_unit_weq (a b : unit) := weqpair _ (uniteq_to_unit_is_weq a b).

    Definition zero_idtoiso_isweq (x y : list_category C 0) : isweq (@idtoiso _ x y).
    Proof.
      use weqhomot.
      - exact (unit_to_iso_weq x y ∘ uniteq_to_unit_weq x y)%weq.
      - intro p.
        induction p.
        apply (subtypeEquality (isaprop_is_iso x x)).
        cbn. apply idpath.
    Defined.

  End factor_zero.

  Section factor_successor.

    Definition prod_iso_to_iso_list (n : nat) (lx ly : list_category C (S n)) :
      (iso (pr1 lx) (pr1 ly))×(@iso (list_category C n) (pr2 lx) (pr2 ly))
      -> iso lx ly.
    Proof.
      intro ip.


    Definition successor_idtoiso_isweq (n : nat) (lx ly : list_category C (S n))
    : isweq (@idtoiso _ lx ly).
    Proof.
      use weqhomot.
      -
      Check (@weqcomp (lx = ly) ((pr1 lx = pr1 ly)×(pr2 lx = pr2 ly))
                      ((iso (pr1 lx) (pr1 ly))×
                                              (@iso (list_category C n) (pr2 lx) (pr2 ly)))).


    Check dirprod_paths.


        Check ().

  Definition list_category_is_univalent (n : nat) : is_univalent (list_category C n).
  Proof.
    unfold is_univalent.
    apply dirprodpair.
    - induction n.
      + apply unit_idtoiso_isweq.
      +
    - apply list_precategory_has_homsets.
