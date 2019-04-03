Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
(* Require Import UniMath.CategoryTheory.Core.Isos. *)
(* Require Import UniMath.CategoryTheory.Core.NaturalTransformations. *)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Combinatorics.Lists.

Local Open Scope cat.

(** This is essentially a lifting of the free monoid monad from Set to Cat *)

Section ListPrecategory.

  Variable (C : precategory).

  Definition list_precategory (n : nat) : precategory.
  Proof.
    induction n as [|n Cn].
    - exact unit_category.
    - exact (precategory_binproduct C Cn).
  Defined.

End ListPrecategory.

Section UnivalentListCategory.

  Variable (C : univalent_category).

  Definition is_univalent_list_category (n : nat)
    : is_univalent (list_precategory C n).
  Proof.
    induction n.
    - apply unit_category.
    - apply (is_univalent_binproduct C (_ ,, IHn)).
  Defined.

End UnivalentListCategory.
