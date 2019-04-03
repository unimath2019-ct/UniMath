Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Section listyoga.

  Definition sumlist : list nat -> nat := foldr add 0.

  Definition flatten {A : UU} : list (list A) -> list A := foldr concatenate nil.

End listyoga.


Local Open Scope cat.
Local Open Scope stn.

Section unit_category_is_unit.

  Variable (C : precategory).

  Definition lunit_functor : functor (precategory_binproduct unit_category C) C.
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (dirprod_pr2).
      + intros a b f. exact (dirprod_pr2 f).
    - apply dirprodpair.
      + intro a. apply idpath.
      + intros a b c f g. apply idpath.
  Defined.

  Definition lunit_inv_functor : functor C (precategory_binproduct unit_category C).
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (dirprodpair tt).
      + intros a b. apply dirprodpair. apply idpath.
    - apply dirprodpair.
      + intro a. apply dirprod_paths ; apply idpath.
      + intros a b c f g. apply dirprod_paths ; apply idpath.
  Defined.

  Definition runit_functor : functor (precategory_binproduct C unit_category) C.
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (dirprod_pr1).
      + intros a b f. exact (dirprod_pr1 f).
    - apply dirprodpair.
      + intro a. apply idpath.
      + intros a b c f g. apply idpath.
  Defined.

  Definition runit_inv_functor : functor C (precategory_binproduct C unit_category).
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (fun o => dirprodpair o tt).
      + intros a b f. apply dirprodpair. exact f. apply idpath.
    - apply dirprodpair.
      + intro a. apply dirprod_paths ; apply idpath.
      + intros a b c f g. apply dirprod_paths ; apply idpath.
  Defined.

End unit_category_is_unit.

Section ListPrecategory.

  Variable (C : precategory).

  Definition list_precategory (n : nat) : precategory.
  Proof.
    induction n as [|n Cn].
    - exact unit_category.
    - exact (precategory_binproduct C Cn).
  Defined.

  Definition horizontal_domain : list nat -> precategory.
  Proof.
    Check list_ind.
    use (@list_ind nat (fun _ => precategory)).
    - exact unit_category.
    - intros k ks partial_product.
      exact (precategory_binproduct (list_precategory k) partial_product).
  Defined.

  Definition flattened_domain_functor (l : list nat) :
    functor (horizontal_domain l) (list_precategory (sumlist l)).
  Proof.
    use (list_ind (fun l => functor (horizontal_domain l)
                                 (list_precategory (sumlist l)))).
    - exact (functor_identity unit_category).
    - intros k ks suffix_functor.
      induction k.
      + exact (lunit_functor _ ∙ suffix_functor).
      + refine (functor_composite _ _).
        exact (precategory_binproduct_unassoc
                 C (list_precategory k) (horizontal_domain ks)).
        exact (pair_functor (functor_identity C) IHk).
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

Section ListReassociation.



Section UnbiasedMoniodalPrecat.

  (** An unbiased (lax) monoidal category is a category C equipped with maps:

      tensor_n : C^n -> C

      for each natural n, as well as natural transformations

      γ : tensor_k ∘ (tensor_n1 , ... , tensor_nk) -> tensor_(∑ n_i)
      ι : id_C -> tensor_1

      for each k ∈ ℕ, and n_1, ..., n_k ∈ ℕ, subject to the following.
   *)

  Context {C : precategory} (tensor : ∏ n, list_precategory C n ⟶ C) .

  Definition horizontal_tensor (l : list nat) :
    functor (horizontal_domain C l) (list_precategory C (length l)).
  Proof.
    use (list_ind (fun l => (functor (horizontal_domain C l) (list_precategory C (length l))))).
    - exact (functor_identity unit_category).
    - intros k ks functor.
      exact (pair_functor (tensor k) functor).
  Defined.

  Definition gammator (l : list nat) : UU
    := nat_trans ((horizontal_tensor l) ∙ (tensor (length l)))
                 ((flattened_domain_functor C l) ∙ tensor (sumlist l)).

  Definition iotator : UU
    := nat_trans ((runit_inv_functor C) ∙ tensor 1) (functor_identity _).

  Definition double_list_to_domain1 : list (list nat) -> precategory.
  Proof.
    use (@list_ind (list nat) (fun _ => precategory)).
    - exact unit_category.
    - intros l ls IHls.
      exact (precategory_binproduct (horizontal_domain C l) IHls).
  Defined.

  Definition double_list_to_domain2 : (list (list nat)) -> precategory.
  Proof.



  Definition gamma_law : UU :=
    ∏ (lll : list (list (list nat))) .
