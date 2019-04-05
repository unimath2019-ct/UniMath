Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

(*** Ye have been warned, everything is made from right-associated products. *)

Section listyoga.

  Definition sumlist : list nat -> nat := foldr add 0.

  Definition flattenlist {A : UU} : list (list A) -> list A := foldr concatenate nil.

End listyoga.


Local Open Scope cat.
Local Open Scope list.

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

  (** Given [C : precategory] and [l : list nat] this constructs

      C^l(0) x (C^l(1) x .. (C^l(last)))

      Note the association, and each power is right-associated too.

   *)

  Variable C : precategory.

  Definition list_precategory (n : nat) : precategory.
  Proof.
    induction n.
    - exact unit_category.
    - exact (precategory_binproduct C IHn).
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

      ⊗_n : C^n -> C

      for each natural n, as well as natural transformations

      γ : ⊗_k ∘ (⊗_n1 , ... , ⊗_nk) -> ⊗_(∑ n_i)
      ι : id_C -> ⊗_1

      for each k ∈ ℕ, and n_1, ..., n_k ∈ ℕ, subject to the following.
   *)

  Context {C : precategory} (tensor : ∏ n, list_precategory C n ⟶ C) .

  Local Notation "⊗ n" := (tensor n) (at level 30).

  (** This constructs (C^l(0)) x .. x (C^l(last))  *)
  Definition h_dom : ∏ (l : list nat), precategory.
  Proof.
    use list_ind.
    - exact unit_category.
    - intros k ks partial_product.
      exact (precategory_binproduct (list_precategory C k) partial_product).
  Defined.

  (** This is the horizontal product of tensor functors,
      (C^l(0)) x .. x (C^l(last))
          |               |
          | ⊗  x .. x   ⊗ |
          v               v
          C x    ..     x C
   *)
  Definition h_ten : ∏ (l : list nat),
    h_dom l ⟶ list_precategory C (length l).
  Proof.
    use list_ind.
    - exact (functor_identity unit_category).
    - intros k ks functor.
      exact (pair_functor (⊗ k) functor).
  Defined.

  (** Given [l : list nat ], this constructs the cannonical functor from

      C^l(0) x (C^l(1) x .. (C^l(last))) --> C^(sumlist l)

   *)
  Definition flatten_functor : ∏ (l : list nat),
      h_dom l ⟶ list_precategory C (sumlist l).
  Proof.
    use list_ind.
    - exact (functor_identity unit_category).
    - intros k ks suffix_functor.
      induction k.
      + exact (lunit_functor _ ∙ suffix_functor).
      + refine (functor_composite _ _).
        exact (precategory_binproduct_unassoc
                 C (list_precategory C k) (h_dom ks)).
        exact (pair_functor (functor_identity C) IHk).
  Defined.

  (** Here we construct

                       (C^(k_(1,1)) x ... x C^(k_(1,j_1)))    -
                                                               |
                     x ...                                     | n
                                                               |
                     x (C^(k_(n,1)) x ... x C^(k_(n,j_n)))    -

                        |______________________________|
                                       j_n

      from [ ll : list (list nat) ] where        n = length ll,
                                             j_i = length ll[i]
                                         k_(i,m) = ll[i][m]

    This is the horizontal, horizontal domain.
   *)

    Definition hh_dom : ∏ (ll : list (list nat)), precategory.
    Proof.
      use list_ind.
      - exact unit_category.
      - intros l ls IHls.
        exact (precategory_binproduct (h_dom l) IHls).
    Defined.

    Definition functor_layer1 :=
      ∑ (l : list nat), h_dom l ⟶ list_precategory C (length l).

    Definition functor_layer2 :=
      ∑ (ll : list (list nat)),
      hh_dom ll ⟶ h_dom (map length ll).

    Definition functor_layer3 := ∑ (ll : list (list nat)),
      hh_dom ll ⟶ list_precategory C (length ll).

    Definition list_of_tensor : list (list nat) → list functor_layer1.
    Proof.
      apply map.
      intro l.
      exact (l ,, h_ten _).
    Defined.

    Definition innermost_tensor : list functor_layer1 -> functor_layer2.
    Proof.
      apply foldr.
      - intros lF llG.
        exists ((pr1 lF) :: (pr1 llG)).
        exact (pair_functor (pr2 lF) (pr2 llG)).
      - exact (nil ,, functor_identity _).
    Defined.

    Definition innermost_tensor_preserves_list_shape : ∏ (ll : list (list nat)),
      pr1 (innermost_tensor (list_of_tensor ll)) = ll.
    Proof.
      use list_ind.
      - reflexivity.
      - intros l ls IH.
        exact (maponpaths (cons l) IH).
    Defined.

    (** This constructs the functor

            (C^(k_(1,1)) x ... x C^(k_(1,j_1)))
          x ...
          x (C^(k_(n,1)) x ... x C^(k_(n,j_n)))

                           |
                           | (⊗ x .. x ⊗) x .. x (⊗ x .. x ⊗)
                           |
                           v

                     (C x ... x C)
                   x ...
                   x (C x ... x C)

     *)
    Definition hh_ten {ll : list (list nat)} :
      hh_dom ll ⟶ h_dom (map length ll).
    Proof.
      apply (transportf (fun ll => functor (hh_dom ll)
                                        (h_dom (map length ll)))
                        (innermost_tensor_preserves_list_shape ll)).
      exact (pr2 (innermost_tensor (list_of_tensor ll))).
    Defined.

  (** This constructs, for [ l: list nat ], the functor

      C^l(0) x (C^l(1) ... ( C^l(last) )) --> C^(length l)

      by taking tensors on each listed power.
   *)


  Definition gammator (l : list nat) : UU
    := nat_trans ((h_ten _) ∙ (⊗ (length l)))
                 ((flatten_functor _ _) ∙ ⊗ (sumlist l)).

  Definition iotator : UU
    := nat_trans ((runit_inv_functor C) ∙ ⊗ 1) (functor_identity _).

  Section first_functor.


    (**
      as well as the functor (below) with this domain and codomain C.

         x_n (x_m1 (x_k11) ... (x_k1j1) )
             (x_m2 (x_k21 ) ...(x_k2j2) ) ...
             (x_mn (x_kn1) ... (x_knjn) )


  *)

    Definition tensor1 {ll : list (list nat)} : double_list_to_domain1 ll ⟶ C
      := pre_tensor1 ∙ h_ten _ ∙ ⊗ _.
  End first_functor.

  Section second_functor.

    (** In the notation of the above comments, given [ ll : list (list nat ) ]
        this section constructs:

        C^(k_(1,1)) x (... x ( C^(k_(1,j_1)) x ( C^(2,1) x ( ... C^(k_(n,j_n))...)

        as well as the functor (below) with this as domain and codomain C.

          x_n (x_(sum xk1i) )
             (x_(sum xk2i) ) ...
             (x_(sum xkni) )
     *)

    Definition double_list_to_domain3 (ll : list (list nat)) : precategory
      := horizontal_domain C (map length ll).

    Definition tensor2 {ll : list (list nat)} : double_list_to_domain3 ll ⟶ C
      := h_ten _ ∙ ⊗ _.

  End second_functor.

  Section third_functor.

    (** In the established notation, given [ ll: list (list nat) ] this section
        constructsn

        C^(sum k_(1,i)) x ( ... x C^(sum k_(n,i)))

        as well as the functor (below) with this as domain and codomain C.

        x_(sum mi) (x_k11) ... (x_k1j1) ... (x_kn1) ... (x_knjn)

     *)

  Definition double_list_to_domain4 (ll : list (list nat)) : precategory
    := horizontal_domain C (map sumlist ll).

  Definition tensor3 {ll : list (list nat)} : double_list_to_domain4 ll ⟶ C
    := h_ten _ ∙ ⊗ _ .

  End third_functor.

  Section fourth_functor.

    (** Given [ ll: list (list nat) ] this section constructs the ⊗ functor


                            x_(sum sum (k_ij))
        C^(sum sum k_(i,j)) -------------------> C
     *)

  Definition double_list_to_domain5 (ll : list (list nat)) : precategory
    := list_precategory C (sumlist (map sumlist ll)).

  Definition tensor4 {ll : list (list nat)} : double_list_to_domain5 ll ⟶ C
    := ⊗ _.

  End fourth_functor.

  Section first_pasting.

    (** In this section we construct the pasting

        This is wrong. We need to be able to commute flatten with products of functors.


             domain1 ======== domain1
                 |              |
    pre_tensor1  |              |  tensor1
                 v   h_ten ∙ ⊗  v
             domain2 ---------> A
                 |             ||
        flatten  |  gammator   ||
                 v             ||
             domain2 -tensor2-> A
                 |             ||
        flatten  |  gammator   ||
                 v             ||
             domain3 ---------> A
                      tensor3
     *)

    Variable (ll : list (list nat)).

    Definition first_whisker1 : gammator (map length ll) ->
      tensor1 ⟹ pre_tensor1 ∙ flatten_functor _ (map length ll) ∙ ⊗ _
      := pre_whisker pre_tensor1.

    Check @pre_tensor1 ll.
    Check pre_tensor1 ∙ flatten_functor _ _.

    Definition second_whisker1 : gammator (map length ll) ->
                                 pre_tensor1 ∙ flatten_functor _ (map length ll) ∙ tensor2 ⟹ pre_tensor1 ∙
                                             flatten_functor _ _ ∙
                                             flatten_functor _ _ ∙ tensor3.
