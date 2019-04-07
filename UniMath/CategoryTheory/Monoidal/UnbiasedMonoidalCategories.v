Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Combinatorics.Lists.

(** * Ye have been warned, everything is made from right-associated products. *)


Local Open Scope list.

Section listyoga.

  Definition sum_list : list nat -> nat := foldr add 0.

  Definition isdecnillist {A : UU} (xs : list A) : decidable (xs = []).
  Proof.
    unfold decidable.
    induction (isdeceqnat (pr1 xs) 0) as [zerlen | poslen].
    - apply ii1.
      replace 0 with (pr1 (@nil A)) in zerlen by reflexivity.
      apply (total2_paths_f zerlen).
      apply isapropunit.
    - apply ii2.
      intro bad.
      apply poslen.
      exact (maponpaths pr1 bad).
  Defined.

End listyoga.


Local Open Scope cat.

Local Notation "C × D" := (precategory_binproduct C D)
                            (at level 75, right associativity).
Local Notation "F #× G" := (pair_functor F G)
                             (at level 75, right associativity).

Section unit_category_is_unit_for_prod.

  Variable (C : precategory).

  Definition lunit_functor : (unit_category × C) ⟶ C.
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (dirprod_pr2).
      + intros a b f. exact (dirprod_pr2 f).
    - apply dirprodpair.
      + intro a. apply idpath.
      + intros a b c f g. apply idpath.
  Defined.

  Definition lunit_inv_functor : C ⟶ (unit_category × C).
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (dirprodpair tt).
      + intros a b. apply dirprodpair. apply idpath.
    - apply dirprodpair.
      + intro a. apply dirprod_paths ; apply idpath.
      + intros a b c f g. apply dirprod_paths ; apply idpath.
  Defined.

  Definition runit_functor : (C × unit_category) ⟶ C.
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (dirprod_pr1).
      + intros a b f. exact (dirprod_pr1 f).
    - apply dirprodpair.
      + intro a. apply idpath.
      + intros a b c f g. apply idpath.
  Defined.

  Definition runit_inv_functor : C ⟶ (C × unit_category).
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + exact (fun o => dirprodpair o tt).
      + intros a b f. apply dirprodpair. exact f. apply idpath.
    - apply dirprodpair.
      + intro a. apply dirprod_paths ; apply idpath.
      + intros a b c f g. apply dirprod_paths ; apply idpath.
  Defined.

End unit_category_is_unit_for_prod.

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
    - exact (C × IHn).
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

  (** ** TODO: Where does this go?  *)
  (** This constructs, for [ l: list nat ], the functor

      C^l(0) x (C^l(1) ... ( C^l(last) )) --> C^(length l)

      by taking tensors on each listed power.
   *)

Section tensor_constructions.

  Context {C : precategory} (tensor : ∏ n, list_precategory C n ⟶ C) .

  Local Notation "⊗ n" := (tensor n) (at level 30).

  (** This constructs (C^l(0)) x .. x (C^l(last)), the horizontal_domain. *)
  Definition h_dom : ∏ (l : list nat), precategory.
  Proof.
    use list_ind.
    - exact unit_category.
    - intros k ks partial_product.
      exact ((list_precategory C k) × partial_product).
  Defined.

  (** This is the horizontal product of n-ary functors,
      (C^l(0)) x .. x (C^l(last))
          |               |
    nfun  |    x .. x     | nfun
          v               v
          C x    ..     x C
   *)
  Definition h_prod_fun (nfun : (∏ (n : nat), list_precategory C n ⟶ C)) :
    ∏ (l : list nat), h_dom l ⟶ list_precategory C (length l).
  Proof.
    use list_ind.
    - exact (functor_identity unit_category).
    - intros k ks functor.
      Check tensor.
      exact (nfun _ #× functor).
  Defined.

  (** and the specialisation of h_prod_fun to ⊗. *)
  Definition h_ten := h_prod_fun tensor.

  (** Given [l : list nat ], this constructs the cannonical functor

      C^l(0) x (C^l(1) x .. (C^l(last))) --> C^(sum_list l)

   *)
  Definition h_dom_flatten_functor : ∏ (l : list nat),
                               h_dom l ⟶ list_precategory C (sum_list l).
  Proof.
    use list_ind.
    - exact (functor_identity unit_category).
    - intros k ks suffix_functor.
      induction k.
      + exact (lunit_functor _ ∙ suffix_functor).
      + refine (functor_composite _ _).
        exact (precategory_binproduct_unassoc
                 C (list_precategory C k) (h_dom ks)).
        exact (functor_identity _ #× IHk).
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
      exact (h_dom l × IHls).
  Defined.


  (** Given [ ll : list (list nat) ], this constructs the cannonical functor

      (C^(ll(1,1)) x .. x C^(ll(1,last))) x .. x (C^(ll(last,1)) x .. x C^(ll(last,last)))

                                            |
                                            |
                                            v

                   C^(ll(1,1)) x .. x C^(ll(1,last)) x .. x C^(ll(last,last))
   *)

  Definition hh_dom_flatten_functor : ∏ (ll : list (list nat)),
                                     hh_dom ll ⟶ h_dom (foldr concatenate [] ll).
  Proof.
    use list_ind.
    - cbn -[hh_dom h_dom]. apply functor_identity.
    - intros l lls IHll ; simpl in IHll ; revert l.
      use list_ind ; cbn -[hh_dom h_dom foldr].
      + replace (hh_dom ([] :: lls))
          with (unit_category × hh_dom lls)
          by reflexivity.
        replace (foldr concatenate [] ([] :: lls))
          with (foldr concatenate [] lls) by reflexivity.
        exact (lunit_functor _ ∙ IHll).
      + intros n ls IHl.
        replace (foldr concatenate [] ((n :: ls) :: lls)) with
            (n ::  (foldr concatenate [] (ls :: lls))) by reflexivity.
        replace (h_dom (n :: foldr concatenate [] (ls :: lls))) with
            (list_precategory C n × h_dom (foldr concatenate [] (ls :: lls)))
          by reflexivity.
        replace (hh_dom ((n :: ls) :: lls)) with
            (h_dom (n :: ls) × hh_dom lls) by reflexivity.
        replace (h_dom (n :: ls))
          with (list_precategory C n × h_dom ls)
          by reflexivity.
        apply (functor_composite (precategory_binproduct_unassoc _ _ _)).
        replace (h_dom ls × hh_dom lls) with (hh_dom (ls :: lls))
          by reflexivity.
        exact (functor_identity _ #× IHl).
  Defined.

  (** This is supporting code for h_prod_fun below.  *)
  Definition functor_layer1 :=
    ∑ (l : list nat), h_dom l ⟶ list_precategory C (length l).

  Definition functor_layer2 :=
    ∑ (ll : list (list nat)),
    hh_dom ll ⟶ h_dom (map length ll).

  Definition functor_layer3 := ∑ (ll : list (list nat)),
                               hh_dom ll ⟶ list_precategory C (length ll).

  Definition to_listfun :
    (∏ (l : list nat), h_dom l ⟶ list_precategory C (length l))
      -> list (list nat) → list functor_layer1.
  Proof.
    intro funfam.
    apply map.
    intro l.
    exact (l ,, funfam _).
  Defined.

  Definition prod_of_listfun : list functor_layer1 -> functor_layer2.
  Proof.
    apply foldr.
    - intros lF llG.
      exists ((pr1 lF) :: (pr1 llG)).
      exact (pr2 lF #× pr2 llG).
    - exact (nil ,, functor_identity _).
  Defined.

  Definition prod_of_listfun_correct_domain
             (funfam : (∏ (l : list nat), h_dom l ⟶ list_precategory C (length l))) :
    ∏ (ll : list (list nat)), pr1 (prod_of_listfun (to_listfun funfam ll)) = ll.
  Proof.
    use list_ind.
    - reflexivity.
    - intros l ls IH.
      exact (maponpaths (cons l) IH).
  Defined.

  (** Given [funfam : ∏ (l : list nat), h_dom l ⟶ list_precategory C (length l)]
      and [ll : list (list nat)] this constructs the functor

            (C^(ll(1,1)) x ... x C^(ll(1,last)))
          x ...
          x (C^(ll(last,1)) x ... x C^(ll(last,last)))

                           |
                           | (funfam x .. x funfam) x .. x (funfam x .. x funfam)
                           |
                           v

                     (C x ... x C)
                   x ...
                   x (C x ... x C)


   *)

  Definition hh_prod_fun (ll : list (list nat))
    (funfam : (∏ (l : list nat), h_dom l ⟶ list_precategory C (length l))) :
    hh_dom ll ⟶ h_dom (map length ll).
  Proof.
    apply (transportf (fun ll => functor (hh_dom ll)
                                      (h_dom (map length ll)))
                      (prod_of_listfun_correct_domain funfam ll)).
    exact (pr2 (prod_of_listfun (to_listfun funfam ll))).
  Defined.

  (** This is a specialisation of hh_prod_fun above to funfam := ⊗. *)
  Definition hh_ten {ll : list (list nat)} := hh_prod_fun ll h_ten.

  Check hh_dom_flatten_functor.

  (** We need to be able to commute flattening and tensoring in several ways. *)

  Variable ll : list (list nat).
  Variable nfun : ∏ (n : nat), list_precategory C n ⟶ C.

  Check (hh_dom_flatten_functor ll ∙ h_prod_fun nfun (foldr concatenate [] ll)).
  Check (hh_prod_fun ll (h_prod_fun nfun) ∙ h_prod_fun _ _).
  Check h_prod_fun.

  Definition something : ∏ (ll : list (list nat)),
    list_precategory C (length (map length ll)) ⟶
    list_precategory C (length (foldr concatenate [] ll)).
  Proof.
    use list_ind.
    - apply functor_identity.
    - intros l ll func ; simpl in func.
      revert l.
      use list_ind ;      cbn -[list_precategory length map foldr].
      + replace (cons nil ll) with (ll).
        * admit.
        * revert




  Definition hh_dom_commute (nfun : ∏ (n : nat), list_precategory C n ⟶ C)
             (ll : list (list nat)) :
    hh_dom_flatten_functor ll ∙ h_prod_fun nfun (foldr concatenate [] ll) =
    hh_prod_fun ll (h_prod_fun nfun) ∙ h_prod_fun (h_dom_flatten_functor) _.


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

        (** In the established notation, given [ ll: list (list nat) ] this section
        constructsn

        C^(sum k_(1,i)) x ( ... x C^(sum k_(n,i)))

        as well as the functor (below) with this as domain and codomain C.

        x_(sum mi) (x_k11) ... (x_k1j1) ... (x_kn1) ... (x_knjn)

     *)

  Definition double_list_to_domain4 (ll : list (list nat)) : precategory
    := horizontal_domain C (map sum_list ll).

  Definition tensor3 {ll : list (list nat)} : double_list_to_domain4 ll ⟶ C
    := h_ten _ ∙ ⊗ _ .

    (** Given [ ll: list (list nat) ] this section constructs the ⊗ functor


                            x_(sum sum (k_ij))
        C^(sum sum k_(i,j)) -------------------> C
     *)

  Definition double_list_to_domain5 (ll : list (list nat)) : precategory
    := list_precategory C (sum_list (map sum_list ll)).

  Definition tensor4 {ll : list (list nat)} : double_list_to_domain5 ll ⟶ C
    := ⊗ _.


End tensor_constructions.

Section unbiased_monoidal_precategory.

    (** An unbiased (lax) monoidal category is a category C equipped with maps:

      ⊗_n : C^n -> C

      for each natural n, as well as natural transformations

      γ : ⊗_k ∘ (⊗_n1 , ... , ⊗_nk) -> ⊗_(∑ n_i)
      ι : id_C -> ⊗_1

      for each k ∈ ℕ, and n_1, ..., n_k ∈ ℕ, subject to the following.
   *)

  Definition gammator (l : list nat) : UU
    := nat_trans ((h_ten _) ∙ (⊗ (length l)))
                 ((h_dom_flatten_functor _ _) ∙ ⊗ (sum_list l)).

  Definition iotator : UU
    := nat_trans ((runit_inv_functor C) ∙ ⊗ 1) (functor_identity _).


  Section first_pasting.

      (** Our starting point in the definition of unbiased monoidal categories is
      the thrice-iterated tensor, denfined below. Its shape is:

         ⊗_n (⊗_m1 (⊗_k11) ... (⊗_k1j1) )
             (⊗_m2 (⊗_k21 ) ...(⊗_k2j2) ) ...
             (⊗_mn (⊗_kn1) ... (⊗_knjn) )
  *)



  Definition ten_ten_ten {ll : list (list nat)} : hh_dom ll ⟶ C
    := hh_ten ∙ h_ten _ ∙ ⊗ _.


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
      tensor1 ⟹ pre_tensor1 ∙ h_dom_flatten_functor _ (map length ll) ∙ ⊗ _
      := pre_whisker pre_tensor1.

    Check @pre_tensor1 ll.
    Check pre_tensor1 ∙ flatten_functor _ _.

    Definition second_whisker1 : gammator (map length ll) ->
                                 pre_tensor1 ∙ flatten_functor _ (map length ll) ∙ tensor2 ⟹ pre_tensor1 ∙
                                             flatten_functor _ _ ∙
                                             flatten_functor _ _ ∙ tensor3.
  End first_pasting.
End ListReassociation.
End
