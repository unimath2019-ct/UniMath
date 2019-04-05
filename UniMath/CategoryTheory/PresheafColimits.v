Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.CategoryTheory.Elements.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.categories.Cats.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Local Open Scope cat.

Section canonical_colimit.

Context {C : category} (X : PreShv C).

Definition cat_of_elems_ps : precategory :=
  (@cat_of_elems C^op X)^op.

Definition assembly_functor : cat_of_elems_ps ⟶ PreShv C.
Proof.
  assert (forget : cat_of_elems_ps ⟶ C).
  exact (functor_opp (@cat_of_elems_forgetful C^op X)).
  exact (forget ∙ (yoneda (pr1 C) (pr2 C))).
Defined.

Definition elements_graph : graph :=
  graph_from_precategory cat_of_elems_ps.

Definition assembly_diagram : diagram elements_graph (PreShv C) :=
  @diagram_from_functor cat_of_elems_ps (PreShv C) assembly_functor.

Definition coconeX : cocone assembly_diagram X.
Proof.
  use mk_cocone.
  - unfold elements_graph; unfold assembly_diagram; unfold diagram_from_functor; unfold assembly_functor;cbn.
    intros v; induction v as [c x];cbn.
    apply yoneda_map_2.
    exact x.
  - cbn.
    intros u v e; induction u as [c x]; induction v as [c' x']; induction e as [f H]; cbn in *.
    rewrite <- H.
    Check nat_trans_comp.
    Print is_nat_trans.
    Print yoneda_iso_target.
    set (natcond := (is_natural_yoneda_iso_inv (pr1 C) (pr2 C) X)).
    unfold is_nat_trans in natcond.
    set (natcondf := eqtohomot (natcond c' c f)).
    unfold yoneda_iso_target, homot in natcondf; cbn in natcondf.
    apply pathsinv0.
    exact (natcondf x').
Defined.

Proposition canonical_assembly : isColimCocone assembly_diagram X coconeX.
Proof.
  unfold isColimCocone.
  unfold elements_graph, coconeX; cbn.
  intros Y ccY.
  induction ccY as [ccY ccYcommutes].
  unfold cocone, assembly_diagram in ccY.
  unfold assembly_functor, cat_of_elems_ps, cat_of_elems_ob_mor in ccY; cbn in ccY.
  use unique_exists.
  - use mk_nat_trans.
    + assert (mapXY : ∏ c : C, (X : functor _ _) c --> Y c  ).
      { intros c x.
        set (ccYx := ccY (c,,x)); cbn in ccYx.
        apply (yoneda_map_1 (pr1 C) (pr2 C)).
        exact ccYx.
      }
      exact mapXY.
    + cbn.
      unfold is_nat_trans.
      intros c c' f; cbn.
      apply funextfun.
      intros x.
      set (ccYcommutesf := ccYcommutes (c',,# (X : functor _ _) f x) (c,,x) (f,,idpath (# (X : functor _ _) f x))); cbn in ccYcommutesf.
      rewrite <- ccYcommutesf; cbn.
      unfold yoneda_morphisms_data.
      rewrite id_left.
      Check yoneda_map_1_2.
      set (H := yoneda_map_1_2 (pr1 C) (pr2 C) c Y (ccY (c,,x))).
      etrans.
      Check maponpaths.
      set (HH := maponpaths pr1 H).
      set (Hfunc' := eqtohomot HH c').
      set (Hfunc'f := eqtohomot Hfunc' f).
      exact (!Hfunc'f).
      cbn.
      reflexivity.
  - cbn.
    intros v; induction v as [c x]; cbn.
    apply nat_trans_eq.
    + exact has_homsets_HSET.
    + intros c'; cbn.
      Check (ccY (c,, x)) c'.
      apply funextfun.
      unfold yoneda_objects_ob.
      intros f.
      set (ccYcommutesf := ccYcommutes (c',,# (X : functor _ _) f x) (c,,x) (f,,idpath (# (X : functor _ _) f x))); cbn in ccYcommutesf.
      apply pathsinv0.
      etrans.
      exact (maponpaths ((ccY (c,, x)) c') (!id_left f)).
      unfold yoneda_map_1.
      set (H := maponpaths pr1 ccYcommutesf).
      exact (eqtohomot (eqtohomot (maponpaths pr1 ccYcommutesf) c') (identity c')).
  - intros F.
    cbn.
    apply impred_isaprop.
    intros t; induction t as [c x]; cbn.
    apply isaset_nat_trans.
    exact has_homsets_HSET.
  - cbn.
    intros F H; cbn.
    apply nat_trans_eq.
    + exact has_homsets_HSET.
    + intros c; cbn.
      apply funextfun; intros x.
      set (Hcx := maponpaths pr1 (H (c,,x))); cbn in Hcx.
      set (Hcxc := eqtohomot Hcx c).
      unfold yoneda_objects in Hcxc; unfold yoneda_objects_ob in Hcxc.
      set (Hcxcid := eqtohomot Hcxc (identity c)); cbn in Hcxcid.
      unfold yoneda_map_1.
      assert (idpf : # (X : functor _ _) (identity c) x = x).
      { set (Xfun := pr2 X).
        unfold is_functor in Xfun.
        unfold functor_idax in Xfun.
        set (Xfunid := (pr1 Xfun c)).
        assert (unfolder : # (X : functor _ _) (identity c) = # (pr1 X) (identity c)).
        { reflexivity. }
        rewrite unfolder.
        apply (eqtohomot Xfunid x).
      }
      etrans.
      exact (maponpaths (F c) (!idpf)).
      exact Hcxcid.
Qed.



End canonical_colimit.

Definition elemsfrompresheaf_functor {C : precategory} : PreShv C ⟶ precat_precat.
Proof.
  use mk_functor.
  - use tpair.
    + intros X.
      apply (@cat_of_elems C^op).
      exact X.
    + cbn.
      intros X Y F.
      induction F as [F Fnat].
      unfold nat_trans_data in F.
      use mk_functor.
      -- use tpair.
         ++ unfold cat_of_elems_data; cbn.
            intros x.
            induction x as [c x].
            use tpair.
            --- exact c.
            --- cbn.
                unfold hset_precategory_data in F; cbn in F.
                exact (F c x).
         ++ cbn.
            intros a b f.
            induction a as [c x]; induction b as [c' x']; induction f as [f fxx'];cbn in *.
            use tpair.
            --- exact f.
            --- cbn.
                unfold is_nat_trans in Fnat; unfold opp_precat_data in Fnat; cbn in Fnat.
                set (Fnatf := eqtohomot (Fnat c c' f) x); cbn in Fnatf.
                etrans.
                exact (!Fnatf).
                exact (maponpaths (F c') fxx').
      -- cbn.
         use tpair.
         ++ unfold functor_idax; cbn.
            intros a; induction a as [c x]; cbn.
            use subtypeEquality.
            --- intros f.
                Check F c x.
                Check Y c.
                Print hset_precategory_data.
                Print hset_precategory_ob_mor.
                Print hSet.
                assert (Ycset : isaset (pr1 (Y c))).
                { exact (pr2 (Y c)). }
                unfold isaset in Ycset.
                apply Ycset.
            --- cbn.
                reflexivity.
         ++ cbn.
            unfold functor_compax; cbn.
            intros a1 a2 a3.
            induction a1 as [c x]; induction a2 as [c' x']; induction a3 as [c'' x'']; cbn.
            intros ff gg; induction ff as [f feq]; induction gg as [g geq]; cbn.
            use subtypeEquality.
            --- intros gf.
                assert (Yc''set : isaset (pr1 (Y c''))).
                { exact (pr2 (Y c'')). }
                unfold isaset in Yc''set.
                apply Yc''set.
            --- cbn.
                reflexivity.
  - unfold is_functor.
    use tpair.
    + unfold functor_idax.
      intros X; cbn.
      use subtypeEquality.
      -- unfold isPredicate.
         intros F.
         unfold is_functor.
         Search (isaprop _ × _).
         unfold isaprop.
         unfold isofhlevel.
         is_functor.