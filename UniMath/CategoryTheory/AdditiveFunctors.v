(** * Additive functors *)
(** ** Contents
- Definition of additive functors
- Additive functor preserves BinDirectSums
 - Definition of PreservesBinDirectSums
   - Additive funtor preserves zero.
 - Preserves IdIn1, IdIn2, Unit1, Unit2, and Id of BinDirectSum
 - Preserves BinDirectCoproducts
 - Preserves BinDirectProducts
 - Preserves BinDirectSums
- If a functor preserves BinDirectSums, then it is additive
 - Preserves unel
 - Commutes with BinOp
 - isAdditiveFunctor
- The natural additive functor to quotient
- Additive equivalences
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.

Local Open Scope cat.

(** * Definition of additive functor
   Functor is additive if for any two objects a1 a2 of an additive category A, the map on morphisms
   A⟦a1, a2⟧ -> B⟦F a1, F a2⟧ is a morphism of abelian groups. *)
Section def_additivefunctor.

  (** ** isAdditiveFunctor *)

  Definition isAdditiveFunctor {A B : CategoryWithAdditiveStructure} (F : functor A B) : UU :=
    ∏ (a1 a2 : A), @ismonoidfun (to_abgr a1 a2) (to_abgr (F a1) (F a2)) (# F).

  Definition make_isAdditiveFunctor {A B : CategoryWithAdditiveStructure} (F : functor A B)
             (H : ∏ (a1 a2 : A),
                  @ismonoidfun (to_abgr a1 a2) (to_abgr (F a1) (F a2)) (# F)) :
    isAdditiveFunctor F.
  Proof.
    intros a1 a2.
    exact (H a1 a2).
  Qed.

  Definition make_isAdditiveFunctor' {A B : CategoryWithAdditiveStructure} (F : functor A B)
             (H1 : ∏ (a1 a2 : A), (# F (ZeroArrow (to_Zero A) a1 a2)) =
                                  ZeroArrow (to_Zero B) (F a1) (F a2))
             (H2 : ∏ (a1 a2 : A) (f g : A⟦a1, a2⟧), # F (to_binop _ _ f g) =
                                                    to_binop _ _ (# F f) (# F g)) :
    isAdditiveFunctor F.
  Proof.
    use make_isAdditiveFunctor.
    intros a1 a2.
    split.
    - intros f g. apply (H2 a1 a2 f g).
    - set (tmp := PreAdditive_unel_zero A (to_Zero A) a1 a2).
      unfold to_unel in tmp. rewrite tmp. clear tmp.
      set (tmp := PreAdditive_unel_zero B (to_Zero B) (F a1) (F a2)).
      unfold to_unel in tmp. rewrite tmp. clear tmp.
      apply (H1 a1 a2).
  Qed.

  Lemma isaprop_isAdditiveFunctor {A B : CategoryWithAdditiveStructure} (F : functor A B) :
    isaprop (isAdditiveFunctor F).
  Proof.
    apply impred_isaprop. intros t.
    apply impred_isaprop. intros t0.
    apply isapropismonoidfun.
  Qed.

  (** ** Additive functor *)

  Definition AdditiveFunctor (A B : CategoryWithAdditiveStructure) : UU := ∑ F : (functor A B), isAdditiveFunctor F.

  Definition make_AdditiveFunctor {A B : CategoryWithAdditiveStructure} (F : functor A B) (H : isAdditiveFunctor F) :
    AdditiveFunctor A B := tpair _ F H.

  (** Accessor functions *)
  Definition AdditiveFunctor_Functor {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B) :
    functor A B := pr1 F.
  Coercion AdditiveFunctor_Functor : AdditiveFunctor >-> functor.

  Definition AdditiveFunctor_isAdditiveFunctor {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B) :
    isAdditiveFunctor (AdditiveFunctor_Functor F) := pr2 F.

  (** ** Basics of additive functors *)

  Lemma AdditiveFunctorUnel {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B)
        (a1 a2 : A) : # F (to_unel a1 a2) = to_unel (F a1) (F a2).
  Proof.
    unfold to_unel.
    apply (pr2 (pr2 F a1 a2)).
  Qed.

  Lemma AdditiveFunctorZeroArrow {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B)
        (a1 a2 : A) : # F (ZeroArrow (to_Zero A) a1 a2) = ZeroArrow (to_Zero B) (F a1) (F a2).
  Proof.
    rewrite <- PreAdditive_unel_zero. rewrite <- PreAdditive_unel_zero.
    apply AdditiveFunctorUnel.
  Qed.

  Lemma AdditiveFunctorLinear {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B) {a1 a2 : A}
        (f g : a1 --> a2) : # F (to_binop _ _ f g) = to_binop _ _ (# F f) (# F g).
  Proof.
    apply (pr1 (pr2 F a1 a2)).
  Qed.

  Lemma AdditiveFunctorInv {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B) {a1 a2 : A} (f : a1 --> a2) :
    # F (to_inv f) = to_inv (# F f).
  Proof.
    apply (to_lcan _ (# F f)). rewrite <- AdditiveFunctorLinear.
    rewrite rinvax. rewrite AdditiveFunctorUnel. rewrite rinvax.
    apply idpath.
  Qed.

  Definition CompositionIsAdditive {A1 A2 A3 : CategoryWithAdditiveStructure} (F1 : AdditiveFunctor A1 A2)
             (F2 : AdditiveFunctor A2 A3) : isAdditiveFunctor (functor_composite F1 F2).
  Proof.
    use make_isAdditiveFunctor'.
    - intros a1 a2. cbn. rewrite AdditiveFunctorZeroArrow. use AdditiveFunctorZeroArrow.
    - intros a1 a2 f g. cbn. rewrite AdditiveFunctorLinear. use AdditiveFunctorLinear.
  Qed.

  Definition AdditiveComposite {A1 A2 A3 : CategoryWithAdditiveStructure}(F1 : AdditiveFunctor A1 A2)
             (F2 : AdditiveFunctor A2 A3) : AdditiveFunctor A1 A3 :=
    make_AdditiveFunctor (functor_composite F1 F2) (CompositionIsAdditive F1 F2).

End def_additivefunctor.


(** * Additive functor preserves BinDirectSums
   We say that a functor F between additive categories A and B preserves BinDirectSums if for any
   BinDirectSum (a1 ⊕ a2, in1, in2, pr1, pr2) in A, the data (F(a1 ⊕ a2), F(in1), F(in2), F(pr1),
   F(pr2)) is a BinDirectSum in B. *)
Section additivefunctor_preserves_bindirectsums.

  Definition PreservesBinDirectSums {A B : CategoryWithAdditiveStructure} (F : functor A B) : hProp :=
    ∀ (a1 a2 : A) (DS : BinDirectSum a1 a2),
    isBinDirectSum
                       (# F (to_In1 DS)) (# F (to_In2 DS))
                       (# F (to_Pr1 DS)) (# F (to_Pr2 DS)).

  (** Additive functor preserves zeros. *)
  Lemma AdditiveFunctorPreservesBinDirectSums_zero {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B) :
    isZero (F (to_Zero A)).
  Proof.
    set (isadd0 := AdditiveFunctor_isAdditiveFunctor F (to_Zero A) (to_Zero A)).
    set (unel := to_unel (to_Zero A) (to_Zero A)).
    set (tmp := (pr2 isadd0)). cbn in tmp.
    set (tmp1 := PreAdditive_unel_zero A (to_Zero A) (to_Zero A) (to_Zero A)).
    unfold to_unel in tmp1. rewrite tmp1 in tmp. clear tmp1.
    assert (tmp2 : identity (to_Zero A) = ZeroArrow (to_Zero A) _ _) by apply ArrowsToZero.
    rewrite <- tmp2 in tmp. clear tmp2.
    assert (X : # F (identity (to_Zero A)) = identity (F (to_Zero A))) by apply functor_id.
    set (tmp2 := PreAdditive_unel_zero B (to_Zero B) (F (to_Zero A)) (F (to_Zero A))).
    unfold to_unel in tmp2. rewrite tmp2 in tmp. clear tmp2.
    assert (X0 : iso (F (to_Zero A)) (to_Zero B)).
    {
      use make_iso.
      - apply (ZeroArrowTo (F (to_Zero A))).
      - use is_iso_qinv.
        apply (ZeroArrowFrom (F (to_Zero A))).
        split.
        + rewrite <- X. rewrite tmp. apply ZeroArrowEq.
        + apply ArrowsToZero.
    }
    apply (IsoToisZero B (to_Zero B) X0).
  Qed.

  (** ** F preserves IdIn1, IdIn2, IdUnit1, IdUnit2, and Id of BinDirectSum *)

  Local Lemma AdditiveFunctorPreservesBinDirectSums_idin1 {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B)
        {a1 a2 : A} (DS : BinDirectSum a1 a2) :
    (# F (to_In1 DS)) · (# F (to_Pr1 DS)) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite (to_IdIn1 DS). apply functor_id.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_idin2 {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B)
        {a1 a2 : A} (DS : BinDirectSum a1 a2) :
    (# F (to_In2 DS)) · (# F (to_Pr2 DS)) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite (to_IdIn2 DS). apply functor_id.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_unit1 {A B : CategoryWithAdditiveStructure}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSum a1 a2) :
    (# F (to_In1 DS)) · (# F (to_Pr2 DS)) = to_unel (F a1) (F a2).
  Proof.
    rewrite <- functor_comp. rewrite (to_Unel1 DS). apply AdditiveFunctorUnel.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_unit2 {A B : CategoryWithAdditiveStructure}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSum a1 a2) :
    (# F (to_In2 DS)) · (# F (to_Pr1 DS)) = to_unel (F a2) (F a1).
  Proof.
    rewrite <- functor_comp. rewrite (to_Unel2 DS). apply AdditiveFunctorUnel.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_id {A B : CategoryWithAdditiveStructure}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSum a1 a2) :
    to_binop _ _
             ((# F (to_Pr1 DS)) · (# F (to_In1 DS)))
             ((# F (to_Pr2 DS)) · (# F (to_In2 DS))) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite <- functor_comp.
    rewrite <- AdditiveFunctorLinear. rewrite (to_BinOpId DS). apply functor_id.
  Qed.

  (** An additive functor preserves BinDirectSums *)
  Lemma AdditiveFunctorPreservesBinDirectSums {A B : CategoryWithAdditiveStructure} (F : AdditiveFunctor A B) :
    PreservesBinDirectSums F.
  Proof.
    intros a1 a2 DS.
    use make_isBinDirectSum.
    - use (AdditiveFunctorPreservesBinDirectSums_idin1 F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_idin2 F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_unit1 F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_unit2 F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_id F DS).
  Qed.

End additivefunctor_preserves_bindirectsums.


(** * Additive criteria
   In this section we show that a functor between additive categories which preserves BinDirectSums
   is additive. *)
Section additivefunctor_criteria.


  (** ** Preserves unel *)

  (** A functor which preserves binary direct sums preserves zero objects. *)
  Lemma isAdditiveCriteria_isZero {A B : CategoryWithAdditiveStructure} (F : functor A B)
        (H : PreservesBinDirectSums F) : isZero (F (to_Zero A)).
  Proof.
    set (DS := to_BinDirectSums A (to_Zero A) (to_Zero A)).
    set (isBDS := H (to_Zero A) (to_Zero A) DS).
    assert (e1 : (# F (to_In1 DS)) = (# F (to_In2 DS))).
    {
      apply maponpaths.
      apply ArrowsFromZero.
    }
    assert (e2 : (# F (to_Pr1 DS)) = (# F (to_Pr2 DS))).
    {
      apply maponpaths.
      apply ArrowsToZero.
    }
    cbn in isBDS.
    rewrite e1 in isBDS. rewrite e2 in isBDS. clear e1 e2.
    set (BDS := make_BinDirectSum _ _ _ _ _ _ _ _ isBDS).
    use make_isZero.
    - intros b.
      use tpair.
      + apply (ZeroArrow (to_Zero B) _ _).
      + cbn. intros t.
        use (pathscomp0 (!(BinDirectSumIn1Commutes B BDS _ t (ZeroArrow (to_Zero B) _ _)))).
        use (pathscomp0 _ (BinDirectSumIn2Commutes B BDS _ t (ZeroArrow (to_Zero B) _ _))).
        cbn. apply cancel_precomposition. apply idpath.
    - intros a.
      use tpair.
      + apply (ZeroArrow (to_Zero B) _ _).
      + cbn. intros t.
        use (pathscomp0 (!(BinDirectSumPr1Commutes B BDS _ t (ZeroArrow (to_Zero B) _ _)))).
        use (pathscomp0 _ (BinDirectSumPr2Commutes B BDS _ t (ZeroArrow (to_Zero B) _ _))).
        cbn. apply cancel_postcomposition. apply idpath.
  Qed.

  (** F preserves unel *)
  Local Corollary isAdditiveCriteria_preservesUnel {A B : CategoryWithAdditiveStructure} (F : functor A B)
        (H : PreservesBinDirectSums F) (a1 a2 : A) :
    (# F (to_unel a1 a2)) = (to_unel (F a1) (F a2)).
  Proof.
    set (Z := make_Zero (F (to_Zero A)) (isAdditiveCriteria_isZero F H)).
    rewrite (PreAdditive_unel_zero A (to_Zero A) a1 a2).
    rewrite (PreAdditive_unel_zero B Z (F a1) (F a2)).
    unfold ZeroArrow. rewrite functor_comp. cbn.
    assert (e1 : # F (ZeroArrowTo a1) = @ZeroArrowTo B Z (F a1)).
    {
      apply (ArrowsToZero B Z).
    }
    assert (e2 : # F (ZeroArrowFrom a2) = @ZeroArrowFrom B Z (F a2)).
    {
      apply (ArrowsFromZero B Z).
    }
    rewrite e1. rewrite e2. apply idpath.
  Qed.


  (** ** Commutes with binop *)

  (** F commutes with addition of projections from a1 ⊕ a1 *)
  Local Lemma isAdditiveCriteria_isBinopFun_Pr {A B : CategoryWithAdditiveStructure} (F : functor A B)
        (H : PreservesBinDirectSums F) {a1 a2 : A} (DS : BinDirectSum a1 a1):
    # F (to_binop DS a1 (to_Pr1 DS) (to_Pr2 DS)) =
    to_binop (F DS) (F a1) (# F (to_Pr1 DS)) (# F (to_Pr2 DS)).
  Proof.
    set (isBDS := H a1 a1 DS).
    set (BDS := make_BinDirectSum _ _ _ _ _ _ _ _ isBDS).
    use (FromBinDirectSumsEq B BDS); cbn.
    - rewrite <- functor_comp.
      rewrite to_premor_linear'.
      rewrite (to_IdIn1 DS). rewrite (to_Unel1 DS).
      rewrite to_runax'. rewrite functor_id.
      rewrite to_premor_linear'.
      rewrite <- functor_comp. rewrite <- functor_comp.
      rewrite (to_IdIn1 DS). rewrite (to_Unel1 DS).
      rewrite functor_id. rewrite (isAdditiveCriteria_preservesUnel _ H).
      rewrite to_runax'. apply idpath.
    - rewrite <- functor_comp.
      rewrite to_premor_linear'.
      rewrite (to_Unel2 DS). rewrite (to_IdIn2 DS). rewrite to_lunax'. rewrite functor_id.
      rewrite to_premor_linear'.
      rewrite <- functor_comp. rewrite <- functor_comp.
      rewrite (to_Unel2 DS). rewrite (to_IdIn2 DS).
      rewrite (isAdditiveCriteria_preservesUnel _ H). rewrite functor_id. rewrite to_lunax'.
      apply idpath.
  Qed.

  Local Lemma isAdditiveCriteria_BinOp_eq {A B : CategoryWithAdditiveStructure} (F : functor A B)
        (H : PreservesBinDirectSums F) {a1 a2 : A} (f g : A⟦a1, a2⟧)
        (DS := to_BinDirectSums A a2 a2) :
    to_binop a1 a2 f g = (to_binop a1 DS (f · (to_In1 DS)) (g · (to_In2 DS)))
                           · (to_binop DS a2 (to_Pr1 DS) (to_Pr2 DS)).
  Proof.
    set (isBDS := H a2 a2 DS).
    set (BDS := make_BinDirectSum _ _ _ _ _ _ _ _ isBDS).
    (* First term of to_binop *)
    rewrite to_premor_linear'. rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn1 DS). rewrite (to_Unel2 DS).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_runax'.
    (* Second term of to_binop *)
    rewrite to_postmor_linear'. rewrite <- assoc. rewrite <- assoc.
    rewrite (to_Unel1 DS). rewrite (to_IdIn2 DS).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_lunax'.
    apply idpath.
  Qed.

  (** F commutes with addition of morphisms *)
  Local Lemma isAdditiveCriteria_BinOp {A B : CategoryWithAdditiveStructure} (F : functor A B)
        (H : PreservesBinDirectSums F) {a1 a2 : A} (f g : A⟦a1, a2⟧) :
    # F (to_binop a1 a2 f g) = to_binop (F a1) (F a2) (# F f) (# F g).
  Proof.
    set (DS := to_BinDirectSums A a2 a2).
    set (isBDS := H a2 a2 DS).
    set (BDS := make_BinDirectSum _ _ _ _ _ _ _ _ isBDS).
    rewrite (isAdditiveCriteria_BinOp_eq F H f g). rewrite functor_comp.
    rewrite (@isAdditiveCriteria_isBinopFun_Pr A B F H a2 DS).
    rewrite to_premor_linear'.
    (* First term of the first to_binop *)
    rewrite <- functor_comp. rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc.
    fold DS. rewrite (to_IdIn1 DS). rewrite (to_Unel2 DS).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_runax'.
    (* Second term of the first to_binop *)
    rewrite <- functor_comp. rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn2 DS). rewrite (to_Unel1 DS).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_lunax'.
    apply idpath.
  Qed.

  Lemma isAdditiveCriteria {A B : CategoryWithAdditiveStructure} (F : functor A B) (H : PreservesBinDirectSums F) :
    isAdditiveFunctor F.
  Proof.
    use make_isAdditiveFunctor.
    intros a1 a2.
    split.
    - intros f g. cbn.
      apply (isAdditiveCriteria_BinOp F H f g).
    - set (tmp := isAdditiveCriteria_preservesUnel F H a1 a2). unfold to_unel in tmp.
      apply tmp.
  Qed.

  Definition AdditiveFunctorCriteria {A B : CategoryWithAdditiveStructure} (F : functor A B)
             (H : PreservesBinDirectSums F) : AdditiveFunctor A B.
  Proof.
    use make_AdditiveFunctor.
    - exact F.
    - exact (isAdditiveCriteria F H).
  Defined.

End additivefunctor_criteria.


(** * The functor [QuotcategoryFunctor] is additive *)
Section def_additive_quot_functor.

  Variable A : CategoryWithAdditiveStructure.
  Variable PAS : PreAdditiveSubabgrs A.
  Variable PAC : PreAdditiveComps A PAS.

  Local Lemma QuotcategoryAdditiveFunctor_isAdditiveFunctor :
    @isAdditiveFunctor A (Quotcategory_Additive A PAS PAC)
                       (QuotcategoryFunctor (Additive_PreAdditive A) PAS PAC).
  Proof.
    use make_isAdditiveFunctor.
    intros X Y.
    split.
    - intros f g. apply idpath.
    - apply idpath.
  Qed.

  Definition QuotcategoryAdditiveFunctor :
    AdditiveFunctor A (Quotcategory_Additive A PAS PAC).
  Proof.
    use make_AdditiveFunctor.
    - exact (QuotcategoryFunctor A PAS PAC).
    - exact QuotcategoryAdditiveFunctor_isAdditiveFunctor.
  Defined.

End def_additive_quot_functor.


(** * Equivalences of additive categories *)
Section def_additive_equivalence.

  Definition AddEquiv (A1 A2 : CategoryWithAdditiveStructure) : UU :=
    ∑ D : (∑ F : (AdditiveFunctor A1 A2 × AdditiveFunctor A2 A1),
                 are_adjoints (dirprod_pr1 F) (dirprod_pr2 F)),
          (∏ a : A1, is_z_isomorphism (unit_from_left_adjoint (pr2 D) a))
            × (∏ b : A2, is_z_isomorphism (counit_from_left_adjoint (pr2 D) b)).

  Definition make_AddEquiv {A1 A2 : CategoryWithAdditiveStructure} (F : AdditiveFunctor A1 A2)
             (G : AdditiveFunctor A2 A1) (H : are_adjoints F G)
             (H1 : ∏ a : A1, is_z_isomorphism (unit_from_left_adjoint H a))
             (H2 : ∏ b : A2, is_z_isomorphism (counit_from_left_adjoint H b)) :
    AddEquiv A1 A2 := (((F,,G),,H),,(H1,,H2)).

  (** Accessor functions *)
  Definition AddEquiv1 {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) : AdditiveFunctor A1 A2 :=
    dirprod_pr1 (pr1 (pr1 AE)).

  Definition AddEquiv2 {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) : AdditiveFunctor A2 A1 :=
    dirprod_pr2 (pr1 (pr1 AE)).

  Definition AddEquiv_are_adjoints {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) :
    are_adjoints (AddEquiv1 AE) (AddEquiv2 AE) := pr2 (pr1 AE).
  Coercion AddEquiv_are_adjoints : AddEquiv >-> are_adjoints.

  Definition AddEquivUnit {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) :
    nat_trans (functor_identity A1) (functor_composite (AddEquiv1 AE) (AddEquiv2 AE)) :=
    unit_from_left_adjoint AE.

  Definition AddEquivCounit {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) :
    nat_trans (functor_composite (AddEquiv2 AE) (AddEquiv1 AE)) (functor_identity A2) :=
    counit_from_left_adjoint AE.

  Definition AddEquivUnitInvMor {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) (X : A1) :
    A1⟦(AddEquiv2 AE (AddEquiv1 AE X)), X⟧ := pr1 ((dirprod_pr1 (pr2 AE)) X).

  Definition AddEquivUnitInvMor_is_iso_with_inv_data {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2)
             (X : A1) : is_z_isomorphism (unit_from_left_adjoint AE X) :=
    ((dirprod_pr1 (pr2 AE)) X).

  Definition AddEquivUnitInvMor_is_inverse_in_precat {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2)
             (X : A1) :
    is_inverse_in_precat (unit_from_left_adjoint AE X) (AddEquivUnitInvMor AE X) :=
    pr2 ((dirprod_pr1 (pr2 AE)) X).

  Definition AddEquivCounitInvMor {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) (X : A2) :
    A2⟦X, (AddEquiv1 AE (AddEquiv2 AE X))⟧ := pr1 ((dirprod_pr2 (pr2 AE)) X).

  Definition AddEquivCounitInvMor_is_iso_with_inv_data {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2)
             (X : A2) : is_z_isomorphism (counit_from_left_adjoint AE X) :=
    ((dirprod_pr2 (pr2 AE)) X).

  Definition AddEquivCounitInvMor_is_inverse_in_precat {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2)
             (X : A2) :
    is_inverse_in_precat (counit_from_left_adjoint AE X) (AddEquivCounitInvMor AE X) :=
    pr2 ((dirprod_pr2 (pr2 AE)) X).

  Definition AddEquivUnitIso {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) (X : A1) :
    z_iso X (AddEquiv2 AE (AddEquiv1 AE X)).
  Proof.
    use make_z_iso.
    - exact (AddEquivUnit AE X).
    - exact (AddEquivUnitInvMor AE X).
    - exact (AddEquivUnitInvMor_is_inverse_in_precat AE X).
  Defined.

  Definition AddEquivCounitIso {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) (X : A2) :
    z_iso (AddEquiv1 AE (AddEquiv2 AE X)) X.
  Proof.
    use make_z_iso.
    - exact (AddEquivCounit AE X).
    - exact (AddEquivCounitInvMor AE X).
    - exact (AddEquivCounitInvMor_is_inverse_in_precat AE X).
  Defined.

  Definition AddEquivLeftTriangle {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) :
    ∏ (a : ob A1), # (AddEquiv1 AE) (AddEquivUnitIso AE a)
                     · AddEquivCounitIso AE (AddEquiv1 AE a) =
                   identity (AddEquiv1 AE a) := triangle_id_left_ad AE.

  Definition AddEquivRightTriangle {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) :
    ∏ (b : ob A2), (AddEquivUnitIso AE (AddEquiv2 AE b))
                     · # (AddEquiv2 AE) (AddEquivCounitIso AE b) =
                   identity (AddEquiv2 AE b) := triangle_id_right_ad AE.

  Definition AddEquivUnitComm {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) :
    ∏ (x x' : ob A1) (f : x --> x'),
    f · (AddEquivUnitIso AE x') =
    (AddEquivUnitIso AE x) · # (functor_composite (AddEquiv1 AE) (AddEquiv2 AE)) f :=
    nat_trans_ax (AddEquivUnit AE).

  Definition AddEquivCounitComm {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) :
    ∏ (x x' : A2) (f : x --> x'),
    # (functor_composite (AddEquiv2 AE) (AddEquiv1 AE)) f · (AddEquivCounitIso AE x') =
    (AddEquivCounitIso AE x) · f := nat_trans_ax (AddEquivCounit AE).

  Lemma AddEquivUnitMorComm {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) {x x' : ob A1} (f : x --> x') :
    f = (AddEquivUnitIso AE x)
          · (# (functor_composite (AddEquiv1 AE) (AddEquiv2 AE)) f)
          · (inv_from_z_iso (AddEquivUnitIso AE x')).
  Proof.
    use (post_comp_with_z_iso_is_inj (AddEquivUnitIso AE x')).
    use (pathscomp0 (AddEquivUnitComm AE _ _ f)).
    rewrite <- assoc.
    set (tmp := is_inverse_in_precat2 (AddEquivUnitIso AE x')). cbn in tmp. cbn.
    rewrite tmp. clear tmp. rewrite id_right. apply idpath.
  Qed.

  Lemma AddEquivCounitMorComm {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) {x x' : ob A2} (f : x --> x') :
    f = (inv_from_z_iso (AddEquivCounitIso AE x))
          · (# (functor_composite (AddEquiv2 AE) (AddEquiv1 AE)) f)
          · (AddEquivCounitIso AE x').
  Proof.
    use (pre_comp_with_z_iso_is_inj (AddEquivCounitIso AE x)).
    use (pathscomp0 (! AddEquivCounitComm AE _ _ f)).
    rewrite assoc. rewrite assoc.
    set (tmp := is_inverse_in_precat1 (AddEquivCounitIso AE x)). rewrite tmp.
    rewrite id_left. apply idpath.
  Qed.

  Definition AddEquivUnitInv {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) {x x' : ob A1} (f : x --> x') :
    inv_from_z_iso (AddEquivUnitIso AE x) · f =
    # (functor_composite (AddEquiv1 AE) (AddEquiv2 AE)) f
      · inv_from_z_iso (AddEquivUnitIso AE x').
  Proof.
    use (pre_comp_with_z_iso_is_inj (AddEquivUnitIso AE x)). rewrite assoc.
    rewrite (is_inverse_in_precat1 (AddEquivUnitIso AE x)). rewrite id_left.
    use (post_comp_with_z_iso_is_inj (AddEquivUnitIso AE x')).
    rewrite AddEquivUnitComm. rewrite <- assoc. apply cancel_precomposition. cbn.
    rewrite <- assoc.
    set (tmp := is_inverse_in_precat2 (AddEquivUnitIso AE x')). cbn in tmp. cbn. rewrite tmp.
    rewrite id_right. apply idpath.
  Qed.

  Definition AddEquivCounitInv {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) {x x' : ob A2}
             (f : x --> x') :
    (inv_from_z_iso (AddEquivCounitIso AE x))
      · # (functor_composite (AddEquiv2 AE) (AddEquiv1 AE)) f =
    f · inv_from_z_iso (AddEquivCounitIso AE x').
  Proof.
    use (pre_comp_with_z_iso_is_inj (AddEquivCounitIso AE x)). rewrite assoc.
    rewrite (is_inverse_in_precat1 (AddEquivCounitIso AE x)). rewrite id_left.
    use (post_comp_with_z_iso_is_inj (AddEquivCounitIso AE x')).
    use (pathscomp0 (AddEquivCounitComm AE _ _ f)). rewrite <- assoc.
    apply cancel_precomposition. cbn.
    rewrite <- assoc.
    set (tmp := is_inverse_in_precat2 (AddEquivCounitIso AE x')). cbn in tmp. cbn. rewrite tmp.
    rewrite id_right. apply idpath.
  Qed.

  Lemma AddEquivCounitUnit {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) (x : A1) :
    inv_from_z_iso (AddEquivCounitIso AE (AddEquiv1 AE x)) =
    # (AddEquiv1 AE) (AddEquivUnitIso AE x).
  Proof.
    use (post_comp_with_z_iso_is_inj (AddEquivCounitIso AE (AddEquiv1 AE x))).
    apply pathsinv0. rewrite (is_inverse_in_precat2 (AddEquivCounitIso AE ((AddEquiv1 AE) x))).
    exact (AddEquivLeftTriangle AE x).
  Qed.

  Lemma AddEquivCounitUnit' {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) (x : A1) :
    ((AddEquivCounitIso AE (AddEquiv1 AE x)) : A2⟦_, _⟧) =
    # (AddEquiv1 AE) (inv_from_z_iso (AddEquivUnitIso AE x)).
  Proof.
    use (post_comp_with_z_iso_inv_is_inj (AddEquivCounitIso AE (AddEquiv1 AE x))).
    apply pathsinv0. rewrite (is_inverse_in_precat1 (AddEquivCounitIso AE ((AddEquiv1 AE) x))).
    rewrite AddEquivCounitUnit. rewrite <- functor_comp.
    rewrite (is_inverse_in_precat2 (AddEquivUnitIso AE x)). apply functor_id.
  Qed.

  Lemma AddEquivUnitCounit {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) (x : A2) :
    inv_from_z_iso (AddEquivUnitIso AE (AddEquiv2 AE x)) =
    # (AddEquiv2 AE) (AddEquivCounitIso AE x).
  Proof.
    use (pre_comp_with_z_iso_is_inj (AddEquivUnitIso AE (AddEquiv2 AE x))).
    apply pathsinv0. rewrite (is_inverse_in_precat1 (AddEquivUnitIso AE ((AddEquiv2 AE) x))).
    exact (AddEquivRightTriangle AE x).
  Qed.

  Lemma AddEquivUnitCounit' {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) (x : A2) :
    ((AddEquivUnitIso AE (AddEquiv2 AE x)) : A1⟦_, _⟧) =
    # (AddEquiv2 AE) (inv_from_z_iso (AddEquivCounitIso AE x)).
  Proof.
    use (pre_comp_with_z_iso_inv_is_inj (AddEquivUnitIso AE (AddEquiv2 AE x))).
    apply pathsinv0. rewrite (is_inverse_in_precat2 (AddEquivUnitIso AE ((AddEquiv2 AE) x))).
    rewrite AddEquivUnitCounit. rewrite <- functor_comp.
    rewrite (is_inverse_in_precat1 (AddEquivCounitIso AE x)). apply functor_id.
  Qed.

  Lemma AddEquiv1Inj {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) {x y : A1} (f g : x --> y)
        (H : # (AddEquiv1 AE) f = # (AddEquiv1 AE) g) : f = g.
  Proof.
    apply (maponpaths (# (AddEquiv2 AE))) in H.
    use (post_comp_with_z_iso_is_inj (AddEquivUnitIso AE y)).
    use (pathscomp0 (AddEquivUnitComm AE _ _ f)).
    use (pathscomp0 _ (! (AddEquivUnitComm AE _ _ g))).
    exact (maponpaths (λ gg : _, (AddEquivUnit AE) x · gg) H).
  Qed.

  Lemma AddEquiv2Inj {A1 A2 : CategoryWithAdditiveStructure} (AE : AddEquiv A1 A2) {x y : A2} (f g : x --> y)
        (H : # (AddEquiv2 AE) f = # (AddEquiv2 AE) g) : f = g.
  Proof.
    apply (maponpaths (# (AddEquiv1 AE))) in H.
    use (pre_comp_with_z_iso_is_inj (AddEquivCounitIso AE x)).
    use (pathscomp0 (! AddEquivCounitComm AE _ _ f)).
    use (pathscomp0 _ (AddEquivCounitComm AE _ _ g)).
    exact (maponpaths (λ gg : _, gg · (AddEquivCounit AE) y) H).
  Qed.

End def_additive_equivalence.
