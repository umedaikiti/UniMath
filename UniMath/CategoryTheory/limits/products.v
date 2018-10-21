(**

Direct implementation of indexed products together with:

- The general product functor ([product_functor])
- Definition of a product structure on a functor category by taking pointwise products in the target
  category (adapted from the binary version) ([Products_functor_precat])
- Products from limits ([Products_from_Lims])
- Uniqueness of products

Written by: Anders Mörtberg 2016
Extended by: Langston Barrett 2018

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Local Open Scope cat.

(** * Definition of indexed products of objects in a precategory *)
Section product_def.

Variable (I : UU) (C : category).

Definition isProduct (c : ∏ (i : I), C) (p : C)
  (pi : ∏ i, p --> c i) :=
  ∏ (a : C) (f : ∏ i, a --> c i),
    ∃! (fap : a --> p), ∏ i, fap · pi i = f i.

Definition Product (ci : ∏ i, C) :=
  ∑ pp1p2 : (∑ p : C, ∏ i, p --> ci i),
    isProduct ci (pr1 pp1p2) (pr2 pp1p2).

Definition Products := ∏ (ci : ∏ i, C), Product ci.
Definition hasProducts := ∏ (ci : ∏ i, C), ∥ Product ci ∥.

Definition ProductObject {c : ∏ i, C} (P : Product c) : C := pr1 (pr1 P).
Definition ProductPr {c : ∏ i, C} (P : Product c) : ∏ i, ProductObject P --> c i :=
  pr2 (pr1 P).

Definition isProduct_Product {c : ∏ i, C} (P : Product c) :
   isProduct c (ProductObject P) (ProductPr P).
 Proof.
  exact (pr2 P).
Defined.

Definition isaprop_isProduct (c : ∏ (i : I), C) (p : C)
           (pi : ∏ i, p --> c i) : isaprop (isProduct c p pi).
Proof.
  unfold isProduct.
  do 2 (apply impred; intro).
  apply isapropiscontr.
Defined.

Definition ProductArrow {c : ∏ i, C} (P : Product c) {a : C} (f : ∏ i, a --> c i)
  : a --> ProductObject P.
Proof.
  apply (pr1 (pr1 (isProduct_Product P _ f))).
Defined.

Lemma ProductPrCommutes (c : ∏ i, C) (P : Product c) :
     ∏ (a : C) (f : ∏ i, a --> c i) i, ProductArrow P f · ProductPr P i = f i.
Proof.
  intros a f i.
  apply (pr2 (pr1 (isProduct_Product P _ f)) i).
Qed.

Lemma ProductPr_idtoiso {i1 i2 : I} (a : I -> C) (P : Product a)
      (e : i1 = i2) :
  ProductPr P i1 · idtoiso (maponpaths a e) = ProductPr P i2.
Proof.
  induction e.
  apply id_right.
Qed.

Lemma ProductArrowUnique (c : ∏ i, C) (P : Product c) (x : C)
    (f : ∏ i, x --> c i) (k : x --> ProductObject P)
    (Hk : ∏ i, k · ProductPr P i = f i) : k = ProductArrow P f.
Proof.
  set (H' := pr2 (isProduct_Product P _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Definition make_Product (a : ∏ i, C) :
  ∏ (c : C) (f : ∏ i, C⟦c,a i⟧), isProduct _ _ f -> Product a.
Proof.
  intros c f X.
  exact (tpair _ (c,,f) X).
Defined.

Definition make_isProduct (hsC : has_homsets C) (a : I -> C) (p : C)
  (pa : ∏ i, C⟦p,a i⟧) : (∏ (c : C) (f : ∏ i, C⟦c,a i⟧),
                                  ∃! k : C⟦c,p⟧, ∏ i, k · pa i = f i) ->
                              isProduct a p pa.
Proof.
intros H c cc; apply H.
Defined.

Lemma ProductArrowEta (c : ∏ i, C) (P : Product c) (x : C)
    (f : x --> ProductObject P) :
    f = ProductArrow P (λ i, f · ProductPr P i).
Proof.
  now apply ProductArrowUnique.
Qed.

Definition ProductOfArrows {c : ∏ i, C} (Pc : Product c) {a : ∏ i, C}
    (Pa : Product a) (f : ∏ i, a i --> c i) :
      ProductObject Pa --> ProductObject Pc :=
    ProductArrow Pc (λ i, ProductPr Pa i · f i).

Lemma ProductOfArrowsPr {c : ∏ i, C} (Pc : Product c) {a : ∏ i, C}
    (Pa : Product a) (f : ∏ i, a i --> c i) :
    ∏ i, ProductOfArrows Pc Pa f · ProductPr Pc i = ProductPr Pa i · f i.
Proof.
  unfold ProductOfArrows; intro i.
  now rewrite (ProductPrCommutes _ _ _ _ i).
Qed.

Lemma postcompWithProductArrow {c : ∏ i, C} (Pc : Product c) {a : ∏ i, C}
    (Pa : Product a) (f : ∏ i, a i --> c i)
    {x : C} (k : ∏ i, x --> a i) :
        ProductArrow Pa k · ProductOfArrows Pc Pa f =
        ProductArrow Pc (λ i, k i · f i).
Proof.
apply ProductArrowUnique; intro i.
now rewrite <- assoc, ProductOfArrowsPr, assoc, ProductPrCommutes.
Qed.

Lemma precompWithProductArrow {c : ∏ i, C} (Pc : Product c)
  {a : C} (f : ∏ i, a --> c i) {x : C} (k : x --> a)  :
       k · ProductArrow Pc f = ProductArrow Pc (λ i, k · f i).
Proof.
apply ProductArrowUnique; intro i.
now rewrite <- assoc, ProductPrCommutes.
Qed.

End product_def.

Section Products.

Variables (I : UU) (C : category) (CC : Products I C).

Definition ProductOfArrows_comp (a b c : ∏ (i : I), C)
  (f : ∏ i, a i --> b i) (g : ∏ i, b i --> c i)
  : ProductOfArrows _ _ _ _ f · ProductOfArrows _ _ _ (CC _) g
    = ProductOfArrows _ _ (CC _) (CC _) (λ i, f i · g i).
Proof.
apply ProductArrowUnique; intro i.
rewrite <- assoc, ProductOfArrowsPr.
now rewrite assoc, ProductOfArrowsPr, assoc.
Qed.

End Products.

Section Product_unique.

Variables (I : UU) (C : category).
Variable CC : Products I C.
Variables a : ∏ (i : I), C.

Lemma Product_endo_is_identity (P : Product _ _ a)
  (k : ProductObject _ _ P --> ProductObject _ _ P)
  (H1 : ∏ i, k · ProductPr _ _ P i = ProductPr _ _ P i)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply ProductArrowEta.
  apply pathsinv0.
  apply ProductArrowUnique; intro i; apply pathsinv0.
  now rewrite id_left, H1.
Qed.

End Product_unique.

(** * The product functor: C^I -> C *)
Section product_functor.

Context (I : UU) {C : category} (PC : Products I C).

Definition product_functor_data :
  functor_data (power_category I C) C.
Proof.
use tpair.
- intros p.
  apply (ProductObject _ _ (PC p)).
- simpl; intros p q f.
  exact (ProductOfArrows _ _ _ _ f).
Defined.

Definition product_functor : functor (power_category I C) C.
Proof.
apply (tpair _ product_functor_data).
abstract (split;
  [ now intro x; simpl; apply pathsinv0, Product_endo_is_identity;
        intro i; rewrite ProductOfArrowsPr, id_right
  | now intros x y z f g; simpl; rewrite ProductOfArrows_comp]).
Defined.

End product_functor.

(* The product of a family of functors *)
Definition product_of_functors_alt
  (I : UU) {C D : category} (HD : Products I D)
  (F : ∏ (i : I), functor C D) : functor C D :=
   functor_composite (delta_functor I C)
     (functor_composite (family_functor _ F) (product_functor _ HD)).

(** * Products lift to functor categories *)
Section def_functor_pointwise_prod.

Variables (I : UU) (C D : category).
Variable HD : Products I D.

Section product_of_functors.

Variables F : I -> functor C D.

Definition product_of_functors_ob (c : C) : D :=
  ProductObject _ _ (HD (λ i, F i c)).

Definition product_of_functors_mor (c c' : C) (f : c --> c') :
  product_of_functors_ob c --> product_of_functors_ob c' :=
    ProductOfArrows _ _ _ _ (λ i, # (F i) f).

Definition product_of_functors_data : functor_data C D.
Proof.
  exists product_of_functors_ob.
  exact product_of_functors_mor.
Defined.

Lemma is_functor_product_of_functors_data : is_functor product_of_functors_data.
Proof.
split; simpl; intros.
- unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply Product_endo_is_identity; intro i.
    unfold product_of_functors_mor.
    eapply pathscomp0; [apply (ProductOfArrowsPr _ _ (HD (λ i, (F i) a)))|].
    now simpl; rewrite functor_id, id_right.
- unfold functor_compax; simpl; unfold product_of_functors_mor.
  intros; simpl in *.
  apply pathsinv0.
  eapply pathscomp0.
  apply ProductOfArrows_comp.
  apply maponpaths, funextsec; intro i.
  now rewrite functor_comp.
Qed.

Definition product_of_functors : functor C D :=
  tpair _ _ is_functor_product_of_functors_data.

Lemma product_of_functors_alt_eq_product_of_functors :
  product_of_functors_alt _ HD F = product_of_functors.
Proof.
now apply (functor_eq _ _ D).
Defined.

Definition product_nat_trans_pr_data i (c : C) :
  D ⟦ product_of_functors c, (F i) c ⟧ :=
  ProductPr _ _ (HD (λ j, (F j) c)) i.

Lemma is_nat_trans_product_nat_trans_pr_data i :
  is_nat_trans _ _ (product_nat_trans_pr_data i).
Proof.
intros c c' f.
apply (ProductOfArrowsPr I _ (HD (λ i, F i c')) (HD (λ i, F i c))).
Qed.

Definition product_nat_trans_pr i : nat_trans product_of_functors (F i) :=
  tpair _ _ (is_nat_trans_product_nat_trans_pr_data i).

Section vertex.

(** The product morphism of a diagram with vertex [A] *)

Variable A : functor C D.
Variable f : ∏ i, nat_trans A (F i).

Definition product_nat_trans_data c :
  A c --> product_of_functors c:=
    ProductArrow _ _ _ (λ i, f i c).

Lemma is_nat_trans_product_nat_trans_data :
  is_nat_trans _ _ product_nat_trans_data.
Proof.
intros a b k; simpl.
eapply pathscomp0; [apply precompWithProductArrow|].
apply pathsinv0.
eapply pathscomp0; [apply postcompWithProductArrow|].
apply maponpaths, funextsec; intro i.
now rewrite (nat_trans_ax (f i)).
Qed.

Definition product_nat_trans : nat_trans A product_of_functors
  := tpair _ _ is_nat_trans_product_nat_trans_data.

End vertex.

Definition functor_precat_product_cone
  : Product I [C, D] F.
Proof.
use make_Product.
- apply product_of_functors.
- apply product_nat_trans_pr.
- use make_isProduct.
  + apply functor_category_has_homsets.
  + intros A f.
    use tpair.
    * apply (tpair _ (product_nat_trans A f)).
      abstract (intro i; apply (nat_trans_eq D); intro c;
                apply (ProductPrCommutes I D _ (HD (λ j, (F j) c)))).
    * abstract (
        intro t; apply subtypePath; simpl;
          [intro; apply impred; intro; apply (isaset_nat_trans D)|];
        apply (nat_trans_eq D); intro c;
        apply ProductArrowUnique; intro i;
        apply (nat_trans_eq_pointwise (pr2 t i))).
Defined.

End product_of_functors.

Definition Products_functor_precat : Products I [C, D].
Proof.
intros F; apply functor_precat_product_cone.
Defined.

End def_functor_pointwise_prod.

(** * Products from limits *)
Section products_from_limits.

Variables (I : UU) (C : category).

Definition I_graph : graph := (I,,λ _ _,empty).

Definition products_diagram (F : I → C) : diagram I_graph C.
Proof.
exists F.
abstract (intros u v e; induction e).
Defined.

Definition productscone c (F : I → C) (H : ∏ i, c --> F i) :
  cone (products_diagram F) c.
Proof.
use tpair.
+ intro v; apply H.
+ abstract (intros u v e; induction e).
Defined.

Lemma Products_from_Lims : Lims_of_shape I_graph C -> Products I C.
Proof.
intros H F.
set (HF := H (products_diagram F)).
use make_Product.
+ apply (lim HF).
+ intros i; apply (limOut HF).
+ apply (make_isProduct _ _ C); intros c Fic.
  use unique_exists.
  - apply limArrow.
    use make_cone.
    * simpl; intro i; apply Fic.
    * abstract (simpl; intros u v e; induction e).
  - abstract (simpl; intro i; apply (limArrowCommutes HF)).
  - abstract (intros y; apply impred; intro i; apply C).
  - abstract (intros f Hf; apply limArrowUnique; simpl in *; intros i; apply Hf).
Defined.

End products_from_limits.

(** * Uniqueness of products *)

Section uniqueness.
  Context (I : UU) {C : category} (c : I -> C).

  (** The arrow from p1 to p2 induced by the projections from p1 is an iso *)
  Lemma product_unique (p1 p2 : Product I C c) :
    is_iso (ProductArrow _ _ p2 (ProductPr I C p1)).
  Proof.
    use is_iso_qinv.
    - (** The inverse is the induced arrow in the other direction *)
      apply ProductArrow, ProductPr.
    - split.
      + rewrite precompWithProductArrow.
        pose (H := ProductPrCommutes I C c p2 _ (ProductPr _ _ p1)).
        rewrite ProductArrowEta.
        apply maponpaths.
        apply funextsec; intro.
        rewrite H.
        now rewrite id_left.
      + rewrite precompWithProductArrow.
        pose (H := ProductPrCommutes I C c p2 _ (ProductPr _ _ p1)).
        rewrite ProductArrowEta.
        apply maponpaths.
        apply funextsec; intro.
        rewrite ProductPrCommutes.
        now rewrite id_left.
  Qed.

End uniqueness.
