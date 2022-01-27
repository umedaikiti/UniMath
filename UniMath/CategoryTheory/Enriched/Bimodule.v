Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.RepresentableFunctors.Representation.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Enriched.Enriched.

Local Open Scope cat.

Section Bimodule.

Context {Mon_V : monoidal_cat}.

Let I        := monoidal_cat_unit Mon_V.
Let tensor   := monoidal_cat_tensor Mon_V.
Let α        := monoidal_cat_associator Mon_V.
Let l_unitor := monoidal_cat_left_unitor Mon_V.
Let r_unitor := monoidal_cat_right_unitor Mon_V.

Local Notation "X ⊗ Y"  := (tensor (X , Y)).
Local Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Let nat_trans_ax_α {x x' y y' z z' : Mon_V} (f : x --> x') (g : y --> y') (h : z --> z') : ((f #⊗ g) #⊗ h) · α ((_, _), _) = α ((_, _), _) · (f #⊗ (g #⊗ h)) := nat_trans_ax α _ _ ((_ #, _) #, _).

Definition bimodule_data (A B : enriched_precat Mon_V) := ∑ M : enriched_cat_ob B -> enriched_cat_ob A -> ob Mon_V, (∏ (a a' : enriched_cat_ob A) (b : enriched_cat_ob B), enriched_cat_mor a a' ⊗ M b a --> M b a') × (∏ (a : enriched_cat_ob A) (b b' : enriched_cat_ob B), M b a ⊗ enriched_cat_mor b' b --> M b' a).

Definition obj_from_bimodule_data {A B : enriched_precat Mon_V} (m : bimodule_data A B) := pr1 m.

Coercion obj_from_bimodule_data : bimodule_data >-> Funclass.

Definition bimodule_data_left_action {A B : enriched_precat Mon_V} (m : bimodule_data A B) : ∏ (a a' : enriched_cat_ob A) (b : enriched_cat_ob B), enriched_cat_mor a a' ⊗ m b a --> m b a' := pr12 m.

Definition bimodule_data_right_action {A B : enriched_precat Mon_V} (m : bimodule_data A B) : ∏ (a : enriched_cat_ob A) (b b' : enriched_cat_ob B), m b a ⊗ enriched_cat_mor b' b --> m b' a := pr22 m.

Definition make_bimodule_data {A B : enriched_precat Mon_V} m l r : bimodule_data A B := (m,, (l,, r)).

Local Definition left_id_law {A B : enriched_precat Mon_V} (m : bimodule_data A B) := ∏ (a : A) (b : B), (enriched_cat_id _ #⊗ id _) · bimodule_data_left_action m a a b = l_unitor _.

Local Definition left_comp_law {A B : enriched_precat Mon_V} (m : bimodule_data A B) := ∏ (a a' a'' : A) (b : B), (enriched_cat_comp a a' a'' #⊗ id _) · bimodule_data_left_action m a a'' b = α ((_, _), _) · (id (enriched_cat_mor _ _) #⊗ bimodule_data_left_action m a a' b) · bimodule_data_left_action m a' a'' b.

Local Definition right_id_law {A B : enriched_precat Mon_V} (m : bimodule_data A B) := ∏ (a : A) (b : B), (id _ #⊗ enriched_cat_id _) · bimodule_data_right_action m a b b = r_unitor _.

Local Definition right_comp_law {A B : enriched_precat Mon_V} (m : bimodule_data A B) := ∏ (a : A) (b'' b' b : B), α ((_, _), _) · (id (m _ _) #⊗ enriched_cat_comp b b' b'') · bimodule_data_right_action m a _ _ = (bimodule_data_right_action m a _ _ #⊗ id _) · bimodule_data_right_action m a _ _.

Local Definition left_right_commute_law {A B : enriched_precat Mon_V} (m : bimodule_data A B) := ∏ (a a' : A) (b b' : B), (bimodule_data_left_action m a a' b #⊗ id _) · bimodule_data_right_action m a' b b' = α ((_, _), _) · (id (enriched_cat_mor _ _) #⊗ bimodule_data_right_action m a b b') · bimodule_data_left_action m a a' b'.


Definition bimodule_law {A B : enriched_precat Mon_V} (m : bimodule_data A B) := left_id_law m × left_comp_law m × right_id_law m × right_comp_law m × left_right_commute_law m.

Definition bimodule (A B : enriched_precat Mon_V) := ∑ m : bimodule_data A B, bimodule_law m.

Definition make_bimodule {A B : enriched_precat Mon_V} bmd l : bimodule A B := (bmd,, l).

Definition bimodule_data_from_bimodule {A B : enriched_precat Mon_V} (m : bimodule A B) : bimodule_data A B := pr1 m.
Coercion bimodule_data_from_bimodule : bimodule >-> bimodule_data.

Definition left_action_from_bimodule {A B : enriched_precat Mon_V} (bm : bimodule A B) := bimodule_data_left_action bm.

Definition right_action_from_bimodule {A B : enriched_precat Mon_V} (bm : bimodule A B) := bimodule_data_right_action bm.

Definition bimodule_eq {A B : enriched_precat Mon_V} {m n : bimodule A B} : bimodule_data_from_bimodule m = bimodule_data_from_bimodule n -> m = n.
Proof.
  intro H.
  use total2_paths_b.
  - assumption.
  - apply proofirrelevance.
    repeat apply isapropdirprod;repeat (apply impred_isaprop; intro); repeat (apply impred_isaprop; intro); apply homset_property.
Defined.

Definition bimodule_left_id {A B : enriched_precat Mon_V} (m : bimodule A B) : left_id_law m := pr12 m.

Definition bimodule_left_comp {A B : enriched_precat Mon_V} (m : bimodule A B) : left_comp_law m := pr122 m.

Definition bimodule_right_id {A B : enriched_precat Mon_V} (m : bimodule A B) : right_id_law m := pr1 (pr222 m).

Definition bimodule_right_comp {A B : enriched_precat Mon_V} (m : bimodule A B) : right_comp_law m := pr12 (pr222 m).

Definition bimodule_left_right_commute {A B : enriched_precat Mon_V} (m : bimodule A B) : left_right_commute_law m := pr22 (pr222 m).

Definition hom_bimodule (A : enriched_precat Mon_V) : bimodule A A.
Proof.
  use make_bimodule.
  - use make_bimodule_data.
    + apply enriched_cat_mor.
    + intros a a' b.
      apply enriched_cat_comp.
    + intros a b b'.
      apply enriched_cat_comp.
  - repeat split.
    + intros a b.
      apply enriched_id_left.
    + intros a a' a'' b.
      rewrite assoc'.
      apply enriched_assoc.
    + intros a b.
      apply enriched_id_right.
    + intros a b'' b' b.
      apply pathsinv0.
      rewrite assoc'.
      apply enriched_assoc.
    + intros a a' b b'.
      rewrite assoc'.
      apply enriched_assoc.
Defined.

Section Bimodule_Functor_Composition.

Definition bimodule_functor_right_composition {A B B' : enriched_precat Mon_V} (m : bimodule A B) (F : enriched_functor B' B) : bimodule A B'.
Proof.
  use make_bimodule.
  - use make_bimodule_data.
    + intros b a.
      exact (m (F b) a).
    + intros a a' b.
      simpl.
      apply (left_action_from_bimodule m).
    + intros b a a'.
      exact ((id _ #⊗ enriched_functor_on_morphisms F _ _) · right_action_from_bimodule m _ _ _).
  - repeat split.
    + intros a b.
      apply bimodule_left_id.
    + intros a a' a'' b.
      apply bimodule_left_comp.
    + intros a b.
      cbn.
      rewrite assoc.
      rewrite <- (functor_comp tensor).
      change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
      rewrite id_left.
      rewrite (enriched_functor_on_identity F).
      apply bimodule_right_id.
    + intros a b'' b' b.
      cbn.
      rewrite !assoc.
      rewrite (assoc' _ _ (#tensor _)).
      rewrite <- (functor_comp tensor).
      change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
      rewrite (enriched_functor_on_comp F).
      change (?x · ?y #, ?z · ?w) with ((x #, z) · (y #, w)).
      rewrite (functor_comp tensor).
      rewrite assoc.
      etrans.
      {
        do 2 apply cancel_postcomposition.
        apply pathsinv0.
        apply nat_trans_ax_α.
      }
      etrans.
      {
        rewrite !assoc'.
        apply cancel_precomposition.
        rewrite assoc.
        apply bimodule_right_comp.
      }
      rewrite assoc.
      apply cancel_postcomposition.
      rewrite <- !(functor_comp tensor).
      change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
      rewrite id_left, !id_right.
      reflexivity.
    + intros a a' b b'.
      cbn.
      rewrite !assoc.
      rewrite (bifunctor_on_morphisms_comm tensor).
      rewrite (bifunctor_comp_right tensor).
      rewrite assoc.
      apply pathsinv0.
      etrans.
      {
        do 2 apply cancel_postcomposition.
        apply pathsinv0.
        apply nat_trans_ax_α.
      }
      rewrite (functor_id tensor).
      rewrite !assoc'.
      apply cancel_precomposition.
      rewrite !assoc.
      apply pathsinv0.
      apply bimodule_left_right_commute.
Defined.

Definition bimodule_functor_left_composition {A A' B : enriched_precat Mon_V} (m : bimodule A B) (F : enriched_functor A' A) : bimodule A' B.
Proof.
  use make_bimodule.
  - use make_bimodule_data.
    + intros b a.
      exact (m b (F a)).
    + intros a a' b.
      exact ((enriched_functor_on_morphisms F _ _ #⊗ id _) · left_action_from_bimodule m _ _ _).
    + intros a b' b.
      apply (right_action_from_bimodule m).
  - repeat split.
    + intros a b.
      cbn.
      rewrite assoc.
      rewrite <- (functor_comp tensor).
      change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
      rewrite (enriched_functor_on_identity F).
      rewrite id_left.
      apply bimodule_left_id.
    + intros a a' a'' b.
      cbn.
      rewrite !assoc.
      rewrite <- (functor_comp tensor).
      change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
      rewrite enriched_functor_on_comp.
      change (?x · ?y #, ?z · ?w) with ((x #, z) · (y #, w)).
      rewrite (functor_comp tensor).
      rewrite assoc'.
      rewrite bimodule_left_comp.
      rewrite (bifunctor_comp_right tensor).
      rewrite !assoc.
      apply cancel_postcomposition.
      etrans.
      {
        apply cancel_postcomposition.
        apply nat_trans_ax_α.
      }
      rewrite !assoc'.
      apply cancel_precomposition.
      rewrite <- (bifunctor_on_morphisms_comm tensor).
      rewrite assoc.
      apply cancel_postcomposition.
      rewrite <- (functor_comp tensor).
      change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
      rewrite id_left, id_right.
      reflexivity.
    + intros a b.
      apply bimodule_right_id.
    + intros a b'' b' b.
      apply bimodule_right_comp.
    + intros a a' b b'.
      cbn.
      rewrite assoc.
      rewrite (assoc' _ _ (#tensor _)).
      rewrite <- (bifunctor_on_morphisms_comm tensor).
      rewrite assoc.
      rewrite <- (functor_id tensor).
      rewrite (bifunctor_comp_left tensor).
      apply pathsinv0.
      etrans.
      {
        do 2 apply cancel_postcomposition.
        apply pathsinv0.
        apply nat_trans_ax_α.
      }
      rewrite !assoc'.
      apply cancel_precomposition.
      rewrite assoc.
      apply pathsinv0.
      apply bimodule_left_right_commute.
Defined.

(*
Notation "m ▻ F" := (bimodule_functor_right_composition m F) (at level 60).
Check fun m F' F => m ▻ F ▻ F'.

Notation "F ◅ m" := (bimodule_functor_left_composition m F) (at level 60).
Check fun m F' F => F' ◅ (F ◅ m).
*)

Lemma bimodule_functor_left_right_composition_commute {A A' B B' : enriched_precat Mon_V} (m : bimodule A B) (F : enriched_functor A' A) (G : enriched_functor B' B) : bimodule_functor_right_composition (bimodule_functor_left_composition m F) G = bimodule_functor_left_composition (bimodule_functor_right_composition m G) F.
Proof.
  use bimodule_eq.
  reflexivity.
Defined.

Lemma bimodule_functor_left_left_composition {A A' A'' B : enriched_precat Mon_V} (m : bimodule A B) (F : enriched_functor A'' A') (G : enriched_functor A' A) : bimodule_functor_left_composition (bimodule_functor_left_composition m G) F = bimodule_functor_left_composition m (enriched_functor_comp F G).
Proof.
  use bimodule_eq.
  use total2_paths_f.
  - reflexivity.
  - apply dirprod_paths; cbn.
    + apply funextsec; intro a.
      apply funextsec; intro a'.
      apply funextsec; intro b.
      rewrite (bifunctor_comp_left tensor).
      apply assoc.
    + reflexivity.
Defined.

Lemma bimodule_functor_right_right_composition {A B B' B'' : enriched_precat Mon_V} (m : bimodule A B) (F : enriched_functor B'' B') (G : enriched_functor B' B) : bimodule_functor_right_composition (bimodule_functor_right_composition m G) F = bimodule_functor_right_composition m (enriched_functor_comp F G).
Proof.
  use bimodule_eq.
  use total2_paths_f.
  - reflexivity.
  - apply dirprod_paths; cbn.
    + reflexivity.
    + apply funextsec; intro b.
      apply funextsec; intro a.
      apply funextsec; intro a'.
      rewrite (bifunctor_comp_right tensor).
      apply assoc.
Defined.

End Bimodule_Functor_Composition.

Section Morphism.

Definition bimodule_morphism {A B : enriched_precat Mon_V} (m m' : bimodule A B) := ∑ (f : ∏ (b : B) (a : A), m b a --> m' b a), (∏ (a a' : A) (b : B), (id _ #⊗ f b a) · left_action_from_bimodule m' _ _ _ = left_action_from_bimodule m _ _ _ · f b a') × (∏ (a : A) (b' b : B), (f b a #⊗ id _) · right_action_from_bimodule m' _ _ _ = right_action_from_bimodule m _ _ _ · f b' a).

Definition funclass_from_bimodule_morphism {A B : enriched_precat Mon_V} {m m' : bimodule A B} (f : bimodule_morphism m m') : ∏ (b : B) (a : A), m b a --> m' b a := pr1 f.
Coercion funclass_from_bimodule_morphism : bimodule_morphism >-> Funclass.

Definition bimodule_morphism_left_law {A B : enriched_precat Mon_V} {m m' : bimodule A B} (f : bimodule_morphism m m') : ∏ (a a' : A) (b : B), (id _ #⊗ f b a) · left_action_from_bimodule m' _ _ _ = left_action_from_bimodule m _ _ _ · f b a' := pr12 f.

Definition bimodule_morphism_right_law {A B : enriched_precat Mon_V} {m m' : bimodule A B} (f : bimodule_morphism m m') : ∏ (a : A) (b' b : B), (f b a #⊗ id _) · right_action_from_bimodule m' _ _ _ = right_action_from_bimodule m _ _ _ · f b' a := pr22 f.

Definition make_bimodule_morphism {A B : enriched_precat Mon_V} {m m' : bimodule A B} f l r : bimodule_morphism m m' := (f,, (l,, r)).

Definition bimodule_morphism_eq {A B : enriched_precat Mon_V} {m m' : bimodule A B} (f g : bimodule_morphism m m') : (∏ (b : B) (a : A), f b a = g b a) -> f = g.
Proof.
  intro H.
  use total2_paths_b.
  - apply funextsec.
    intro b.
    apply funextsec.
    intro a.
    apply H.
  - apply proofirrelevance.
    apply isapropdirprod; repeat (apply impred_isaprop; intro);apply homset_property.
Defined.

End Morphism.

Section Category_Of_Bimodules.

Definition bimodule_morphism_ident {A B : enriched_precat Mon_V} (m : bimodule A B) : bimodule_morphism m m.
Proof.
  use make_bimodule_morphism.
  - intros b a.
    exact (id _).
  - intros a a' b.
    rewrite (functor_id tensor).
    rewrite id_right.
    apply id_left.
  - intros a b' b.
    rewrite (functor_id tensor).
    rewrite id_right.
    apply id_left.
Defined.

Definition bimodule_morphism_composite {A B : enriched_precat Mon_V} {m m' m'' : bimodule A B} (f : bimodule_morphism m m') (g : bimodule_morphism m' m'') : bimodule_morphism m m''.
Proof.
  use make_bimodule_morphism.
  - intros b a.
    exact (f b a · g b a).
  - intros a a' b.
    cbn.
    rewrite assoc.
    rewrite <- (bimodule_morphism_left_law f).
    rewrite assoc'.
    rewrite <- (bimodule_morphism_left_law g).
    rewrite assoc.
    rewrite <- functor_comp.
    change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
    rewrite id_left.
    reflexivity.
  - intros a b' b.
    rewrite assoc.
    rewrite <- (bimodule_morphism_right_law f).
    rewrite assoc'.
    rewrite <- (bimodule_morphism_right_law g).
    rewrite assoc.
    rewrite <- functor_comp.
    change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
    rewrite id_left.
    reflexivity.
Defined.

Definition bimodule_cat (A B : enriched_precat Mon_V) : category.
Proof.
  use make_category.
  - use make_precategory.
    + use make_precategory_data.
      * use make_precategory_ob_mor.
        exact (bimodule A B).
        exact bimodule_morphism.
      * intro c.
        exact (bimodule_morphism_ident c).
      * intros a b c f g.
        exact (bimodule_morphism_composite f g).
    + repeat split; intros; apply bimodule_morphism_eq; intros; simpl.
      * apply id_left.
      * apply id_right.
      * apply assoc.
      * apply assoc'.
  - simpl.
    intros a b.
    simpl. (* isaset_bimodule_morphism *)
    apply isaset_total2.
    + apply impred_isaset.
      intro.
      apply impred_isaset.
      intro.
      apply homset_property.
    + intro.
      apply isasetaprop.
      apply isapropdirprod; repeat (apply impred_isaprop; intro);apply homset_property.
Defined.

End Category_Of_Bimodules.

Section Bimorphism.

Definition bimodule_bimorphism_data {A B C : enriched_precat Mon_V} (m : bimodule A B) (n : bimodule B C) (p : bimodule A C) := ∏ (a : A) (b : B) (c : C), m b a ⊗ n c b --> p c a.

(* TODO *)
Local Definition left_law {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} (f : bimodule_bimorphism_data m n p) := ∏ (a a' : A) (b : B) (c : C), (left_action_from_bimodule m a a' b #⊗ id _) · f a' b c = α ((_, _), _) · (id (enriched_cat_mor _ _) #⊗ f a b c) · left_action_from_bimodule p _ _ _.

Local Definition middle_law {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} (f : bimodule_bimorphism_data m n p) := ∏ (a : A) (b b' : B) (c : C), (right_action_from_bimodule m a b' b #⊗ id _) · f a b c = α ((_, _), _) · (id (m _ _) #⊗ left_action_from_bimodule n b b' c) · f a b' c.

Local Definition right_law {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} (f : bimodule_bimorphism_data m n p) := ∏ (a : A) (b : B) (c c' : C), α ((_, _), _) · (id (m _ _) #⊗ right_action_from_bimodule n b c c') · f a b c' = (f a b c #⊗ id _) · right_action_from_bimodule p a c c'.

Local Definition bimodule_bimorphism_law {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} (f : bimodule_bimorphism_data m n p) := left_law f × middle_law f × right_law f.

Definition bimodule_bimorphism {A B C : enriched_precat Mon_V} (m : bimodule A B) (n : bimodule B C) (p : bimodule A C) := ∑ f : bimodule_bimorphism_data m n p, bimodule_bimorphism_law f.

Definition funclass_from_bimodule_bimorphism {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} (f : bimodule_bimorphism m n p) : ∏ (a : A) (b : B) (c : C), m b a ⊗ n c b --> p c a := pr1 f.
Coercion funclass_from_bimodule_bimorphism : bimodule_bimorphism >-> Funclass.

Definition bimodule_bimorphism_left_law {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} (f : bimodule_bimorphism m n p) : left_law f := pr12 f.

Definition bimodule_bimorphism_middle_law {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} (f : bimodule_bimorphism m n p) : middle_law f := pr122 f.

Definition bimodule_bimorphism_right_law {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} (f : bimodule_bimorphism m n p) : right_law f := pr222 f.

Definition make_bimodule_bimorphism {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} f a b c : bimodule_bimorphism m n p := (f,, (a,, (b,, c))).

Lemma bimodule_bimorphism_eq {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} {f g : bimodule_bimorphism m n p} : (∏ (a : A) (b : B) (c : C), f a b c = g a b c) -> f = g.
Proof.
  intro H.
  use total2_paths_b.
  - do 3 (apply funextsec; intro).
    apply H.
  - apply proofirrelevance. (* isaprop_module_bimorphism_law *)
    repeat apply isapropdirprod; repeat (apply impred_isaprop; intro); apply homset_property.
Defined.

End Bimorphism.

Section Tensor_Hom.

Definition isaset_bimodule_bimorphism {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p : bimodule A C} : isaset (bimodule_bimorphism m n p).
Proof.
  use isaset_total2.
  - do 3 (apply impred_isaset; intro).
    apply homset_property.
  - intro.
    apply isasetaprop.
    repeat apply isapropdirprod; repeat (apply impred_isaprop; intro); apply homset_property.
Defined.

Definition bimodule_bimorphism_postcompose {A B C : enriched_precat Mon_V} {m : bimodule A B} {n : bimodule B C} {p p' : bimodule A C} (f : bimodule_bimorphism m n p) (g : bimodule_morphism p p') : bimodule_bimorphism m n p'.
Proof.
  use make_bimodule_bimorphism.
  - intros a b c.
    exact (f a b c · g c a).
  - intros b c a a'.
    simpl.
    rewrite assoc.
    etrans.
    {
      apply cancel_postcomposition.
      apply bimodule_bimorphism_left_law.
    }
    rewrite !assoc'.
    apply cancel_precomposition.
    rewrite <- (bimodule_morphism_left_law g).
    rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    {
      apply pathsinv0.
      apply (functor_comp tensor).
    }
    change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
    rewrite id_left.
    reflexivity.
  - intros a c b b'.
    rewrite !assoc.
    rewrite (cancel_postcomposition _ _ _ (bimodule_bimorphism_middle_law f a c b b')).
    reflexivity.
  - intros a b c c'.
    simpl.
    rewrite assoc.
    etrans.
    {
      apply cancel_postcomposition.
      apply bimodule_bimorphism_right_law.
    }
    rewrite assoc'.
    rewrite <- (bimodule_morphism_right_law g).
    rewrite assoc.
    rewrite <- (functor_comp tensor).
    change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
    rewrite id_left.
    reflexivity.
Defined.

Definition bimorphism_tensor_functor {A B C : enriched_precat Mon_V} (m : bimodule A B) (n : bimodule B C) : [bimodule_cat A C,HSET].
Proof.
  use make_functor.
  - use make_functor_data.
    + intro p.
      exists (bimodule_bimorphism m n p).
      apply isaset_bimodule_bimorphism.
    + simpl.
      intros p p' f g.
      simpl.
      exact (bimodule_bimorphism_postcompose g f).
  - split.
    + intro p.
      simpl.
      apply funextsec.
      intro f.
      apply bimodule_bimorphism_eq.
      intros a b c.
      simpl.
      apply id_right.
    + intros p p' p'' f g.
      simpl.
      apply funextsec.
      intro h.
      apply bimodule_bimorphism_eq.
      intros a b c.
      simpl.
      apply assoc.
Defined.

Definition bimodule_tensor {A B C : enriched_precat Mon_V} (m : bimodule A B) (n : bimodule B C) := Representation (bimorphism_tensor_functor m n : [(bimodule_cat A C)^op^op, SET]).

Definition exhibits_tensor {A B C : enriched_precat Mon_V} (m : bimodule A B) (n : bimodule B C) {p : bimodule A C} (f : bimodule_bimorphism m n p) := @isUniversal _ (bimorphism_tensor_functor m n : [(bimodule_cat A C)^op^op, SET]) p f.

Definition bimodule_bimorphism_precompose {A B C : enriched_precat Mon_V} {m m' : bimodule A B} {n n' : bimodule B C} {p : bimodule A C} (f : bimodule_morphism m' m) (g : bimodule_morphism n' n) (h : bimodule_bimorphism m n p) : bimodule_bimorphism m' n' p.
Proof.
  use make_bimodule_bimorphism.
  - intros a b c.
    exact ((f b a #⊗ g c b) · h a b c).
  - intros a a' b c.
    rewrite assoc.
    rewrite <- (functor_comp tensor).
    change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
    rewrite <- (bimodule_morphism_left_law f).
    rewrite (pathscomp0 (id_left _) (! id_right _)).
    change (?x · ?y #, ?z · ?w) with ((x #, z) · (y #, w)).
    rewrite (functor_comp tensor).
    rewrite (bifunctor_comp_right tensor).
    rewrite assoc.
    etrans.
    {
      rewrite assoc'.
      apply cancel_precomposition.
      apply (bimodule_bimorphism_left_law h a a' b c).
    }
    rewrite !assoc.
    do 2 apply cancel_postcomposition.
    apply nat_trans_ax_α.
  - intros a b b' c.
    rewrite assoc.
    rewrite <- (functor_comp tensor).
    change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
    rewrite <- (bimodule_morphism_right_law f).
    rewrite (pathscomp0 (id_left _) (! id_right _)).
    change (?x · ?y #, ?z · ?w) with ((x #, z) · (y #, w)).
    rewrite (functor_comp tensor).
    etrans.
    {
      rewrite assoc'.
      apply cancel_precomposition.
      apply (bimodule_bimorphism_middle_law h a b b' c).
    }
    rewrite !assoc.
    apply cancel_postcomposition.
    etrans.
    {
      apply cancel_postcomposition.
      apply nat_trans_ax_α.
    }
    rewrite !assoc'.
    apply cancel_precomposition.
    cbn.
    rewrite <- !(functor_comp tensor).
    change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
    rewrite id_left, id_right.
    apply (maponpaths (λ f, # tensor (_ #, f))).
    apply (bimodule_morphism_left_law g b b' c).
  - intros a b c c'.
    rewrite (bifunctor_comp_left tensor).
    apply pathsinv0.
    etrans.
    {
      rewrite assoc'.
      apply cancel_precomposition.
      apply pathsinv0.
      apply (bimodule_bimorphism_right_law h a b c c').
    }
    rewrite !assoc.
    apply cancel_postcomposition.
    etrans.
    {
      apply cancel_postcomposition.
      apply nat_trans_ax_α.
    }
    rewrite !assoc'.
    apply cancel_precomposition.
    cbn.
    rewrite <- !(functor_comp tensor).
    change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
    rewrite id_left, id_right.
    apply (maponpaths (λ f, #tensor (_ #, f))).
    apply (bimodule_morphism_right_law g b c' c).
Defined.

Definition bimorphism_right_hom_functor {A B C : enriched_precat Mon_V} (n : bimodule B C) (p : bimodule A C) : [(bimodule_cat A B)^op,HSET].
Proof.
  use make_functor.
  - use make_functor_data.
    + intro m.
      exists (bimodule_bimorphism m n p).
      apply isaset_bimodule_bimorphism.
    + simpl.
      intros m m' f g.
      exact (bimodule_bimorphism_precompose f (bimodule_morphism_ident n) g).
  - split.
    + intro m.
      cbn.
      apply funextsec.
      intro f.
      apply bimodule_bimorphism_eq.
      intros a b c.
      simpl.
      rewrite (functor_id tensor).
      apply id_left.
    + intros m m' m'' f g.
      apply funextsec.
      cbn.
      intro h.
      apply bimodule_bimorphism_eq.
      intros a b c.
      simpl.
      rewrite assoc.
      rewrite <- (functor_comp tensor).
      change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
      rewrite id_left.
      reflexivity.
Defined.

Definition bimodule_right_hom {A B C : enriched_precat Mon_V} (n : bimodule B C) (p : bimodule A C) := Representation (bimorphism_right_hom_functor n p).

Definition exhibits_right_hom {A B C : enriched_precat Mon_V} {m : bimodule A B} (n : bimodule B C) (p : bimodule A C) (f : bimodule_bimorphism m n p) := @isUniversal _ (bimorphism_right_hom_functor n p) m f.

Definition bimorphism_left_hom_functor {A B C : enriched_precat Mon_V} (m : bimodule A B) (p : bimodule A C) : [(bimodule_cat B C)^op,HSET].
Proof.
  use make_functor.
  - use make_functor_data.
    + intro n.
      exists (bimodule_bimorphism m n p).
      apply isaset_bimodule_bimorphism.
    + simpl.
      intros n n' f g.
      exact (bimodule_bimorphism_precompose (bimodule_morphism_ident m) f g).
  - split.
    + intro n.
      simpl.
      apply funextsec.
      intro f.
      apply bimodule_bimorphism_eq.
      intros a b c.
      simpl.
      rewrite (functor_id tensor).
      apply id_left.
    + intros n n' n'' f g.
      apply funextsec.
      simpl.
      intro h.
      apply bimodule_bimorphism_eq.
      intros a b c.
      simpl.
      rewrite assoc.
      rewrite <- (functor_comp tensor).
      change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
      rewrite id_left.
      reflexivity.
Defined.

Definition bimodule_left_hom {A B C : enriched_precat Mon_V} (m : bimodule A B) (p : bimodule A C) := Representation (bimorphism_left_hom_functor m p).

Definition exhibits_left_hom {A B C : enriched_precat Mon_V} (m : bimodule A B) {n : bimodule B C} (p : bimodule A C) (f : bimodule_bimorphism m n p) := @isUniversal _ (bimorphism_left_hom_functor m p) n f.

End Tensor_Hom.

End Bimodule.