Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.

Section MonadLifting.

Context {C : category} (T : Monad C).

Definition disp_monad_data (D : disp_cat C) := ∑ F : disp_functor T D D, disp_nat_trans (Monads.μ T) (disp_functor_composite F F) F × disp_nat_trans (Monads.η T) (disp_functor_identity D) F.

Coercion disp_functor_from_disp_monad_data {D : disp_cat C} (TT : disp_monad_data D) : disp_functor T D D := pr1 TT.

Definition μ {D : disp_cat C} (TT : disp_monad_data D) : disp_nat_trans (Monads.μ T) (disp_functor_composite TT TT) TT := pr12 TT.
Definition η {D : disp_cat C} (TT : disp_monad_data D) : disp_nat_trans (Monads.η T) (disp_functor_identity D) TT := pr22 TT.

Definition make_disp_monad_data {D : disp_cat C} f eta mu : disp_monad_data D := (f,, (eta,, mu)).

Definition total_monad_data {D : disp_cat C} (m : disp_monad_data D) : Monad_data (total_category D).
Proof.
  use tpair. (* make Monad_data *)
  exists (total_functor m).
  exact (total_nat_trans (μ m)).
  exact (total_nat_trans (η m)).
Defined.

Definition disp_monad_laws {D : disp_cat C} (TT : disp_monad_data D) : UU :=
    (
      (∏ (c : C) (d : D c), η TT _ (TT c d) ;; μ TT _ d = transportb _ (Monad_law1 _) (id_disp (TT c d)))
        ×
        (∏ (c : C) (d : D c), # TT (η TT c d) ;; μ TT _ d = transportb _ (Monad_law2 _) (id_disp (TT c d)))
        ×
        (∏ (c : C) (d : D c), # TT (μ TT c d) ;; μ TT _ d = transportb _ (Monad_law3 _) (μ TT _ (TT c d) ;; μ TT c d))
    )%mor_disp.


Definition disp_monad (D : disp_cat C) : UU := ∑ TT : disp_monad_data D, disp_monad_laws TT.

Coercion disp_monad_data_from_disp_monad {D : disp_cat C} (TT : disp_monad D) : disp_monad_data D := pr1 TT.

Definition disp_monad_law1 {D : disp_cat C} (TT : disp_monad D) : (∏ (c : C) (d : D c), η TT _ (TT c d) ;; μ TT _ d = transportb _ (Monad_law1 _) (id_disp (TT c d)))%mor_disp := pr12 TT.
Definition disp_monad_law2 {D : disp_cat C} (TT : disp_monad D) : (∏ (c : C) (d : D c), # TT (η TT c d) ;; μ TT _ d = transportb _ (Monad_law2 _) (id_disp (TT c d)))%mor_disp := pr122 TT.
Definition disp_monad_law3 {D : disp_cat C} (TT : disp_monad D) : (∏ (c : C) (d : D c), # TT (μ TT c d) ;; μ TT _ d = transportb _ (Monad_law3 _) (μ TT _ (TT c d) ;; μ TT c d))%mor_disp := pr222 TT.

Definition make_disp_monad {D : disp_cat C} (data : disp_monad_data D) (law : disp_monad_laws data) : disp_monad D := (data,, law).

Lemma total_monad_laws {D : disp_cat C} (TT : disp_monad D) : Monad_laws (total_monad_data TT).
Proof.
  repeat split.
  - intros.
  use total2_paths2_b.
  + apply Monad_law1.
  + apply disp_monad_law1.
- intros.
  use total2_paths2_b.
  + apply Monad_law2.
  + apply disp_monad_law2.
- intros.
  use total2_paths2_b.
  + apply Monad_law3.
  + apply disp_monad_law3.
Qed.

Definition total_monad {D : disp_cat C} (TT : disp_monad D) : Monad (total_category D).
Proof.
  exists (total_monad_data TT).
  apply total_monad_laws.
Defined.

Definition disp_monad_eq {D : disp_cat C} (TT TT' : disp_monad D) : disp_monad_data_from_disp_monad TT = disp_monad_data_from_disp_monad TT' -> TT = TT'.
Proof.
  intro.
  apply subtypePath.
  - intro.
    apply isapropdirprod.
    + do 2 (apply impred_isaprop;intro).
      apply homsets_disp.
    + apply isapropdirprod;do 2 (apply impred_isaprop;intro);apply homsets_disp.
  - assumption.
Defined.

Definition fibered_disp_monad (D : disp_cat C) : UU := ∑ TT : disp_monad D, is_cartesian_disp_functor TT.

Coercion disp_monad_from_fibered_disp_monad {D : disp_cat C} (TT : fibered_disp_monad D) : disp_monad D := pr1 TT.

Definition fibered_disp_monad_eq {D : disp_cat C} (TT TT' : fibered_disp_monad D) : disp_monad_from_fibered_disp_monad TT = disp_monad_from_fibered_disp_monad TT' -> TT = TT'.
Proof.
  intro.
  apply subtypePath.
  - intro.
    apply impred_isaprop.
    intro.
    do 6 (apply impred_isaprop;intro).
    apply isaprop_is_cartesian.
  - assumption.
Defined.

Definition cartesian_disp_monad (D : disp_cat C) : UU := ∑ TT : fibered_disp_monad D, (∏ (c : C) (d : D c), is_cartesian (η TT c d)) × (∏ (c : C) (d : D c), is_cartesian (μ TT c d)).

Coercion fibered_disp_monad_from_cartesian_disp_monad {D : disp_cat C} (TT : cartesian_disp_monad D) : fibered_disp_monad D := pr1 TT.

Definition is_cartesian_eta {D : disp_cat C} (TT : cartesian_disp_monad D) := pr12 TT.
Definition is_cartesian_mu {D : disp_cat C} (TT : cartesian_disp_monad D) := pr22 TT.

Definition cartesian_disp_monad_eq {D : disp_cat C} (TT TT' : cartesian_disp_monad D) : fibered_disp_monad_from_cartesian_disp_monad TT = fibered_disp_monad_from_cartesian_disp_monad TT' -> TT = TT'.
Proof.
  intro.
  apply subtypePath.
  - intro.
    apply isapropdirprod;apply impred_isaprop;intro;apply impred_isaprop;intro;apply isaprop_is_cartesian.
  - assumption.
Defined.

End MonadLifting.

Local Hint Rewrite @mor_disp_transportf_prewhisker @mor_disp_transportf_postwhisker @disp_functor_transportf @transport_f_f @id_left_disp @id_right_disp @assoc_disp @disp_functor_id @disp_functor_comp : disp_cat_hint.

Section DispMonadMor.

Definition disp_monad_mor_laws {C : category} {D : disp_cat C} {S T : Monad C} (m : Monad_Mor S T) (SS : disp_monad S D) (TT : disp_monad T D) (a : disp_nat_trans m SS TT) := (∏ (x : C) (xx : D x), (η _ SS x xx ;; a x xx)%mor_disp = transportb _ (Monad_Mor_η m _) (η _ TT x xx)) × (∏ (x : C) (xx : D x), μ _ SS x xx ;; a x xx = transportb _ (Monad_Mor_μ m _) (a _ _ ;; # TT (a _ _) ;; μ _ TT _ _))%mor_disp.

Definition disp_monad_mor {C : category} {D : disp_cat C} {S T : Monad C} (m : Monad_Mor S T) (SS : disp_monad S D) (TT : disp_monad T D) := ∑ a : disp_nat_trans m SS TT, disp_monad_mor_laws m SS TT a.

Definition make_disp_monad_mor {C : category} {D : disp_cat C} {S T : Monad C} (m : Monad_Mor S T) (SS : disp_monad S D) (TT : disp_monad T D) a laws : disp_monad_mor m SS TT := (a,, laws).

Definition disp_nat_trans_from_disp_monad_mor {C : category} {D : disp_cat C} {S T : Monad C} {m : Monad_Mor S T} {SS : disp_monad S D} {TT : disp_monad T D} (mm : disp_monad_mor m SS TT) : disp_nat_trans m SS TT := pr1 mm.
Coercion disp_nat_trans_from_disp_monad_mor : disp_monad_mor >-> disp_nat_trans.

Definition disp_monad_mor_η {C : category} {D : disp_cat C} {S T : Monad C} {m : Monad_Mor S T} {SS : disp_monad S D} {TT : disp_monad T D} (mm : disp_monad_mor m SS TT) : ∏ (x : C) (xx : D x), (η _ SS x xx ;; mm x xx)%mor_disp = transportb _ (Monad_Mor_η m _) (η _ TT x xx) := pr12 mm.

Definition disp_monad_mor_μ {C : category} {D : disp_cat C} {S T : Monad C} {m : Monad_Mor S T} {SS : disp_monad S D} {TT : disp_monad T D} (mm : disp_monad_mor m SS TT) : (∏ (x : C) (xx : D x), μ _ SS x xx ;; mm x xx = transportb _ (Monad_Mor_μ m _) (mm _ _ ;; # TT (mm _ _) ;; μ _ TT _ _))%mor_disp := pr22 mm.

Lemma disp_monad_mor_eq {C : category} {D : disp_cat C} {S T : Monad C} {m : Monad_Mor S T} {SS : disp_monad S D} {TT : disp_monad T D} (mm mm' : disp_monad_mor m SS TT) : (disp_nat_trans_from_disp_monad_mor mm = disp_nat_trans_from_disp_monad_mor mm') -> mm = mm'.
Proof.
  intro X.
  apply subtypePath.
  - intro.
    apply isapropdirprod;repeat (apply impred_isaprop;intro);apply homsets_disp.
  - assumption.
Defined.

Definition disp_monad_mor_identity_laws {C : category} {D : disp_cat C} {T : Monad C} (TT : disp_monad T D) : disp_monad_mor_laws (Monad_identity T) TT TT (disp_nat_trans_id TT).
Proof.
  split.
  - intros x xx.
    cbn.
    rewrite id_right_disp.
    unfold transportb.
    apply transportf_paths.
    apply homset_property.
  - intros x xx.
    cbn.
    autorewrite with disp_cat_hint using unfold transportb.
    (*rewrite id_right_disp.
    rewrite id_left_disp.
    rewrite disp_functor_id.
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite id_left_disp.
    unfold transportb.
    rewrite !transport_f_f.*)
    apply transportf_paths.
    apply homset_property.
Qed.

Definition disp_monad_mor_identity {C : category} {D : disp_cat C} {T : Monad C} (TT : disp_monad T D) : disp_monad_mor (Monad_identity T) TT TT.
Proof.
  exists (disp_nat_trans_id TT).
  apply disp_monad_mor_identity_laws.
Defined.

Definition disp_monad_mor_composite_laws {C : category} {D : disp_cat C} {S T U : Monad C} {f : Monad_Mor S T} {g : Monad_Mor T U} {SS : disp_monad S D} {TT : disp_monad T D} {UU : disp_monad U D} (ff : disp_monad_mor f SS TT) (gg : disp_monad_mor g TT UU) : disp_monad_mor_laws (Monad_composition f g) SS UU (disp_nat_trans_comp ff gg).
Proof.
  split; intros x xx; cbn.
  - rewrite assoc_disp.
    etrans.
    {
      apply maponpaths.
      eapply (maponpaths (λ x, x;;_)%mor_disp).
      apply (disp_monad_mor_η ff).
    }
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    etrans.
    {
      do 2 apply maponpaths.
      apply (disp_monad_mor_η gg).
    }
    unfold transportb.
    rewrite !transport_f_f.
    apply transportf_paths.
    apply homset_property.
  - rewrite assoc_disp.
    etrans.
    {
      apply maponpaths.
      eapply (maponpaths (λ x, x;;_)%mor_disp).
      apply (disp_monad_mor_μ ff).
    }
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    etrans.
    {
      do 3 apply maponpaths.
      eapply (maponpaths (λ x, _;;x)%mor_disp).
      apply (disp_monad_mor_μ gg).
    }
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite assoc_disp_var.
    do 2 rewrite (assoc_disp (# TT (ff x xx))).
    rewrite (disp_nat_trans_ax gg).
    autorewrite with disp_cat_hint using unfold transportb.
    (*unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite disp_functor_comp.
    rewrite !assoc_disp.
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !assoc_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.*)
    apply transportf_paths.
    apply homset_property.
Qed.

Definition disp_monad_mor_composite {C : category} {D : disp_cat C} {S T U : Monad C} {f : Monad_Mor S T} {g : Monad_Mor T U} {SS : disp_monad S D} {TT : disp_monad T D} {UU : disp_monad U D} (ff : disp_monad_mor f SS TT) (gg : disp_monad_mor g TT UU) : disp_monad_mor (Monad_composition f g) SS UU.
Proof.
  exists (disp_nat_trans_comp ff gg).
  apply disp_monad_mor_composite_laws.
Defined.

End DispMonadMor.

Lemma transportf_disp_monad_mor {C : category} {D : disp_cat C} {S T : Monad C} {f g : Monad_Mor S T} {SS : disp_monad S D} {TT : disp_monad T D} (ff : disp_monad_mor f SS TT) (e : f = g) {x : C} (xx : D x) : transportf (λ h, disp_monad_mor h SS TT) e ff x xx = transportf (mor_disp (SS x xx) (TT x xx)) (maponpaths (λ h : Monad_Mor S T, h x) e) (ff x xx).
Proof.
  induction e.
  reflexivity.
Defined.

Lemma transportf_disp_nat_trans {C : category} {D : disp_cat C} {F G : functor C C} {a b : nat_trans F G} {FF : disp_functor F D D} {GG : disp_functor G D D} (aa : disp_nat_trans a FF GG) (e : a = b) {x : C} (xx : D x) : transportf (λ h, disp_nat_trans h FF GG) e aa x xx = transportf (mor_disp (FF x xx) (GG x xx)) (maponpaths (λ h : nat_trans F G, h x) e) (aa x xx).
Proof.
  induction e.
  reflexivity.
Defined.

Section DispMonadDispCat.

(* TODO move to another place *)
Lemma is_cartesian_componentwise {B C : category} {D : disp_cat B} {E : disp_cat C} {F G : functor B C} {a : nat_trans F G} {FF : disp_functor_cat B C D E F} {GG : disp_functor_cat B C D E G} (aa : FF -->[a] GG) : (∏ (x : B) (xx : D x), is_cartesian ((aa : disp_nat_trans _ _ _) x xx)) -> is_cartesian aa.
Proof.
  intro X.
  intros H b HH cc.
  use unique_exists.
  cbn in *.
  - use tpair.
    + intros x xx.
      exact (cartesian_factorisation (X x xx) (b x) (cc x xx)).
    + intros x y f xx yy ff.
      use (cartesian_factorisation_unique (X y yy)).
      rewrite assoc_disp_var.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite (disp_nat_trans_ax aa).
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite assoc_disp.
      rewrite cartesian_factorisation_commutes.
      etrans.
      {
        apply maponpaths.
        apply (disp_nat_trans_ax cc).
      }
      unfold transportb.
      repeat rewrite transport_f_f.
      apply transportf_paths.
      apply homset_property.
  - apply disp_nat_trans_eq.
    intros x xx.
    cbn.
    apply cartesian_factorisation_commutes.
  - intro.
    apply isaset_disp_nat_trans.
  - intros bb X0.
    apply disp_nat_trans_eq.
    intros x xx.
    cbn.
    use (cartesian_factorisation_unique (X x xx)).
    rewrite cartesian_factorisation_commutes.
    simpl in X0.
    rewrite <- X0.
    reflexivity.
Defined.

(* TODO move to another place *)
Lemma cleaving_disp_functor_cat {B C : category} {D : disp_cat B} {E : disp_cat C} (cleavingE : cleaving E) : cleaving (disp_functor_cat B C D E).
Proof.
  intros G F a GG.
  exists (cartesian_factorisation_disp_functor cleavingE GG a).
  exists (cartesian_factorisation_disp_functor_cell cleavingE GG a).
  apply is_cartesian_componentwise.
  intros x xx.
  apply cartesian_factorisation_disp_functor_cell_is_cartesian.
Defined.

(* TODO move to UniMath.CategoryTheory.Monads.Monads *)
Lemma monad_mor_η_pointfree {C : category} {S T : Monad C} (f : Monad_Mor S T) : (nat_trans_comp _ _ _ (Monads.η S) f) = (Monads.η T).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - apply Monad_Mor_η.
Defined.

Lemma monad_mor_μ_pointfree {C : category} {S T : Monad C} (f : Monad_Mor S T) : nat_trans_comp _ _ _ (Monads.μ S) f = nat_trans_comp _ _ _ (nat_trans_comp _ _ _ (whiskering.pre_whisker S f) (whiskering.post_whisker f T)) (Monads.μ T).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - apply Monad_Mor_μ.
Defined.

Context {C : category} (D : disp_cat C).

Definition disp_monad_disp_cat_data : disp_cat_data (category_Monad C).
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + intro T.
      exact (disp_monad T D).
    + cbn.
      intros S T SS TT m.
      exact (disp_monad_mor m SS TT).
  - split.
    + intros T TT.
      exact (disp_monad_mor_identity TT).
    + intros S T U f g SS TT UU.
      exact disp_monad_mor_composite.
Defined.

Lemma disp_monad_disp_cat_axioms : disp_cat_axioms (category_Monad C) disp_monad_disp_cat_data.
Proof.
  repeat split.
  - intros.
    apply disp_monad_mor_eq.
    apply disp_nat_trans_eq.
    intros.
    cbn.
    rewrite id_left_disp.
    apply pathsinv0.
    etrans.
    {
      apply (transportf_disp_monad_mor ff (! id_left f) xx0).
    }
    apply transportf_paths.
    apply homset_property.
  - intros.
    apply disp_monad_mor_eq.
    apply disp_nat_trans_eq.
    intros.
    cbn.
    rewrite id_right_disp.
    apply pathsinv0.
    etrans.
    {
      apply (transportf_disp_monad_mor ff (! id_right f) xx0).
    }
    apply transportf_paths.
    apply homset_property.
  - intros.
    apply disp_monad_mor_eq.
    apply disp_nat_trans_eq.
    intros.
    cbn.
    rewrite assoc_disp.
    apply pathsinv0.
    etrans.
    {
      apply (transportf_disp_monad_mor _ (! assoc f g h) xx0).
    }
    apply transportf_paths.
    apply homset_property.
  - intros.
    cbn.
    apply isaset_total2.
    apply isaset_disp_nat_trans.
    intro.
    apply isasetaprop;apply isapropdirprod;repeat (apply impred_isaprop; intro);apply homsets_disp.
Qed.

Definition disp_monad_disp_cat : disp_cat (category_Monad C).
Proof.
  exists disp_monad_disp_cat_data.
  apply disp_monad_disp_cat_axioms.
Defined.

End DispMonadDispCat.

Section DispMonadFibration.

Context {C : category} (D : fibration C).

Definition disp_monad_cartesian_factorization_disp_monad_data {S T : Monad C} (f : Monad_Mor S T) (TT : disp_monad T D) : disp_monad_data S D.
Proof.
  set (cl := (@cleaving_disp_functor_cat _ _ D D (cleaving_from_fibration D) (T : functor C C) (S : functor C C) (f : nat_trans _ _) (TT : disp_functor _ _ _))).
  use make_disp_monad_data.
  - exact (object_of_cartesian_lift _ _ cl).
  - use (cartesian_factorisation (cartesian_lift_is_cartesian _ _ cl) (Monads.μ S)).
    apply (transportb (@mor_disp _ (disp_functor_cat C C D D) _ _ _ _) (monad_mor_μ_pointfree f)).
    use (disp_nat_trans_comp _ (μ _ TT)).
    use (disp_nat_trans_comp _ (post_whisker_disp_nat_trans (mor_disp_of_cartesian_lift _ _ cl) TT)).
    exact (pre_whisker_disp_nat_trans (object_of_cartesian_lift _ _ cl) (mor_disp_of_cartesian_lift _ _ cl)).
  - use (cartesian_factorisation (cartesian_lift_is_cartesian _ _ cl) (Monads.η S)).
    exact (transportb (@mor_disp _ (disp_functor_cat C C D D) _ _ _ _) (monad_mor_η_pointfree f) (η _ TT)).
Defined.

Definition disp_monad_cartesian_factorization_disp_monad_laws {S T : Monad C} (f : Monad_Mor S T) (TT : disp_monad T D) : disp_monad_laws S (disp_monad_cartesian_factorization_disp_monad_data f TT).
Proof.
  repeat split; intros x xx; cbn.
  - apply (cartesian_factorisation_unique (cartesian_factorisation_disp_functor_cell_is_cartesian (cleaving_from_fibration D) TT f xx)).
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite id_left_disp.
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    cbn.
    rewrite (@transportf_disp_nat_trans _ D (S ∙ S) T _ _ (disp_functor_composite
    (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f)
    (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f)) TT _ (! monad_mor_μ_pointfree f)).
    cbn.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !assoc_disp.
    unfold transportb.
    rewrite !transport_f_f.
    rewrite mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite (@transportf_disp_nat_trans _ D (functor_identity C) T _ _ _ _ (η T TT) (! monad_mor_η_pointfree f)).
    rewrite !mor_disp_transportf_postwhisker.
    etrans.
    {
      do 2 apply maponpaths.
      eapply (maponpaths (λ h, h;;_)%mor_disp).
      apply (disp_nat_trans_ax_var (η T TT)).
    }
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite (disp_monad_law1 T TT).
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite id_right_disp.
    unfold transportb.
    rewrite !transport_f_f.
    apply transportf_paths.
    apply homset_property.
  - apply (cartesian_factorisation_unique (cartesian_factorisation_disp_functor_cell_is_cartesian (cleaving_from_fibration D) TT f xx)).
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite id_left_disp.
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    cbn.
    rewrite (@transportf_disp_nat_trans _ D (S ∙ S) T _ _ (disp_functor_composite
    (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f)
    (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f)) TT _ (! monad_mor_μ_pointfree f)).
    cbn.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !assoc_disp.
    unfold transportb.
    rewrite !transport_f_f.
    rewrite mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    rewrite (@transportf_disp_nat_trans _ D (functor_identity C) T _ _ _ _ (η T TT) (! monad_mor_η_pointfree f)).
    rewrite (assoc_disp_var _ (#TT _) (#TT _)).
    rewrite <- (disp_functor_comp_var TT).
    rewrite cartesian_factorisation_commutes.
    rewrite disp_functor_transportf.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite !transport_f_f.
    rewrite (disp_monad_law2 T TT x).
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite id_right_disp.
    unfold transportb.
    rewrite !transport_f_f.
    apply transportf_paths.
    apply homset_property.
  - apply (cartesian_factorisation_unique (cartesian_factorisation_disp_functor_cell_is_cartesian (cleaving_from_fibration D) TT f xx)).
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    rewrite !(@transportf_disp_nat_trans _ D (S ∙ S) T _ _ (disp_functor_composite
    (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f)
    (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f)) TT _ (! monad_mor_μ_pointfree f)).
    rewrite !mor_disp_transportf_prewhisker.
    cbn.
    rewrite !assoc_disp.
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    do 2 rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite (assoc_disp_var _ (#TT _) (#TT _)).
    rewrite <- (disp_functor_comp_var TT).
    rewrite cartesian_factorisation_commutes.
    autorewrite with disp_cat_hint using unfold transportb.
    (*rewrite disp_functor_transportf.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !(disp_functor_comp TT).
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite !assoc_disp.
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.*)
    rewrite assoc_disp_var.
    rewrite !transport_f_f.
    etrans.
    apply maponpaths.
    eapply (maponpaths (λ h, _;;h)%mor_disp).
    apply (disp_monad_law3 T TT).
    unfold transportb.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite assoc_disp.
    unfold transportb.
    rewrite !transport_f_f.
    etrans.
    apply maponpaths.
    eapply (maponpaths (λ h, h;;_)%mor_disp).
    rewrite assoc_disp_var.
    apply maponpaths.
    eapply (maponpaths (λ h, _;;h)%mor_disp).
    apply (disp_nat_trans_ax (μ T TT)).
    autorewrite with disp_cat_hint using unfold transportb.
    (*unfold transportb.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite assoc_disp.
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.*)
    apply transportf_paths.
    apply homset_property.
Qed.

Definition disp_monad_cartesian_factorization_disp_monad {S T : Monad C} (f : Monad_Mor S T) (TT : disp_monad T D) : disp_monad S D.
Proof.
  use make_disp_monad.
  - exact (disp_monad_cartesian_factorization_disp_monad_data f TT).
  - apply disp_monad_cartesian_factorization_disp_monad_laws.
Defined.

Definition disp_monad_cartesian_factorization_disp_monad_mor_laws {S T : Monad C} (f : Monad_Mor S T) (TT : disp_monad T D) : disp_monad_mor_laws f (disp_monad_cartesian_factorization_disp_monad f TT) TT (mor_disp_of_cartesian_lift _ _ (@cleaving_disp_functor_cat _ _ D D (cleaving_from_fibration D) (T : functor C C) (S : functor C C) (f : nat_trans _ _) (TT : disp_functor _ _ _))).
Proof.
  split.
  - intros x xx.
    cbn.
    rewrite cartesian_factorisation_commutes.
    rewrite (transportf_disp_nat_trans (η T TT) (! monad_mor_η_pointfree f)).
    apply transportf_paths.
    apply homset_property.
  - intros x xx.
    cbn.
    rewrite cartesian_factorisation_commutes.
    unfold transportb.
    rewrite (@transportf_disp_nat_trans _ D (S ∙ S) T _ _ (disp_functor_composite (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f) (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f)) TT _ (! monad_mor_μ_pointfree f)).
    apply transportf_paths.
    apply homset_property.
Qed.

Definition disp_monad_cartesian_factorization_disp_monad_mor {S T : Monad C} (f : Monad_Mor S T) (TT : disp_monad T D) : disp_monad_mor f (disp_monad_cartesian_factorization_disp_monad f TT) TT.
Proof.  
  exact (make_disp_monad_mor _ _ _ _ (disp_monad_cartesian_factorization_disp_monad_mor_laws f TT)).
Defined.

Definition disp_monad_cartesian_factorization_laws {S T : Monad C} (f : Monad_Mor S T) (TT : disp_monad T D) (U : Monad C) (g : Monad_Mor U S) (UU : disp_monad U D) (hh : disp_monad_mor (Monad_composition g f) UU TT) : disp_monad_mor_laws g UU (disp_monad_cartesian_factorization_disp_monad f TT) (cartesian_factorisation (cartesian_lift_is_cartesian _ _ (@cleaving_disp_functor_cat _ _ D D (cleaving_from_fibration D) (T : functor C C) (S : functor C C) (f : nat_trans _ _) (TT : disp_functor _ _ _))) (g : nat_trans U S) (hh : disp_nat_trans _ _ _)).
Proof.
  split.
  - intros x xx.
    cbn.
    apply (cartesian_factorisation_unique (cartesian_factorisation_disp_functor_cell_is_cartesian (cleaving_from_fibration D) TT f xx)).
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    do 2 rewrite cartesian_factorisation_commutes.
    etrans.
    {
      apply maponpaths.
      apply (disp_monad_mor_η hh x xx).
    }
    unfold transportb.
    rewrite !transport_f_f.
    rewrite (transportf_disp_nat_trans (η T TT) (! monad_mor_η_pointfree f)).
    rewrite transport_f_f.
    apply transportf_paths.
    apply homset_property.
  - intros x xx.
    apply (cartesian_factorisation_unique (cartesian_factorisation_disp_functor_cell_is_cartesian (cleaving_from_fibration D) TT f xx)).
    cbn.
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    unfold transportb.
    rewrite (@transportf_disp_nat_trans _ D (S ∙ S) T _ _ (disp_functor_composite (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f) (cartesian_factorisation_disp_functor (cleaving_from_fibration D) TT f)) TT _ (! monad_mor_μ_pointfree f)).
    rewrite !mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_prewhisker.
    cbn.
    rewrite assoc_disp.
    unfold transportb.
    rewrite !transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    rewrite (assoc_disp_var (cartesian_factorisation _ _ _)).
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite (assoc_disp_var _ (#TT _) (#TT _)).
    rewrite <- (disp_functor_comp_var TT).
    rewrite !cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    etrans.
    apply maponpaths.
    apply (disp_monad_mor_μ hh x xx).
    unfold transportb.
    rewrite !transport_f_f.
    apply transportf_paths.
    apply homset_property.
Qed.

Definition disp_monad_cartesian_factorization {S T : Monad C} (f : Monad_Mor S T) (TT : disp_monad T D) (U : Monad C) (g : Monad_Mor U S) (UU : disp_monad U D) (hh : disp_monad_mor (Monad_composition g f) UU TT) : disp_monad_mor g UU (disp_monad_cartesian_factorization_disp_monad f TT).
Proof.
  exact (make_disp_monad_mor _ _ _ _ (disp_monad_cartesian_factorization_laws f TT U g UU hh)).
Defined.

Definition disp_monad_cat_cartesian_lift {S T : Monad C} (f : Monad_Mor S T) (TT : disp_monad_disp_cat D T) : cartesian_lift TT f.
Proof.
  exists (disp_monad_cartesian_factorization_disp_monad f TT).
  exists (disp_monad_cartesian_factorization_disp_monad_mor f TT).
  intros U g UU hh.
  use unique_exists.
  - exact (disp_monad_cartesian_factorization f TT U g UU hh).
  - apply disp_monad_mor_eq.
    apply disp_nat_trans_eq.
    intros x xx.
    cbn.
    apply cartesian_factorisation_commutes.
  - intro.
    apply homsets_disp.
  - cbn.
    intros gg H.
    apply disp_monad_mor_eq.
    apply disp_nat_trans_eq.
    intros x xx.
    cbn.
    cbn in TT.
    apply (cartesian_factorisation_unique (cartesian_factorisation_disp_functor_cell_is_cartesian (cleaving_from_fibration D) TT f xx)).
    rewrite cartesian_factorisation_commutes.
    rewrite <- H.
    reflexivity.
Defined.

Definition disp_monad_fibration : fibration (category_Monad C).
Proof.
  exists (disp_monad_disp_cat D).
  intros T S f TT.
  apply disp_monad_cat_cartesian_lift.
Defined.

End DispMonadFibration.
