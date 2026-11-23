module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Development.EtaleCohomology.EtaleSheaves.Bundle009
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle017
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle016
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle020
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle013
public import Development.EtaleCohomology.CohomologicalPurity.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.EtaleCohomology.EtaleSheaves.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle337
public import Development.EtaleCohomology.EtaleSheaves.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem ded_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) [IsDedekindDomain S] :
    IsDedekindDomain R := by
  have : IsDomain R := Function.Injective.isDomain (e : R →+* S) e.injective
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv S e.symm
  have : Ring.DimensionLEOne R := Ring.DimensionLEOne.of_ringEquiv e
  have : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv e.symm
  exact { }

private theorem base_comp {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ CommRingCat.ofHom (algebraMap k C.functionField) =
      c.appLE ⊤ W le_top ≫ C.germToFunctionField W := by
  rw [← Scheme.ΓSpecIso_naturality, hgen]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, Scheme.germToFunctionField]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem pre_ne {X Y : Scheme.{0}} (u : X ⟶ Y) (hu : Surjective u) (W : Y.Opens)
    (h : (W : Set Y).Nonempty) : ((u ⁻¹ᵁ W : X.Opens) : Set X).Nonempty := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨y, rfl⟩ := hu.surj w
  exact ⟨y, hw⟩

theorem UpperTheory.isChart_affine_sections_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsChart B := by
  intro k _ _ C _ c hc _ hgen W _ hW B hB
  have hWne : (W : Set C).Nonempty := ⟨_, (Classical.arbitrary W).2⟩
  obtain ⟨hC1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve k c hc
  obtain ⟨hded, hnf⟩ := hC1 W hW hWne
  let f : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hmem : ∀ a, f a ∈ B := by
    intro a
    have : f a ∈ (B : Set C.functionField) := by
      rw [hB]; exact ⟨a, rfl⟩
    exact this
  let h : Γ(C, W) ≃+* B := RingEquiv.ofBijective
    (RingHom.codRestrict (σS := Subalgebra k C.functionField) f B hmem)
    ⟨fun a b hab => Scheme.germToFunctionField_injective C W (congrArg Subtype.val hab),
     fun b => by
      have hb : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
      rw [hB] at hb
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext ha⟩⟩
  have hh : ∀ a, (h a : C.functionField) = f a := fun a => rfl
  unfold IsChart
  refine ⟨?_, ded_of_equiv h.symm, fun hf => hnf (MulEquiv.isField hf h.toMulEquiv), ?_, ?_⟩
  · haveI : LocallyOfFiniteType c := @IsProper.toLocallyOfFiniteType _ _ _ hc.2.1
    have g0 := c.finiteType_appLE (isAffineOpen_top (Sp k)) hW le_top
    have gi : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fun y => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom y, by simp⟩)
    have g2 := (g0.comp gi).comp_surjective (g := (h : Γ(C, W) →+* B)) h.surjective
    rw [← RingHom.finiteType_algebraMap]
    convert g2
    ext x
    have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x)) (base_comp c hgen W)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← hh] at this
    simpa using this
  · have hfr := functionField_isFractionRing_of_isAffineOpen C W hW
    have := (IsFractionRing.isFractionRing_iff_of_base_ringEquiv C.functionField h).mp hfr
    have heq : ((algebraMap Γ(C, W) C.functionField).comp h.symm.toRingHom).toAlgebra =
        (inferInstance : Algebra B C.functionField) := by
      apply Algebra.algebra_ext
      intro b
      obtain ⟨a, rfl⟩ := h.surjective b
      show algebraMap Γ(C, W) _ (h.symm (h a)) = (h a : C.functionField)
      rw [h.symm_apply_apply]
      rfl
    rw [heq] at this
    exact this
  · intro L _ _ _
    have hp := IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    obtain ⟨hX, e, -, -⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c _ _ hp hgen W hW B hB
    have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c _ _ hp
    obtain ⟨hX1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve L _ (UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hc)
    obtain ⟨hd2, hn2⟩ := hX1 _ hX (pre_ne _ hsurj W hWne)
    exact ⟨ded_of_equiv e, fun hf => hn2 (MulEquiv.isField hf e.symm.toMulEquiv)⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

private lemma sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change (φ.hom.app (op U) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x
  rw [φ.hom.naturality]

private lemma sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (a : F ⟶ G) (b : G ⟶ H)
    {U : Scheme.{0}} (x : Sec F U) : Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

private lemma sec_map_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

private lemma res_univ_eq_zero {R : Type} [CommRing R] {A W : Scheme.{0}} (i : A ⟶ W) {Z : Shv R}
    (h : (free R).obj (yoneda.obj W) ⟶ Z) (h0 : (free R).map (yoneda.map i) ≫ h = 0) :
    Sec.res i (Sec.map h (freeGen R (yoneda.obj W) W (𝟙 W))) = 0 := by
  rw [sec_map_res, CupSpec.freeGen_res]
  have e : (ConcreteCategory.hom ((yoneda.obj W).map i.op)) (𝟙 W) =
      (ConcreteCategory.hom ((yoneda.map i).app (op A))) (𝟙 A) := by simp
  rw [e, ← CupSpec.freeGen_map, ← sec_map_comp, h0, sec_map_zero]

theorem UpperTheory.etale_purity_free_cover :
    LateralTheory.CohomologicalPurity.Thom.LeafFreeCov := by
  intro R _ X U V
  apply Preadditive.epi_of_cancel_zero
  intro Z g hg
  let ι := {O : X.Opens // O = U ∨ O = V}
  have hle : ∀ i : ι, i.1 ≤ U ⊔ V := by
    rintro ⟨O, rfl | rfl⟩
    · exact le_sup_left
    · exact le_sup_right
  have gz : ∀ i : ι, (free R).map (yoneda.map (X.homOfLE (hle i))) ≫ g = 0 := by
    rintro ⟨O, rfl | rfl⟩
    · have := congrArg (biprod.inl ≫ ·) hg
      simpa using this
    · have := congrArg (biprod.inr ≫ ·) hg
      simpa using this
  have cover : ∀ (O : X.Opens) (hO : O ≤ U ⊔ V) (y : (U ⊔ V : X.Opens).toScheme),
      (U ⊔ V).ι y ∈ O → ∃ z, X.homOfLE hO z = y := by
    intro O hO y hy
    have hy' : (U ⊔ V).ι y ∈ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      exact hy
    obtain ⟨z, hz⟩ := hy'
    refine ⟨z, (U ⊔ V).ι.isOpenEmbedding.injective ?_⟩
    change (X.homOfLE hO ≫ (U ⊔ V).ι) z = _
    rw [Scheme.homOfLE_ι, hz]
  refine CupSpec.free_ext g 0 (fun T x => ?_)
  change Sec.map g (freeGen R _ T x) = 0
  let xx : T ⟶ (U ⊔ V : X.Opens).toScheme := x
  obtain ⟨hsep, -⟩ := sec_sep_glue_of_points R Z T ι (fun i => pullback x (X.homOfLE (hle i)))
    (fun i => pullback.fst x (X.homOfLE (hle i))) (fun i => inferInstance) (by
      intro t
      have hy : (U ⊔ V).ι (xx t) ∈ ((U ⊔ V : X.Opens) : Set X) := by
        rw [← Scheme.Opens.range_ι]
        exact ⟨xx t, rfl⟩
      rw [TopologicalSpace.Opens.coe_sup] at hy
      rcases hy with hU | hV
      · obtain ⟨z, hz⟩ := cover U le_sup_left (xx t) hU
        have ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨U, Or.inl rfl⟩))) := by
          rw [Scheme.Pullback.range_fst]
          exact ⟨z, hz⟩
        obtain ⟨v, hv⟩ := ht
        exact ⟨⟨U, Or.inl rfl⟩, v, hv⟩
      · obtain ⟨z, hz⟩ := cover V le_sup_right (xx t) hV
        have ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨V, Or.inr rfl⟩))) := by
          rw [Scheme.Pullback.range_fst]
          exact ⟨z, hz⟩
        obtain ⟨v, hv⟩ := ht
        exact ⟨⟨V, Or.inr rfl⟩, v, hv⟩)
  apply hsep
  intro i
  have z : Sec.map g (freeGen R (yoneda.obj (U ⊔ V : X.Opens).toScheme) i.1.toScheme (X.homOfLE (hle i))) = 0 := by
    have := res_univ_eq_zero (X.homOfLE (hle i)) g (gz i)
    rwa [sec_map_res, CupSpec.freeGen_res, show (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (X.homOfLE (hle i)).op)) (𝟙 _) = X.homOfLE (hle i) by simp] at this
  rw [sec_map_res, CupSpec.freeGen_res]
  have e : (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (pullback.fst x (X.homOfLE (hle i))).op)) x =
      (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (pullback.snd x (X.homOfLE (hle i))).op)) (X.homOfLE (hle i)) := by
    simp [pullback.condition]
  rw [e, ← CupSpec.freeGen_res, ← sec_map_res, z]
  exact map_zero _
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.DescIntPf

private theorem level_rel {Y X Y₀ S S₀ L : Scheme.{0}} (k : Y ⟶ X) (r : X ⟶ S) (c : S₀ ⟶ S)
    (k₀ : Y₀ ⟶ pullback r c) (m : cech k₀ ⟶ cech k)
    (hm : IsPullback m (cechAug k₀) (cechAug k) (sch.map (pullback.fst r c)))
    (p : SimplexCategoryᵒᵖ) (l : L ⟶ X) (e : yoneda.obj L ≅ (cech k).obj p)
    (he : e.hom ≫ (cechAug k).app p = yoneda.map l) (q : ℕ) (i n : ℤ)
    (h : RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst (l ≫ r) c))) :
    RelZS (ZMod q) (tw q i) n (disc.map (m.app p)) := by
  have hp : IsPullback (m.app p) ((cechAug k₀).app p) ((cechAug k).app p)
      (yoneda.map (pullback.fst r c)) :=
    hm.map ((evaluation _ _).obj p)
  have hB : IsPullback (m.app p ≫ e.inv) ((cechAug k₀).app p) (yoneda.map l)
      (yoneda.map (pullback.fst r c)) := by
    refine hp.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.refl_hom, Iso.symm_hom, ← he]
      erw [Iso.inv_hom_id_assoc, Category.comp_id]
    · erw [Category.comp_id]
      try erw [Category.id_comp]
  let φ : pullback (l ≫ r) c ⟶ pullback r c :=
    pullback.lift (pullback.fst (l ≫ r) c ≫ l) (pullback.snd (l ≫ r) c)
      (by simp [pullback.condition])
  have hφ₁ : φ ≫ pullback.fst r c = pullback.fst (l ≫ r) c ≫ l := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd r c = pullback.snd (l ≫ r) c := pullback.lift_snd _ _ _
  have hS : IsPullback (pullback.fst (l ≫ r) c) φ l (pullback.fst r c) := by
    refine IsPullback.of_bot ?_ hφ₁.symm (IsPullback.of_hasPullback r c)
    rw [hφ₂]
    exact IsPullback.of_hasPullback (l ≫ r) c
  have hA := hS.map yoneda
  let ι := IsPullback.isoIsPullback _ _ hA hB
  have hι : ι.hom ≫ m.app p ≫ e.inv = yoneda.map (pullback.fst (l ≫ r) c) :=
    IsPullback.isoIsPullback_hom_fst _ _ hA hB
  have key : yoneda.map (pullback.fst (l ≫ r) c) ≫ e.hom = ι.hom ≫ m.app p := by
    rw [← hι]
    simp
  refine RelZS.of_iso (ZMod q) (tw q i) (sch.map (pullback.fst (l ≫ r) c)) (disc.map (m.app p))
    (disc.mapIso ι) (disc.mapIso e) ?_ n h
  have := congrArg (fun f => disc.map f) key
  simp only [Functor.map_comp] at this
  exact this

private noncomputable def wpOne {A B : Scheme.{0}ᵒᵖ ⥤ Type} (f : A ⟶ B) :
    A ≅ widePullback B (fun _ : Fin (0 + 1) => A) (fun _ => f) where
  hom := WidePullback.lift f (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  inv := WidePullback.π (fun _ : Fin (0 + 1) => f) 0
  hom_inv_id := WidePullback.lift_π _ _ _ _ _
  inv_hom_id := by
    apply WidePullback.hom_ext (fun _ : Fin (0 + 1) => f)
    · intro j
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      rw [Category.assoc, WidePullback.lift_π]
      simp
    · rw [Category.assoc, WidePullback.lift_base]
      simp

private noncomputable def cech_zero {Y X : Scheme.{0}} (k : Y ⟶ X) :
    yoneda.obj Y ≅ (cech k).obj (Opposite.op (SimplexCategory.mk 0)) :=
  wpOne (yoneda.map k)

private theorem cech_zero_aug {Y X : Scheme.{0}} (k : Y ⟶ X) :
    (cech_zero k).hom ≫ (cechAug k).app (Opposite.op (SimplexCategory.mk 0)) = yoneda.map k :=
  WidePullback.lift_base _ _ _ _

theorem UpperTheory.cohomology_base_change_integral_surjective_cech :
    B4 → ∀ (q : ℕ) (i : ℤ) {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) [IsIntegralHom k] [Surjective k] (r : X ⟶ S) (c : S₀ ⟶ S), IsUnit (q : Γ(X, ⊤)) → ∃ (U E : Spc) (u : U ⟶ E) (a' : U ⟶ sch.obj (pullback r c)) (a : E ⟶ sch.obj X), u ≫ a = a' ≫ sch.map (pullback.fst r c) ∧ Eqv _ a (tw q i) ∧ Eqv _ a' (tw q i) ∧ (∀ p : ℕ, ∃ (L : Scheme.{0}) (l : L ⟶ X), IsIntegralHom l ∧ ∀ m, RelZS (ZMod q) (tw q i) m (sch.map (pullback.fst (l ≫ r) c)) → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) ∧ ∀ m, RelZS (ZMod q) (tw q i) m (sch.map (pullback.fst (k ≫ r) c)) → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk 0)))) := by
  intro b4 q i Y X S S₀ k _ _ r c hq
  have hP := IsPullback.of_hasPullback k (pullback.fst r c)
  obtain ⟨u, hu, -⟩ := GlobalTheory.cech_baseChange Y X _ _ _ _ k (pullback.fst r c) hP
  have hq₀ : IsUnit (q : Γ(pullback r c, ⊤)) := by
    simpa using hq.map (pullback.fst r c).appTop.hom
  haveI : IsIntegralHom (pullback.snd k (pullback.fst r c)) := MorphismProperty.of_isPullback hP inferInstance
  haveI : Surjective (pullback.snd k (pullback.fst r c)) := MorphismProperty.of_isPullback hP inferInstance
  refine ⟨_, _, u, cechAug _, cechAug k, hu.w, b4 q k hq i, b4 q _ hq₀ i, fun p => ?_, fun n h => ?_⟩
  · obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.EtC.cech_level_representable (@IsIntegralHom) Y X k inferInstance
      (Opposite.op (SimplexCategory.mk p))
    haveI : IsIntegralHom π := hπ
    exact ⟨Z, π ≫ k, inferInstance, fun n h =>
      level_rel k r c _ u hu _ (π ≫ k) e he q i n h⟩
  · exact level_rel k r c _ u hu _ k (cech_zero k) (cech_zero_aug k) q i n h
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace LateralTheory.E.BuildCut

theorem UpperTheory.isCompact_open_eq_basicOpen_idempotent_of_prodACF :
    ∀ {W : Type} [CommRing W], ProdACF W → ∀ (V : Opens (PrimeSpectrum W)), IsCompact (V : Set (PrimeSpectrum W)) →
        ∃ e : W, IsIdempotentElem e ∧ (V : Set (PrimeSpectrum W)) = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum W)) := by
  classical
  intro W _ hW V hV
  have key : ∀ s : Finset W, ∃ e : W, IsIdempotentElem e ∧
      ∀ p : PrimeSpectrum W, ((s : Set W) ⊆ (p.asIdeal : Set W) ↔ e ∈ p.asIdeal) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp [p.asIdeal.zero_mem]⟩
    | insert a s ha ih =>
      obtain ⟨f, hf, hfs⟩ := ih
      obtain ⟨e, u, he, hu, rfl⟩ := hW.2 a
      have he' : e * e = e := he
      have hf' : f * f = f := hf
      refine ⟨e + f - e * f, ?_, fun p => ?_⟩
      · show (e + f - e * f) * (e + f - e * f) = e + f - e * f
        linear_combination (1 - f + f * f - f) * he' + (1 - e) * hf'
      · rw [Finset.coe_insert, Set.insert_subset_iff, hfs p, SetLike.mem_coe,
          Ideal.mul_unit_mem_iff_mem _ hu]
        constructor
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right _ h1)
        · intro h
          have h1 : e * (e + f - e * f) = e := by linear_combination (1 - f) * he'
          have h2 : f * (e + f - e * f) = f := by linear_combination (1 - e) * hf'
          exact ⟨h1 ▸ p.asIdeal.mul_mem_left _ h, h2 ▸ p.asIdeal.mul_mem_left _ h⟩
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hV, V.isOpen⟩
  obtain ⟨e, he, hte⟩ := key t
  refine ⟨e, he, ?_⟩
  rw [← ht]
  ext p
  simp [PrimeSpectrum.mem_zeroLocus, hte p]
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace LateralTheory.E.BuildCut

theorem UpperTheory.exists_idempotent_submonoid_isLocalization_atPrime :
    ∀ {W : Type} [CommRing W], ProdACF W → ∀ (q : PrimeSpectrum W),
        ∃ T : Submonoid W, (∀ s ∈ T, IsIdempotentElem s ∧ s ∉ q.asIdeal) ∧ IsLocalization T (Localization.AtPrime q.asIdeal) := by
  intro W _ hW q
  let T : Submonoid W :=
    { carrier := {s | IsIdempotentElem s ∧ s ∉ q.asIdeal}
      one_mem' := ⟨IsIdempotentElem.one, (Ideal.ne_top_iff_one _).mp q.isPrime.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨ha.1.mul hb.1, fun h => (q.isPrime.mem_or_mem h).elim ha.2 hb.2⟩ }
  refine ⟨T, fun s hs => hs, ?_⟩
  have hT : ∀ s ∈ T, s ∈ q.asIdeal.primeCompl := fun s hs => hs.2
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact IsLocalization.map_units (Localization.AtPrime q.asIdeal)
      (⟨s, hT s hs⟩ : q.asIdeal.primeCompl)
  · intro z
    obtain ⟨⟨x, ⟨s, hs⟩⟩, hz⟩ := IsLocalization.surj q.asIdeal.primeCompl z
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 s
    have he_q : e ∉ q.asIdeal := fun h => hs (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨x * ↑hu.unit⁻¹, ⟨e, he, he_q⟩⟩, ?_⟩
    simp only at hz ⊢
    calc z * algebraMap W _ e = z * algebraMap W _ (e * u * ↑hu.unit⁻¹) := by
          rw [mul_assoc e, IsUnit.mul_val_inv, mul_one]
      _ = (z * algebraMap W _ (e * u)) * algebraMap W _ ↑hu.unit⁻¹ := by
          rw [map_mul (algebraMap W _) (e * u), mul_assoc]
      _ = algebraMap W _ x * algebraMap W _ ↑hu.unit⁻¹ := by rw [hz]
      _ = algebraMap W _ (x * ↑hu.unit⁻¹) := (map_mul _ _ _).symm
  · intro x y hxy
    obtain ⟨⟨c, hc⟩, hcxy⟩ := (IsLocalization.eq_iff_exists q.asIdeal.primeCompl _).mp hxy
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 c
    have he_q : e ∉ q.asIdeal := fun h => hc (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨e, he, he_q⟩, ?_⟩
    simp only at hcxy ⊢
    have huv : u * ↑hu.unit⁻¹ = 1 := IsUnit.mul_val_inv hu
    calc e * x = e * u * x * ↑hu.unit⁻¹ := by linear_combination (-(e * x)) * huv
      _ = e * u * y * ↑hu.unit⁻¹ := by rw [hcxy]
      _ = e * y := by linear_combination (e * y) * huv
end
