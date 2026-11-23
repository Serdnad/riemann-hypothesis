module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ChartPart

theorem flat_preimage_of_stalk {R Rc : Type} [CommRing R] [CommRing Rc] [IsLocalRing Rc] (ξ : Sp Rc ⟶ Sp R)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) : (Spec.preimage ξ).hom.Flat := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of Rc) ξ
  have h2 : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := HasRingHomProperty.Spec_iff.mpr h
  have h3 : Flat ξ := by
    rw [← h1]
    exact MorphismProperty.comp_mem @Flat _ _ h2 (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)
  rw [← Spec.map_preimage ξ] at h3
  exact HasRingHomProperty.Spec_iff.mp h3

theorem injective_of_flat {R Rc : Type} [CommRing R] [IsDomain R] [CommRing Rc] [Nontrivial Rc] (ρ : R →+* Rc)
    (h : ρ.Flat) : Function.Injective ρ := by
  algebraize [ρ]
  exact FaithfulSMul.algebraMap_injective R Rc

theorem isPullback_away {R Rc : Type} [CommRing R] [CommRing Rc] (ρ : R →+* Rc) (f : R) :
    IsPullback (spMap (Localization.awayMap ρ f)) (spMap (algebraMap Rc (Localization.Away (ρ f)))) (awayMap f)
      (spMap ρ) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_)
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    simp [Localization.awayMap, IsLocalization.Away.map]
  · rw [Scheme.Hom.opensRange_localizationAway (R := .of R), Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
    rfl

theorem exists_iso_preimage_basicOpen {Rc : Type} [CommRing Rc] (G : Over (Sp Rc)) (r : Rc) :
    ∃ e : (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ≅
      pullback G.hom (spMap (algebraMap Rc (Localization.Away r))),
      e.hom ≫ pullback.fst _ _ = (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι := by
  refine ⟨IsOpenImmersion.isoOfRangeEq _ (pullback.fst _ _) ?_, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  rw [IsOpenImmersion.range_pullbackFst, Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
  simp

theorem exists_pff_of_flat {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (hV : (V : Set Y).Nonempty)
    (φ : V.toScheme ⟶ X) [Flat φ] : ∃ θ : X.functionField →+* Y.functionField, PFF V.ι φ θ := by
  have hη : genericPoint Y ∈ V := ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hrange : Set.range (gp Y) ⊆ Set.range V.ι := by
    rw [gp, Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
    exact fun y hy => hy.mem_open V.isOpen hη
  let l := IsOpenImmersion.lift V.ι (gp Y) hrange
  have hl : l ≫ V.ι = gp Y := IsOpenImmersion.lift_fac _ _ _
  have hl0 : V.ι (l (closedPoint Y.functionField)) = genericPoint Y := by
    have : (l ≫ V.ι) (closedPoint Y.functionField) = genericPoint Y := by
      rw [hl]; exact Scheme.fromSpecStalk_closedPoint
    exact this
  have hx : (l ≫ φ) (closedPoint Y.functionField) = genericPoint X := by
    obtain ⟨v, hv, hφv⟩ := Flat.generalizingMap φ
      (genericPoint_specializes (φ (l (closedPoint Y.functionField))))
    have h1 : V.ι v ⤳ genericPoint Y := hl0 ▸ hv.map V.ι.continuous
    have h2 : V.ι v = genericPoint Y := (h1.antisymm (genericPoint_specializes _)).eq
    have h3 : v = l (closedPoint Y.functionField) := V.ι.isOpenEmbedding.injective (h2.trans hl0.symm)
    subst h3
    exact hφv
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := Y.functionField) (l ≫ φ)
  revert hφ
  generalize Scheme.stalkClosedPointTo (R := Y.functionField) (l ≫ φ) = ψ
  revert ψ
  rw [show (l ≫ φ) (closedPoint Y.functionField) = genericPoint X from hx]
  intro ψ hψ
  exact ⟨ψ.hom, l, hl, hψ.symm⟩

end GlobalTheory.Desc.ChartPart

namespace GlobalTheory.Desc


open GlobalTheory.Desc.ChartPart in
theorem chart_part : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ [IsIntegral A.left] (x : Sp R) (C : Chart (awayMap f) A x) [IsIntegral C.G.left], ∃ (ρ : R →+* C.R) (V : C.G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* C.G.left.functionField), C.ξ = spMap ρ ∧ ρ.Flat ∧ (∀ z : C.G.left, z ∈ V ↔ ρ f ∉ (C.G.hom z).asIdeal) ∧ IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) ∧ (∀ (T : Scheme.{0}) (t : T ⟶ pullback C.G.hom (jK C.R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ C.α = t' ≫ φ) ∧ PFF V.ι φ θ := by
  intro R _ _ _ f hf0 A _ hAb _ x C _
  set ρ : R →+* C.R := (Spec.preimage C.ξ).hom with hρdef
  have hξ : C.ξ = spMap ρ := by
    rw [hρdef]; exact (Spec.map_preimage C.ξ).symm
  have hflat : ρ.Flat := flat_preimage_of_stalk C.ξ C.etc.1
  have hρf : ρ f ≠ 0 := fun h => hf0 (injective_of_flat ρ hflat (h.trans (map_zero ρ).symm))
  obtain ⟨_, hnorm⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R

  let Rf := Localization.Away (ρ f)
  have hle : Submonoid.powers (ρ f) ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors hρf
  haveI : IsDomain Rf := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers (ρ f)) Rf inferInstance
  haveI : IsIntegrallyClosed Rf := isIntegrallyClosed_of_isLocalization Rf _ hle
  let ιf : C.R →+* Rf := algebraMap C.R Rf
  let g : Sp Rf ⟶ Sp (Localization.Away f) := spMap (Localization.awayMap ρ f)
  have sq2 := isPullback_away ρ f

  let K := FractionRing C.R
  have hu : IsUnit (algebraMap C.R K (ρ f)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R K)).mpr hρf)
  letI : Algebra Rf K := (Localization.awayLift (algebraMap C.R K) (ρ f) hu).toAlgebra
  haveI : IsScalarTower C.R Rf K := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap C.R K r = Localization.awayLift (algebraMap C.R K) (ρ f) hu (algebraMap C.R Rf r)
    exact (IsLocalization.Away.lift_eq (ρ f) hu r).symm
  haveI : IsFractionRing Rf K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (ρ f)) Rf K
  let j : Sp K ⟶ Sp Rf := spMap (algebraMap Rf K)
  have hjK : j ≫ spMap ιf = jK C.R := by
    simp only [j, spMap, ← Spec.map_comp]; congr 1; ext r
    exact (IsScalarTower.algebraMap_apply C.R Rf K r).symm
  have hy' : j ≫ g = C.y := by
    rw [← cancel_mono (awayMap f), Category.assoc, sq2.w, ← Category.assoc, hjK, C.hy, hξ]

  let GK := (Over.pullback (jK C.R)).obj C.G
  letI : (Over.pullback (jK C.R)).Monoidal := (Over.instBraidedPullback (f := (jK C.R))).toMonoidal
  letI : GrpObj GK := Functor.grpObjObj
  let G₁ := (Over.pullback (spMap ιf)).obj C.G
  letI : (Over.pullback (spMap ιf)).Monoidal := (Over.instBraidedPullback (f := (spMap ιf))).toMonoidal
  letI : GrpObj G₁ := Functor.grpObjObj
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback (spMap ιf) C.G C.semi
  let H₁ := (Over.pullback g).obj A
  letI : (Over.pullback g).Monoidal := (Over.instBraidedPullback (f := g)).toMonoidal
  letI : GrpObj H₁ := Functor.grpObjObj
  have hH₁ : IsSemiAbelian H₁ :=
    IsSemiAbelian.pullback g A (isSemiAbelian_of_isAbelianScheme A hAb)
  let i₁ : GK.left ⟶ G₁.left := pullback.lift (pullback.fst C.G.hom (jK C.R)) (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hjK]; exact pullback.condition)
  have h₁ : IsGrpPullback GK G₁ j i₁ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback C.G (spMap ιf)) ?_ (pullback.lift_snd _ _ _)
    exact (isGrpPullback_pullback C.G (jK C.R)).congr hjK.symm (pullback.lift_fst _ _ _).symm
  let i₂ : GK.left ⟶ H₁.left := pullback.lift C.α (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hy']; exact C.gen.1.w)
  have h₂ : IsGrpPullback GK H₁ j i₂ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback A g) ?_ (pullback.lift_snd _ _ _)
    exact C.gen.congr hy'.symm (pullback.lift_fst _ _ _).symm
  obtain ⟨E, ⟨hEm, hE⟩, -⟩ := semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) (IsGenericPointHom.fractionField Rf K) hG₁ hH₁ h₁ h₂

  haveI : IsMonHom E.hom := hEm
  let φ₁ : G₁.left ⟶ A.left := E.hom.left ≫ pullback.fst A.hom g
  have sq1 : IsPullback φ₁ G₁.hom A.hom g :=
    (((isGrpPullback_of_iso E).comp (isGrpPullback_pullback A g)).congr (Category.id_comp g) rfl).1

  let V : C.G.left.Opens := C.G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (ρ f)
  obtain ⟨e, he⟩ := exists_iso_preimage_basicOpen C.G (ρ f)
  let φ : V.toScheme ⟶ A.left := e.hom ≫ φ₁
  have sq0 : IsPullback e.hom (V.ι ≫ C.G.hom) (G₁.hom ≫ spMap ιf) (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    show e.hom ≫ pullback.snd _ _ ≫ spMap ιf = (V.ι ≫ C.G.hom) ≫ 𝟙 _
    rw [Category.comp_id, ← pullback.condition, ← Category.assoc, he]
  have hcart : IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) := by
    have := sq0.paste_horiz (sq1.paste_vert sq2)
    rwa [Category.id_comp] at this
  haveI : Flat (spMap ρ) := HasRingHomProperty.Spec_iff.mpr hflat
  haveI : Flat φ := MorphismProperty.of_isPullback hcart.flip inferInstance

  have hVne : (V : Set C.G.left).Nonempty := by
    let s : Sp C.R ⟶ C.G.left := (η[C.G] : 𝟙_ (Over (Sp C.R)) ⟶ C.G).left
    have hs : s ≫ C.G.hom = 𝟙 _ := Over.w η[C.G]
    let p : Sp C.R := (⊥ : PrimeSpectrum C.R)
    refine ⟨s p, ?_⟩
    show ρ f ∉ (C.G.hom (s p)).asIdeal
    rw [← Scheme.Hom.comp_apply, hs]
    exact fun h => hρf (Ideal.mem_bot.1 h)
  obtain ⟨θ, hθ⟩ := exists_pff_of_flat V hVne φ
  refine ⟨ρ, V, φ, θ, hξ, hflat, fun z => Iff.rfl, hcart, ?_, hθ⟩
  intro T t t' htt'
  have key : t ≫ i₁ = t' ≫ e.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, htt', Category.assoc, he]
    · rw [← cancel_mono (spMap ιf)]
      have l : t ≫ i₁ ≫ pullback.snd _ _ ≫ spMap ιf = t ≫ pullback.fst _ _ ≫ C.G.hom := by
        simp only [i₁, pullback.lift_snd_assoc, Category.assoc, hjK]; rw [pullback.condition]
      have r : t' ≫ e.hom ≫ pullback.snd _ _ ≫ spMap ιf = t' ≫ V.ι ≫ C.G.hom := by
        rw [← pullback.condition, ← Category.assoc e.hom, he]
      simp only [Category.assoc]
      rw [l, r, ← Category.assoc t, htt', Category.assoc]
  have : t ≫ C.α = t ≫ i₂ ≫ pullback.fst A.hom g := by rw [pullback.lift_fst]
  rw [this, ← hE, Category.assoc, ← Category.assoc t, key, Category.assoc]

end GlobalTheory.Desc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecBC

theorem sqDec_baseChange : ∀ (k R S : Type) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) (A₀ : Over (Sp k)) [GrpObj A₀] (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) → SqDec ((Over.pullback (spMap (algebraMap k S))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) := by
  intro k R S _ _ _ _ _ ρ A₀ _ L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  set bc := GlobalTheory.Spread.bcMap A₀.hom ρ with hbc
  have hg' : ∀ i, ∃ g : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀,
      IsMonHom g ∧ g.left ≫ bc = bc ≫ (β i).left := by
    intro i
    haveI := hβ i
    obtain ⟨g, hg, e⟩ := GlobalTheory.HomDescent.exists_specialise (β i) ρ
    refine ⟨g, hg, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_fst, e, Category.assoc]
    · have w₁ := Over.w g
      have w₂ := Over.w (β i)
      simp only [Over.pullback_obj_hom] at w₁ w₂
      rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_snd, ← Category.assoc, w₁, Category.assoc, w₂, GlobalTheory.Spread.bcMap_snd]
  choose g hgm hgc using hg'
  refine ⟨N, a₀, r, a, g, hN, ha₀, hgm, ?_⟩
  set fR := pullback.fst A₀.hom (spMap (algebraMap k R)) with hfR
  set fS := pullback.fst A₀.hom (spMap (algebraMap k S)) with hfS
  have efS : fS = bc ≫ fR := (GlobalTheory.Spread.bcMap_fst A₀.hom ρ).symm
  have pullIso : ∀ {X Y : Scheme.{0}} {P Q : LB X}, LBIso P Q → ∀ f : Y ⟶ X, LBIso (P.pull f) (Q.pull f) :=
    fun h f => h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl)
  have i1 := lbIso_lbPow_pull hL fS N
  have i2 := GlobalTheory.Spread.lbIso_pull_pull (isLB_lbPow hL N) bc efS
  have i3 := pullIso (lbIso_lbPow_pull hL fR N).symm bc
  have i4 := pullIso H bc
  have hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (g i).left) ≫ bc = bc ≫ (o.elim (𝟙 _) fun i => (β i).left) := by
    intro o
    cases o with
    | none => simp
    | some i => exact hgc i
  have i5 := (GlobalTheory.SymExtend.lbIso_linComb_pull (pull_isLB hM fR) bc (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (g i).left)
    (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) bc hc).symm
  have i6 : LBIso (LB.LinComb ((M.pull fR).pull bc) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)))
      (LB.LinComb (M.pull fS) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ))) := by
    obtain ⟨w, hw⟩ := (GlobalTheory.Spread.lbIso_pull_pull hM bc efS).symm
    exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩
  have j1 := i1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _)
    (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _) i2
  have j2 := j1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _)
    (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _) i3
  have j3 := j2.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
    (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _) i4
  have j4 := j3.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _)
    (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _) i5
  exact j4.trans (isLB_lbPow (pull_isLB hL _) N) (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _)
    (LB.isLB_linComb (pull_isLB hM _) _ _) i6

end GlobalTheory.SqDecBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecIdBC

theorem sqDec_of_baseChange_id : ∀ (F : Type) [CommRing F] (A : Over (Sp F)) [GrpObj A] (L M : LB A.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (RingHom.id F))).obj A) (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) → SqDec A L M := by
  intro F _ A _ L M hL hM hD
  have hid : spMap (RingHom.id F) = 𝟙 (Sp F) := by
    simp [spMap]
  have hw : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id F) := by rw [hid]; simp
  let π' : A.left ⟶ pullback A.hom (spMap (RingHom.id F)) := pullback.lift (𝟙 _) A.hom hw
  have e₁ : π' ≫ pullback.fst A.hom (spMap (RingHom.id F)) = 𝟙 _ := pullback.lift_fst _ _ _
  have e₂ : π' ≫ ((Over.pullback (spMap (RingHom.id F))).obj A).hom = A.hom ≫ 𝟙 _ := by
    change π' ≫ pullback.snd A.hom (spMap (RingHom.id F)) = A.hom ≫ 𝟙 _
    simp [π']
  have hP : IsGrpPullback A ((Over.pullback (spMap (RingHom.id F))).obj A) (𝟙 _) π' := by
    have n : IsGrpPullback A A (𝟙 _ ≫ spMap (RingHom.id F)) (π' ≫ pullback.fst A.hom (spMap (RingHom.id F))) := by
      rw [e₁, Category.id_comp, hid]; exact GlobalTheory.SiegLower.isGrpPullback_id A
    exact IsGrpPullback.cancel (isGrpPullback_pullback A _) n e₂
  obtain ⟨N, a₀, r, e, β, hN, ha₀, hβ, hI⟩ := hD
  have hβ' : ∀ i, ∃ g : A ⟶ A, IsMonHom g ∧ g.left ≫ π' = π' ≫ (β i).left := fun i => by
    haveI := hβ i
    exact GlobalTheory.HomDescent.exists_isMonHom_pull hP hP (β i)
  choose β' hβ'm hβ'c using hβ'
  have iL : LBIso L ((L.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hL (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hL _) _) (GlobalTheory.SiegLower.lbIso_pull_id hL)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hL) _ _ _ π' (fun _ => by rw [e₁]; simp))
  have iM : LBIso M ((M.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hM (LB.isLB_pull hM _) (LB.isLB_pull (LB.isLB_pull hM _) _) (GlobalTheory.SiegLower.lbIso_pull_id hM)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hM) _ _ _ π' (fun _ => by rw [e₁]; simp))
  refine ⟨N, a₀, r, e, β', hN, ha₀, hβ'm, ?_⟩
  have j₁ : LBIso (lbPow L N) ((lbPow (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) N).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iL _ _ _ π' (fun _ => by simp)
  have j₂ := GlobalTheory.RigidBundleGlue.LBIso.pull hI π'
  have j₃ : LBIso (LB.LinComb M (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β' i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ))
      ((LB.LinComb (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ)).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iM _ _ _ π' (fun o => by
      cases o with
      | none => simp
      | some i => exact hβ'c i)
  exact LBIso.trans (isLB_lbPow hL N) (LB.isLB_pull (isLB_lbPow (LB.isLB_pull hL _) N) _)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₁
    (LBIso.trans (LB.isLB_pull (isLB_lbPow (LB.isLB_pull hL _) N) _)
      (LB.isLB_pull (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (LB.isLB_pull hM _) _ _) _)
      (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₂ (LBIso.symm j₃))

end GlobalTheory.SqDecIdBC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
namespace GlobalTheory.SqDecTransport

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem transport : ∀ (k K k₁ K' : Type) [Field k] [Field K] [Field k₁] [Field K'] (a : k →+* K) (b : k →+* k₁) (c : K →+* K') (d : k₁ →+* K'), c.comp a = d.comp b → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp K)) [GrpObj A] (π : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap a) π → ∀ (L₀ M₀ : LB A₀.left) (L M : LB A.left), L₀.IsLB → M₀.IsLB → L.IsLB → M.IsLB → LBIso L (L₀.pull π) → LBIso M (M₀.pull π) → SqDec ((Over.pullback (spMap b)).obj A₀) (L₀.pull (pullback.fst A₀.hom (spMap b))) (M₀.pull (pullback.fst A₀.hom (spMap b))) → SqDec ((Over.pullback (spMap c)).obj A) (L.pull (pullback.fst A.hom (spMap c))) (M.pull (pullback.fst A.hom (spMap c))) := by
  intro k K k₁ K' _ _ _ _ a b c d hcd A₀ _ A _ π hA L₀ M₀ L M hL₀ hM₀ hLL hML hL hM hD
  have hw : (pullback.fst A.hom (spMap c) ≫ π) ≫ A₀.hom = (pullback.snd A.hom (spMap c) ≫ spMap d) ≫ spMap b := by
    rw [Category.assoc, hA.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      spMap_comp_spMap, spMap_comp_spMap, hcd]
  let π' : pullback A.hom (spMap c) ⟶ pullback A₀.hom (spMap b) := pullback.lift _ _ hw
  have e₁ : π' ≫ pullback.fst A₀.hom (spMap b) = pullback.fst A.hom (spMap c) ≫ π := pullback.lift_fst _ _ _
  have e₂ : π' ≫ pullback.snd A₀.hom (spMap b) = pullback.snd A.hom (spMap c) ≫ spMap d := pullback.lift_snd _ _ _
  have hP : IsGrpPullback ((Over.pullback (spMap c)).obj A) ((Over.pullback (spMap b)).obj A₀) (spMap d) π' := by
    have n := (isGrpPullback_pullback A (spMap c)).comp hA
    rw [spMap_comp_spMap, hcd, ← spMap_comp_spMap, ← e₁] at n
    exact IsGrpPullback.cancel (isGrpPullback_pullback A₀ (spMap b)) n e₂
  obtain ⟨N, a₀, r, e, β, hN, ha₀, hβ, hI⟩ := hD
  have hβ' : ∀ i, ∃ f : (Over.pullback (spMap c)).obj A ⟶ (Over.pullback (spMap c)).obj A,
      IsMonHom f ∧ f.left ≫ π' = π' ≫ (β i).left := fun i => by
    haveI := hβ i
    exact GlobalTheory.HomDescent.exists_isMonHom_pull hP hP (β i)
  choose β' hβ'm hβ'c using hβ'
  have iL : LBIso (L.pull (pullback.fst A.hom (spMap c))) ((L₀.pull (pullback.fst A₀.hom (spMap b))).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull hL _ _ _ π' (fun _ => e₁.symm)
  have iM : LBIso (M.pull (pullback.fst A.hom (spMap c))) ((M₀.pull (pullback.fst A₀.hom (spMap b))).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull hM _ _ _ π' (fun _ => e₁.symm)
  refine ⟨N, a₀, r, e, β', hN, ha₀, hβ'm, ?_⟩
  have j₁ : LBIso (lbPow (L.pull (pullback.fst A.hom (spMap c))) N)
      ((lbPow (L₀.pull (pullback.fst A₀.hom (spMap b))) N).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iL _ _ _ π' (fun _ => by simp)
  have j₂ := GlobalTheory.RigidBundleGlue.LBIso.pull hI π'
  have j₃ : LBIso (LB.LinComb (M.pull (pullback.fst A.hom (spMap c))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β' i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ))
      ((LB.LinComb (M₀.pull (pullback.fst A₀.hom (spMap b))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ)).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iM _ _ _ π' (fun o => by
      cases o with
      | none => simp
      | some i => exact hβ'c i)
  exact LBIso.trans (isLB_lbPow (pull_isLB hLL _) N) (pull_isLB (isLB_lbPow (pull_isLB hL₀ _) N) _)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hML _) _ _) j₁
    (LBIso.trans (pull_isLB (isLB_lbPow (pull_isLB hL₀ _) N) _)
      (pull_isLB (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hM₀ _) _ _) _)
      (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hML _) _ _) j₂ (LBIso.symm j₃))

end GlobalTheory.SqDecTransport
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.PullOpen

open GlobalTheory.Cartier.DomPull

theorem isDominant_of_gen {X V : Scheme.{0}} [IsIntegral X] (φ : V ⟶ X) (v : V)
    (hv : φ v = genericPoint X) : IsDominant φ := by
  refine ⟨?_⟩
  have hd : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact (genericPoint_spec X).def
  exact hd.mono (Set.singleton_subset_iff.2 ⟨v, hv⟩)

theorem gp_apply {X : Scheme.{0}} [IsIntegral X] (q : Sp X.functionField) : gp X q = genericPoint X := by
  have h1 : gp X q ⤳ genericPoint X := by
    have : gp X q ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  exact (h1.antisymm (genericPoint_specializes _)).eq

theorem ffm_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {V : Y.Opens} [IsIntegral V.toScheme]
    [IsDominant V.ι] {φ : V.toScheme ⟶ X} [IsDominant φ] {θ : X.functionField →+* Y.functionField}
    (h : PFF V.ι φ θ) : (GlobalTheory.functionFieldMap V.ι).comp θ = GlobalTheory.functionFieldMap φ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have e1 : Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap V.ι)) ≫ l = genericFieldPoint V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, h₁]
    exact GlobalTheory.specMap_functionFieldMap V.ι
  have e2 : Spec.map (CommRingCat.ofHom ((GlobalTheory.functionFieldMap V.ι).comp θ)) ≫ gp X =
      Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap φ)) ≫ gp X := by
    refine Eq.trans ?_ (GlobalTheory.specMap_functionFieldMap φ).symm
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    erw [← h₂]
    rw [← Category.assoc, e1]
  haveI : Mono (gp X) := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e2))

theorem lbIso_pull : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (φ : V.toScheme ⟶ X)
    (θ : X.functionField →+* Y.functionField) (D : CartierDiv X) (D₁ : CartierDiv Y),
    PFF V.ι φ θ → PPull V.ι φ θ D D₁ → LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := by
  intro X Y _ _ V φ θ D D₁ hF hP
  obtain ⟨l, h₁, h₂⟩ := hF
  obtain ⟨q⟩ : Nonempty (Sp Y.functionField) := inferInstance
  haveI : Nonempty V := ⟨l q⟩
  haveI : IsIntegral V.toScheme := inferInstance
  haveI : IsDominant V.ι := isDominant_of_gen V.ι (l q) (by
    rw [← Scheme.Hom.comp_apply, h₁, gp_apply])
  haveI : IsDominant φ := isDominant_of_gen φ (l q) (by
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, gp_apply])
  have key := ffm_comp (V := V) (φ := φ) ⟨l, h₁, h₂⟩
  have hE : pullback V.ι D₁ = pullback φ D := CartierDiv.ext_of_isEqn fun v => by
    obtain ⟨g, hg⟩ := D.exists_isEqn (φ v)
    refine ⟨unitsMap φ g, ?_, isEqn_pullback φ D hg⟩
    have := isEqn_pullback V.ι D₁ (hP v g hg)
    convert this using 1
    ext
    simp only [unitsMap, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact (congrArg (fun f : X.functionField →+* V.toScheme.functionField => f g) key).symm
  exact (presents_pullback V.ι D₁).lbIso (hE ▸ presents_pullback φ D)

end GlobalTheory.Desc.PullOpen
end
