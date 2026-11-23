module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle037
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle130
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle129
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle063
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LieModelTransportIsomorphism
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

theorem _root_.GlobalTheory.T.projective_point_coords_exist : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (r : ℕ) (p : Sp Ω ⟶ PSpace ℚ r), ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point | exact GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point | (intros; apply GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

theorem _root_.GlobalTheory.T.projective_point_image_reduced : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (hx : x ≠ 0), IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant | exact GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

theorem _root_.GlobalTheory.T.segre_product_affine_chart : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N r : ℕ) (Z : Scheme.{0}) (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r)) [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0) (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx') (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0), IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧ ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l), Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart.prod_chart | exact GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart.prod_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart.prod_chart <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusPoints

theorem charVal_eq_diag {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A] {a : Sp A ⟶ S}
    (t : Over.mk a ⟶ splitTorus S X) (χ : X) : charVal t χ = GlobalTheory.Diag.charVal t χ := by
  rw [GlobalTheory.Diag.charVal_eq_torusFst]
  rfl

theorem main : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] (a : Sp A ⟶ S), (∀ t t' : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = charVal t' χ) → t = t') ∧ (∀ (t t' : Over.mk a ⟶ splitTorus S X) (χ : X), charVal (t * t') χ = charVal t χ * charVal t' χ) ∧ (∀ χ : X, charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1) ∧ (∀ (t : Over.mk a ⟶ splitTorus S X), charVal t 0 = 1 ∧ ∀ χ χ', charVal t (χ + χ') = charVal t χ * charVal t χ') ∧ (∀ w : Multiplicative X →* A, ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = w (Multiplicative.ofAdd χ)) ∧ ∀ (A' : Type) [CommRing A'] (g : A →+* A') (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk (spMap g ≫ a) ⟶ splitTorus S X), t'.left = spMap g ≫ t.left → ∀ χ, charVal t' χ = g (charVal t χ) := by
  intro S X _ A _ a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' h
    refine GlobalTheory.Diag.charVal_ext fun χ => ?_
    rw [← charVal_eq_diag, ← charVal_eq_diag]
    exact h χ
  · intro t t' χ
    rw [charVal_eq_diag, charVal_eq_diag, charVal_eq_diag, GlobalTheory.Diag.charVal_mul]
  · intro χ
    rw [charVal_eq_diag, GlobalTheory.Diag.charVal_one]
  · intro t
    refine ⟨?_, fun χ χ' => ?_⟩
    · rw [charVal_eq_diag, GlobalTheory.Diag.charVal_zero]
    · rw [charVal_eq_diag, charVal_eq_diag, charVal_eq_diag, GlobalTheory.Diag.charVal_add]
  · intro w
    refine ⟨GlobalTheory.Diag.ofVal a w, fun χ => ?_⟩
    rw [charVal_eq_diag, GlobalTheory.Diag.charVal_ofVal]
  · intro A' _ g t t' ht χ
    rw [charVal_eq_diag, charVal_eq_diag]
    exact (GlobalTheory.Diag.left_eq_iff g rfl t' t).1 ht χ

end GlobalTheory.CompanionTheory.Ar.TorusPoints
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

open GlobalTheory.CompanionTheory.Ar.CptModel

theorem val_mul_eq {R K : Type} [CommRing R] [Field K] {φ₀ : R →+* K} (hξ : IsCptGen (pt φ₀)) (φ : R →+* ℂ)
    {g h : R} (h0 : φ₀ h ≠ 0) {r : ℂ} (hv : ValAt (pt φ₀) (pt φ) (φ₀ g / φ₀ h) r) : r * φ h = φ g := by
  obtain ⟨hsp, s, hs, rfl⟩ := hv
  let c : Cpt (pt φ₀) := ⟨centre (pt φ), hsp⟩
  have e : s * tS c.1 h = tS c.1 g := by
    apply hξ.inj c
    rw [map_mul, genMap_toStalk, genMap_toStalk]
    refine (congrArg (· * φ₀ h) hs).trans ?_
    exact div_mul_cancel₀ _ h0
  have k : ∀ a : R, (Scheme.stalkClosedPointTo (pt φ)).hom (tS c.1 a) = φ a := fun a => by
    have := genMap_toStalk φ (self (pt φ)) a
    rw [genMap_self] at this
    exact this
  rw [← k h, ← k g, ← e]
  exact (map_mul _ _ _).symm

theorem ne_zero_of_top_le {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (f : R)
    (hW : ⊤ ≤ (pt φ) ⁻¹ᵁ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens)) : φ f ≠ 0 := by
  have h1 : genPt (pt φ) ∈ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) :=
    hW (show IsLocalRing.closedPoint K ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
  have h2 : f ∉ (genPt (pt φ)).asIdeal := h1
  rw [genPt_asIdeal] at h2
  exact h2

theorem isDVR_regAt {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    {φ : R →+* K} (hξ : IsCptGen (pt φ)) (x : Cpt (pt φ)) (h1 : x.1.asIdeal.height = 1) :
    IsDiscreteValuationRing (regAt (pt φ) x) := by
  haveI : (x.1 : PrimeSpectrum R).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have hd := GlobalTheory.T.isDiscreteValuationRing_localization_of_height_eq_one' R x.1.asIdeal h1
  have key : ∀ (q : PrimeSpectrum R), Nonempty (Localization.AtPrime q.asIdeal ≃+* (Spec.structureSheaf R).presheaf.stalk q) :=
    fun q => ⟨(IsLocalization.algEquiv q.asIdeal.primeCompl _ _).toRingEquiv⟩
  obtain ⟨e⟩ := key x.1
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (e.trans (CPoint.regAtEquivStalk hξ x))

end GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

namespace GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

open GlobalTheory.CompanionTheory.Ar.CptModel

theorem exists_pole_prime {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] (t : K) (ht : ∀ a : R, algebraMap R K a ≠ t) :
    ∃ p : Ideal R, p.IsPrime ∧ p.height = 1 ∧ ∀ a c : R, c ∉ p → t * algebraMap R K c ≠ algebraMap R K a := by
  by_contra hcon
  push Not at hcon
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_eq_algebraMap_of_integral_at_height_one_primes R (e.symm t) fun q hq h1 => by
    obtain ⟨a, c, hc, hac⟩ := hcon q hq h1
    refine ⟨a, c, hc, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply, e.commutes, e.commutes]
    exact hac
  have h2 : e (algebraMap R (FractionRing R) a) = t := by rw [ha, e.apply_symm_apply]
  rw [e.commutes] at h2
  exact ht a h2

theorem exists_cpt {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (hφ : Function.Injective φ) (p : Ideal R)
    (hp : p.IsPrime) : ∃ x : Cpt (pt φ), x.1.asIdeal = p := by
  have hsp : genPt (pt φ) ⤳ ((⟨p, hp⟩ : PrimeSpectrum R) : Spec (CommRingCat.of R)) := by
    refine (PrimeSpectrum.le_iff_specializes (genPt (pt φ) : PrimeSpectrum R) ⟨p, hp⟩).1 ?_
    show (genPt (pt φ)).asIdeal ≤ p
    rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact ⟨⟨_, hsp⟩, rfl⟩

theorem exists_ringHom {R S : Type} [CommRing R] [CommRing S]
    (f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) : ∃ c : R →+* S, spMap c = f :=
  ⟨(Spec.preimage f).hom, Spec.map_preimage f⟩

theorem exists_disc {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R] [Algebra R K] [IsFractionRing R K] (f : R) (hf : algebraMap R K f ≠ 0)
    (t : K) (x : Cpt (pt (algebraMap R K))) (hxf : f ∈ x.1.asIdeal) (hx1 : x.1.asIdeal.height = 1)
    (hxt : t ∉ regAt (pt (algebraMap R K)) x) :
    ∃ (φ : (Fin 1 → ℂ) → (R →+* ℂ)) (r : (Fin 1 → ℂ) → ℂ) (C : ℝ), IsHolPts (Metric.ball 0 1) φ ∧
      ∀ z ∈ punct 1 1 1, ⊤ ≤ (pt (φ z)) ⁻¹ᵁ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) ∧
        ValAt (pt (algebraMap R K)) (pt (φ z)) t (r z) ∧ r z ≠ 0 ∧ ‖(r z)⁻¹‖ ≤ C * ‖z 0‖ := by
  have hξ : IsCptGen (pt (algebraMap R K)) := isCptGen_fractionRing
  have hgW : genPt (pt (algebraMap R K)) ∈
      (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) := by
    show f ∉ (genPt (pt (algebraMap R K))).asIdeal
    rw [genPt_asIdeal]
    exact hf
  have hxW : x.1 ∉ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) := fun hm => (show f ∉ x.1.asIdeal from hm) hxf
  have hlft : LocallyOfFiniteType (spMap (algebraMap ℚ R)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  obtain ⟨V, hV, ψ, r, C, -, hhol, -, hz⟩ := GlobalTheory.T.dvr_point_analytic_disc ℚ (algebraMap ℚ ℂ) (Spec (CommRingCat.of R))
    (spMap (algebraMap ℚ R)) K (pt (algebraMap R K)) (PrimeSpectrum.basicOpen f) x ⊤ t hlft hξ hgW hxW trivial
    (isDVR_regAt hξ x hx1) hxt
  obtain ⟨c, hc⟩ := exists_ringHom (S := Γ(Spec (CommRingCat.of R), V)) hV.fromSpec
  have hy : ∀ w, spMap (ψ w) ≫ hV.fromSpec = pt ((ψ w).comp c) := fun w => by
    rw [← hc]
    exact (Spec.map_comp _ _).symm
  refine ⟨fun z => (ψ z).comp c, r, C, ⟨hhol.1, fun a => hhol.2 (c a)⟩, fun z hzp => ?_⟩
  have := hz z hzp
  rwa [hy] at this

theorem disc_of_pole {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R] [Algebra R K] [IsFractionRing R K] (g h b : R)
    (hh : algebraMap R K h ≠ 0) (hb : algebraMap R K b ≠ 0)
    (ht : ∀ a : R, algebraMap R K a ≠ algebraMap R K g / algebraMap R K h) :
    ∃ (ψ : ℂ → (R →+* ℂ)) (C : ℝ), (∀ a : R, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  have hξ : IsCptGen (pt (algebraMap R K)) := isCptGen_fractionRing
  obtain ⟨p, hp, hp1, hpole⟩ := exists_pole_prime _ ht
  have hhp : h ∈ p := by
    by_contra hn
    exact hpole g h hn (div_mul_cancel₀ _ hh)
  obtain ⟨x, rfl⟩ := exists_cpt (algebraMap R K) (IsFractionRing.injective R K) p hp
  have hnt : algebraMap R K g / algebraMap R K h ∉ regAt (pt (algebraMap R K)) x := by
    intro hm
    obtain ⟨a, c, hc, -, e⟩ := (mem_regAt_iff _ x _).1 hm
    exact hpole a c hc e
  obtain ⟨φ, r, C, hhol, hz⟩ := exists_disc (K := K) (b * h) (by rw [map_mul]; exact mul_ne_zero hb hh) _ x
    (Ideal.mul_mem_left _ b hhp) hp1 hnt
  have hd : ∀ z : ℂ, ‖(fun _ => z : Fin 1 → ℂ)‖ = ‖z‖ := fun z => pi_norm_const z
  refine ⟨fun z => φ fun _ => z, C, fun a => ?_, fun z hz1 hz0 => ?_⟩
  · have h1 : DifferentiableOn ℂ (fun (z : ℂ) (_ : Fin 1) => z) (Metric.ball 0 1) :=
      (differentiable_pi.2 fun _ => differentiable_id).differentiableOn
    refine (hhol.2 a).comp h1 fun z hz1 => ?_
    rw [mem_ball_zero_iff] at hz1 ⊢
    rwa [hd]
  · have hmem : (fun _ => z : Fin 1 → ℂ) ∈ punct 1 1 1 := by
      refine ⟨?_, fun _ _ => hz0⟩
      rw [mem_ball_zero_iff] at hz1 ⊢
      rwa [hd]
    obtain ⟨hW, hval, hr0, hbd⟩ := hz _ hmem
    have hbh := ne_zero_of_top_le _ _ hW
    rw [map_mul] at hbh
    have e := val_mul_eq hξ _ hh hval
    have hz0' := right_ne_zero_of_mul hbh
    refine ⟨left_ne_zero_of_mul hbh, hz0', ?_⟩
    have e2 : φ (fun _ => z) h = (r fun _ => z)⁻¹ * φ (fun _ => z) g := by
      rw [← e]
      field_simp
    show ‖φ (fun _ => z) h‖ ≤ C * ‖z‖ * ‖φ (fun _ => z) g‖
    rw [e2, norm_mul]
    exact mul_le_mul_of_nonneg_right hbd (norm_nonneg _)

theorem pole_disc : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  intro Ω _ _ A hFG hSm hfrac g h b hh hb ht
  haveI : Algebra.FiniteType ℚ A := (Subalgebra.fg_iff_finiteType A).1 hFG
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  haveI : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth ℚ A
  haveI : IsFractionRing A Ω := IsFractionRing.of_field A Ω fun z => by
    obtain ⟨a, ha, c, hc, hc0, e⟩ := hfrac z
    have hc0' : algebraMap A Ω ⟨c, hc⟩ ≠ 0 := hc0
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, eq_div_of_mul_eq hc0' e⟩
  refine disc_of_pole (K := Ω) g h b hh hb fun a e => ht ?_
  have e' : (a : Ω) = (g : Ω) / h := e
  rw [← e']
  exact a.2

end GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.number_field_point_integral_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ Small.ptsOver L (mCoordIdeal y), ∃ z : Sp (𝓞 L) ⟶ X, CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.algebraicPoint_extends_to_integers | exact GlobalTheory.CompanionTheory.Ar.algebraicPoint_extends_to_integers | (intros; apply GlobalTheory.CompanionTheory.Ar.algebraicPoint_extends_to_integers <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.frame_domain_in_segre_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segreCoord y) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f : Ω) (h : genPt ξ ⤳ centre z), CoordsAt ξ y z w → InFrameDomain y cc f w → InChart ξ (segreCoord y) cc ⟨centre z, h⟩ ∧ unitAt ξ ⟨centre z, h⟩ f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.inChart_unitAt_of_inFrameDomain | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.inChart_unitAt_of_inFrameDomain | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.inChart_unitAt_of_inFrameDomain <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.unit_value_frame_domain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f u : Ω), CoordTie ℤ ξ (segreCoord y) → genPt ξ ⤳ centre z → CoordsAt ξ y z w → InFrameDomain y cc f w → IsUnitOn y cc f u → valAt y u w ≠ 0 ∧ ValAt ξ z u (valAt y u w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn | exact GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn | (intros; apply GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.flat_herm_unit_constant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (α : (𝓞 F)ˣ), OverInt y φ → ∃ S : FlatHerm y φ (constLine (ι := ι) 0), S.M = 1 ∧ ∀ σ, S.κ σ = ‖σ ((α : 𝓞 F) : F)‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_model_vector_bundles : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → ∃ (X' : Scheme.{0}) (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (N : ℕ) (x' : Fin (N + 1) → Ω') (b : ∀ s, Fin (r s) → TensorProduct Ω Ω' E), CoordTie ℤ ξ' x' ∧ (∀ q : X', genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω Ω') ∧ Smooth f ∧ Function.Surjective f ∧ IsGenericFlag (Ω' := Ω') (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom V b 1 ∧ ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom).IsFlagVBOn Set.univ (b s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_flagBundle | exact GlobalTheory.CompanionTheory.Ar.exists_flagBundle | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_flagBundle <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.tate_iso_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (i : k →+* k') (x : Sp k ⟶ X), IsProper (pullback.snd t.G.hom x) → ∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t (spMap i ≫ x), ∀ n, 0 < n → (I'.ζ n : k') = i (I.ζ n) ∧ ∀ a, (I'.ev n a).left = spMap i ≫ (I.ev n a).left := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tate_iso_base_change | exact GlobalTheory.CompanionTheory.Relay.tate_iso_base_change | (intros; apply GlobalTheory.CompanionTheory.Relay.tate_iso_base_change <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.IsoMove

theorem lieModel_isoMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (m : SABMap t' t e.hom) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V), ξ' ≫ e.hom = ξ → ∃ M' : LieModel t'.G ξ' V, (∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left) ∧ (∀ n, FullTorsion t.G ξ n → FullTorsion t'.G ξ' n) ∧ (IsCptGen ξ → IsCptGen ξ') ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ ∧ (M'.lat q : Set V) = M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M'.htOm t'.PP.L n q : Set (Module.Dual Ω V)) = M.htOm t.PP.L n ⟨e.hom q.1, h⟩ :=
  @PositivityTheory.UnitarySelfGeneration.lie_model_transport_isomorphism

end GlobalTheory.CompanionTheory.Ar.IsoMove
end
