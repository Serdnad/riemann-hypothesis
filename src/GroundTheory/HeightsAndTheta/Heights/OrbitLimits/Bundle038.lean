module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPtsIntegralPoints
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle092
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointResidue
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle044
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveRationalSectionSum

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_smul {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    logNorm X s (fun p => c p.1 * z p) = logNorm X s z := by
  unfold logNorm
  rw [eval_smul_homog s a hs c z, X.smul c z hc, norm_mul]
  have hprod : (∏ k, ‖c k‖ ^ X.a k) = ‖∏ k, c k ^ a k‖ := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hXa k, zpow_natCast, norm_pow]
  rw [hprod, mul_div_mul_left _ _
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)))]

theorem arInt_eq_sum {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    arInt P s X (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
      ∑ᶠ q : projPts P, logNorm X s (Quot.out q : mcPts P) := by
  have : Nonempty K := hP.1
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) =>
      Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).h z)) = Fin.elim0 :=
    funext fun j => j.elim0
  unfold arInt
  rw [hφ]
  exact PtsIntegralPoints.homogProof K ι P _ hP.2.1.2.1 (HilbertSamuel.CurvePointsFinite.proof K ι P hP)
    fun c z hc _ => logNorm_smul hXa hs c z hc


end CurveRationalSectionSum


end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights.Inter

theorem GenDeg.of_found (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement :=
  PushforwardArithIntersection.proof arithVarZero hRat hCyc hInt

theorem GenDeg.of_pts (hPts : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) (hSec : IntersectionWithSection.Statement)
    (hCyc : ArithmeticIntersectionCycle.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement :=
  GenDeg.of_found (RatR.proof hPts) hCyc (ArithmeticIntersectionIntegral.proof hPts hSec)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem proof : ComponentsGenericCount.Statement := by
  classical
  intro n d F A hF hinc
  have hfib : ∀ y, {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} = ⋃ J ∈ F, _root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y := by
    intro y; ext x; simp only [_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]; tauto
  have hcard : ∀ J ∈ F, ∀ y, (_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).encard ≤ (projDegree J A : ℕ∞) := by
    intro J hJ y
    obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2 y
    rw [← hfin.cast_ncard_eq]; exact_mod_cast hle
  refine ⟨fun y => ?_, ?_⟩
  · rw [hfib, Nat.cast_sum]
    exact (encard_biUnion_le F _).trans (Finset.sum_le_sum fun J hJ => hcard J hJ y)
  obtain ⟨Δ₁, hΔ₁, hΔ₁y⟩ := exists_prod_ne_zero F
    (fun J P => ∀ y, eval y P ≠ 0 → (_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite ∧ (_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).ncard = projDegree J A ∧
      ∀ x ∈ _root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
        DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ g y' ∈ zeroSet J)
    (fun J hJ => by
      obtain ⟨P, hP, hPy⟩ :=
        ComplexSets.DiscriminantCover.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2
      refine ⟨P, hP, fun y hy => ?_⟩
      obtain ⟨hfin, hc, hsec⟩ := hPy y hy
      refine ⟨hfin, hc, fun x hx => ?_⟩
      obtain ⟨U, V, g, hU, hyU, -, -, hg, hgx, hAg, hZ⟩ := hsec x hx
      refine ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨hAg y' hy', ?_⟩⟩
      have hmem : g y' ∈ zeroSet J ∩ V := hZ ▸ Set.mem_image_of_mem g hy'
      exact hmem.1)
  obtain ⟨Δ₂, hΔ₂, hΔ₂y⟩ := exists_prod_ne_zero ((F ×ˢ F).filter fun p => p.1 ≠ p.2)
    (fun p c => ∀ x ∈ zeroSet p.1, x ∈ zeroSet p.2 → eval (A *ᵥ x) c = 0)
    (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact exists_pair_poly p.1 p.2 A (hF _ hp.1.1).1 (hF _ hp.1.1).2.2
        fun h => hp.2 (hinc _ hp.1.2 _ hp.1.1 h).symm)
  refine ⟨Δ₁ * Δ₂, mul_ne_zero hΔ₁ hΔ₂, fun y hy => ?_⟩
  rw [map_mul] at hy
  have h1 := hΔ₁y y (left_ne_zero_of_mul hy)
  have h2 := hΔ₂y y (right_ne_zero_of_mul hy)
  refine ⟨?_, ?_⟩
  · rw [hfib, Nat.cast_sum, encard_biUnion_eq]
    · refine Finset.sum_congr rfl fun J hJ => ?_
      obtain ⟨P, hP, hPy⟩ := h1 J hJ
      obtain ⟨hfin, hc, -⟩ := hP y hPy
      rw [← hfin.cast_ncard_eq, hc]
    · intro J hJ J' hJ' hne
      rw [Set.disjoint_left]
      rintro x ⟨hxJ, hxy⟩ ⟨hxJ', -⟩
      obtain ⟨c, hc, hcy⟩ := h2 (J, J') (by simp [hJ, hJ', hne])
      exact hcy (by rw [← hxy]; exact hc x hxJ hxJ')
  · rintro x ⟨J, hJ, hxJ⟩ hxy
    obtain ⟨P, hP, hPy⟩ := h1 J hJ
    obtain ⟨U, g, hU, hyU, hg, hgx, hsec⟩ := (hP y hPy).2.2 x ⟨hxJ, hxy⟩
    exact ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨(hsec y' hy').1, J, hJ, (hsec y' hy').2⟩⟩

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.SectionBounded

noncomputable section


open CurveVerticalPointSurjective in
theorem CurveVertPointSurj.proof (hFin : CurveRingFinite.Statement) (hC : CurveClosedPointChart.Statement) :
    CurveVertPointSurj.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hP hs hsP m hm hlen
  have hfin := hFin K ι Ω y hP
  obtain ⟨c, hyc, hrat⟩ := hC K ι Ω y hP m hm
  have hrat' := hrat
  have : m.IsPrime := hm.isPrime
  have hYne : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)

  have hunit : ∀ b : m.primeCompl, IsUnit ((curveRing y).subtype (b : curveRing y)) := by
    intro b
    refine isUnit_iff_ne_zero.mpr fun h => b.2 ?_
    have hb0 : (b : curveRing y) = 0 := Subtype.ext h
    rw [hb0]
    exact m.zero_mem
  let L := Localization.AtPrime m
  let φ : L →+* Ω := IsLocalization.lift hunit
  have hinj0 : Function.Injective (algebraMap (curveRing y) L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors m)
  have hφinj : Function.Injective φ :=
    (IsLocalization.lift_injective_iff hunit).mpr fun x x' =>
      ⟨fun h => by rw [hinj0 h], fun h => by rw [Subtype.val_injective h]⟩
  have hφB : ∀ x : curveRing y, φ (algebraMap _ L x) = x := fun x => IsLocalization.lift_eq hunit x
  have hφmk : ∀ (a : curveRing y) (b : m.primeCompl) (v : Ω),
      φ (IsLocalization.mk' L a b) = v ↔ (a : Ω) = ((b : curveRing y) : Ω) * v :=
    fun a b v => IsLocalization.lift_mk'_spec hunit a v b

  choose α β hβ hαβ using hrat
  let ρ : (Σ k, ι k) → L := fun p => IsLocalization.mk' L (α p) (⟨β p, hβ p⟩ : m.primeCompl)
  have hφρ : ∀ p, φ (ρ p) = y p / y ⟨p.1, c p.1⟩ := fun p => (hφmk _ _ _).mpr (hαβ p).symm
  have hφev : ∀ {g : MRing ι} {e : K → ℕ}, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      φ (aeval ρ g) = aeval y g * (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹ := by
    intro g e hg
    rw [ringHom_aeval φ ρ g, show (fun p => φ (ρ p)) = fun p => y p / y ⟨p.1, c p.1⟩ from funext hφρ]
    exact CurveVerticalPointResidue.aeval_div y c g e hg
  have hevB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → aeval ρ g = algebraMap _ L x := by
    intro g e x hg hgx
    apply hφinj
    rw [hφev hg, hφB, hgx, mul_assoc, mul_inv_cancel₀ (hYne e), mul_one]

  let r : (Σ k, ι k) → IsLocalRing.ResidueField L := fun p => IsLocalRing.residue L (ρ p)
  have hWform : ∀ {g : MRing ι} {e : K → ℕ}, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      (g ∈ mCoordIdeal r ↔ aeval ρ g ∈ IsLocalRing.maximalIdeal L) := by
    intro g e hg
    rw [_root_.GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointSurjective.mem_mCoordIdeal_iff r hg, ← IsLocalRing.residue_eq_zero_iff, ringHom_aeval]
  have hWB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → (g ∈ mCoordIdeal r ↔ x ∈ m) := by
    intro g e x hg hgx
    rw [hWform hg, hevB x hg hgx]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff L m x
  have hXc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal r := by
    intro k
    have hρ1 : ρ ⟨k, c k⟩ = 1 := hφinj (by rw [hφρ, map_one, div_self (hyc k)])
    rw [hWform (homog_X ⟨k, c k⟩), aeval_X, hρ1]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hWprime : (mCoordIdeal r).IsPrime := RingHom.ker_isPrime _
  have hPW : mCoordIdeal y ≤ mCoordIdeal r := by
    obtain ⟨S, hS, hPS⟩ := CoordinateConeArithVar.isMultiHomogIdeal y
    intro f hfP
    rw [hPS] at hfP
    refine (Ideal.span_le.mpr ?_) hfP
    intro f hf
    obtain ⟨e, he⟩ := hS f hf
    have hfP' : f ∈ mCoordIdeal y := by rw [hPS]; exact Ideal.subset_span hf
    have hf0 : aeval y f = ((0 : curveRing y) : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k := by
      rw [(_root_.GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointSurjective.mem_mCoordIdeal_iff y he).mp hfP']
      simp
    exact (hWB 0 he hf0).mpr m.zero_mem

  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ s)
  dsimp only at hab
  have hbx : ((b : curveRing y) : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k := by
    have h1 := hφev hs
    rw [← hab] at h1
    rw [(hφmk a b _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne d)]
  have hlenA : locLen m (curveRing y ⧸ Ideal.span {a}) ≠ 0 := by
    rwa [← CurveSectionQuotLocal.proof K ι Ω y s d hP hs hsP m c hm.isPrime hyc hrat' a b b.2 hbx]
  have ham : a ∈ m := by
    by_contra h
    exact hlenA (locLen_quot_eq_zero m h)
  have hsW : s ∈ mCoordIdeal r := by
    rw [hWform hs, ← hab]
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a b).mpr ham
  have hJW : mCoordIdeal y ⊔ Ideal.span {s} ≤ mCoordIdeal r :=
    sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)

  have hcurve : curvePtIdeal y (mCoordIdeal r) = m := by
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro x ⟨e, g, h, hg, hh, hgW, hhW, hx⟩
      have heq : algebraMap _ L x * aeval ρ h = aeval ρ g := by
        apply hφinj
        rw [map_mul, hφB, hφev hh, hφev hg, ← hx]
        ring
      have hmem : algebraMap _ L x * aeval ρ h ∈ IsLocalRing.maximalIdeal L := by
        rw [heq]
        exact (hWform hg).mp hgW
      rcases (IsLocalRing.maximalIdeal.isMaximal L).isPrime.mem_or_mem hmem with h1 | h1
      · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L m x).mp h1
      · exact absurd ((hWform hh).mpr h1) hhW
    · intro x hx
      obtain ⟨e, g, hg, hgx⟩ := exists_form y c hyc x
      have hgW : g ∈ mCoordIdeal r := (hWB x hg hgx).mpr hx
      have hXW : chartMon c e ∉ mCoordIdeal r := chartMon_notMem hWprime hXc e
      have hval : (x : Ω) * aeval y (chartMon c e) = aeval y g := by
        rw [aeval_chartMon, hgx]
      have key : x ∈ {b : curveRing y | ∃ (d : K → ℕ) (g h : MRing ι),
          _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h d ∧ g ∈ mCoordIdeal r ∧ h ∉ mCoordIdeal r ∧
            (b : Ω) * aeval y h = aeval y g} :=
        ⟨e, g, chartMon c e, hg, homog_chartMon c e, hgW, hXW, hval⟩
      exact Ideal.subset_span key
  have ha0 : a ≠ 0 := by
    intro h0
    have hx0 : aeval y s ≠ 0 := fun h => hsP ((_root_.GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointSurjective.mem_mCoordIdeal_iff y hs).mpr h)
    have hb0 : ((b : curveRing y) : Ω) ≠ 0 := by
      intro h
      apply b.2
      rw [show (b : curveRing y) = 0 from Subtype.ext h]
      exact m.zero_mem
    have h2 := hbx
    rw [h0, ZeroMemClass.coe_zero, zero_mul] at h2
    exact mul_ne_zero hb0 hx0 h2
  have hWfrac : ∀ {f : MRing ι} {n : K → ℕ}, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n → f ∈ mCoordIdeal r →
      ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧
        (b' : Ω) * aeval y f = (a' : Ω) * ∏ k, y ⟨k, c k⟩ ^ n k := by
    intro f n hf hfW
    obtain ⟨⟨a', b'⟩, hab'⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ f)
    dsimp only at hab'
    refine ⟨a', b', ?_, b'.2, ?_⟩
    · have h1 := (hWform hf).mp hfW
      rw [← hab'] at h1
      exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a' b').mp h1
    · have h1 := hφev hf
      rw [← hab'] at h1
      rw [(hφmk a' b' _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne n)]

  have hmin : ∀ Q : Ideal (MRing ι), Q.IsPrime → mCoordIdeal y ⊔ Ideal.span {s} ≤ Q →
      Q ≤ mCoordIdeal r → mCoordIdeal r ≤ Q := by
    intro Q hQ hJQ hQW
    have hPQ : mCoordIdeal y ≤ Q := le_trans le_sup_left hJQ
    have hsQ : s ∈ Q := hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    exact le_of_minimal y c hyc hfin m hm (mCoordIdeal r) Q hQ hPQ hQW hXc hWB hWfrac
      (CoordinateConeArithVar.isMultiHomogIdeal r) ha0 hs hsQ hbx
  have hmp : mCoordIdeal r ∈ (mCoordIdeal y ⊔ Ideal.span {s}).minimalPrimes :=
    ⟨⟨hWprime, hJW⟩, fun Q hQ hQW => hmin Q hQ.1 hQ.2 hQW⟩
  exact ⟨mCoordIdeal r, ⟨hmp, fun k => ⟨c k, hXc k⟩⟩, hcurve⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem pot_fin_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (M : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (L : Fin e → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem PoincareLelongRegularised.proof (hInt : PtsIntegrableStatement)
    (hMeas : GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement) : PoincareLelongRegularised.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB _ hs
  obtain ⟨a, ha, hsa, hsP⟩ := id hs
  have hM : ∀ j, IsSmoothHerm ((Fin.cons B L : Fin (n + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) := fun j =>
    Fin.cases (by simpa using hB) (fun i => by simpa using hL i) j
  have hlim := GroundTheory.Heights₂.Heights.Inter.PtsRegLimit.proof hInt
    (GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.proof hInt hMeas) K ι P (n + 1) (Fin.cons B L) A s
    ⟨a, ha, hsa⟩ hP hM hA hsP
  rw [pot_fin_cons] at hlim
  have hg : ∀ ε, (fun z => Real.log ((GroundTheory.Heights₂.Heights.Inter.regLine A s ⟨a, ha, hsa⟩ ε).h z)) =
      regLog A s ε := by
    intro ε
    funext z
    rw [GroundTheory.Heights₂.Heights.Inter.log_regLine_h]
    rfl
  simpa only [hg] using hlim

end GroundTheory.Heights₂.Heights.Targets
end
