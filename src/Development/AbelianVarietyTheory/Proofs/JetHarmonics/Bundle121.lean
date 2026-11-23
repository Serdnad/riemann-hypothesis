module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle111
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle104
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle053
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds
public import Development.AutomorphicArithmetic.CMTraceForms.SplitPlacesDiscriminantDepthOfSplitAt
public import Formalism.LocalRingCardinality.Bundle002
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle114
public import Formalism.HermitianCurvature.Bundle009
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle105
public import Formalism.RealPlaceAnalysis.Bundle005
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.Bundle001
import Formalism.HermitianCurvature.StatementWd

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.DualStepBound

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) :
    n1 (ν - Pi.single s 1 : Fin n → ℤ) ≤ n1 ν + 1 := by
  unfold n1
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa using Int.natAbs_sub_le (ν i) ((Pi.single s 1 : Fin n → ℤ) i)

theorem sum_mem_sm {k r : ℕ} (R : Rep k r) {ι : Type} [Fintype ι] (x : ι → R.H) (hx : ∀ c, x c ∈ R.sm) :
    ∑ c, x c ∈ R.sm :=
  R.smSub.sum_mem (fun c _ => hx c)

theorem dual_step_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s κ₀ hκ
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hν1 : ∀ t, n1 (ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) ≤ q0 :=
    fun t => (lOneNorm_sub_single_one_le ν t).trans hν
  have hDS : (R ν).IsDS _ _ := hFam ν hν0
  have hDS1 : ∀ t, (R (ν - Pi.single t 1)).IsDS (PI.BesselPeriodGGP.eps48 k r)
      (fun a => lam a + ((ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ)) := fun t => hFam _ (hν1 t)
  have hpar : ∀ t, (fun a => lam a + ((ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ))
      = (fun a => lam a + (ν a : ℝ)) - Pi.single t 1 := by
    intro t
    funext a
    by_cases hat : a = t
    · subst hat
      simp
      ring
    · simp [Pi.single_eq_of_ne hat]
  have hDS2 : ∀ t, (R (ν - Pi.single t 1)).IsDS (PI.BesselPeriodGGP.eps48 k r)
      ((fun a => lam a + (ν a : ℝ)) - Pi.single t 1) := fun t => hpar t ▸ hDS1 t
  obtain ⟨hBe, hdg, hdeg⟩ := hSF ν hν0
  obtain ⟨hBe1, hdg1, hdeg1⟩ := hSF _ (hν1 s)
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.dual_tensor_bessel_moment hH k r _ _ (R ν) (fun s => R (ν - Pi.single s 1)) io pr Wp z π u
    μW μN μG νq (l ν) hNum.1 hDS hDS2 hT.raw hSide hBe.1 s
  have hdual := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν) (fun s => R (ν - Pi.single s 1))
    io pr ep _ _ _ Wp z π u μW μN μG νq (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (l ν) hDS hDS2
    (GlobalTheory.isFRep_dualM k r) hT hSide
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hSide.1 g hg).2) hBe hnz s
    (l (ν - Pi.single s 1)) hBe1).2 κ₀ hκ
  obtain ⟨v, hv, hv0⟩ := hnz
  have hy : ∑ d, pr s d (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d) ∈ (R (ν - Pi.single s 1)).sm :=
    sum_mem_sm _ _ fun d => (hT.raw.pr_sm s d).mem _ ((R ν).smSub.smul_mem _ hv)
  have e1 := hdual _ hy
  rw [hcv v hv, hκ v hv, smul_smul] at e1
  have e2 : c = (ep s : ℂ) * star κ₀ * κ₀ := smul_left_injective ℂ hv0 e1
  have hep : ‖(ep s : ℂ)‖ = 1 := by
    rcases hT.ep_sq s with h' | h' <;> simp [h']
  have e3 : ‖κ₀‖ ^ 2 = ‖c‖ := by
    rw [e2, norm_mul, norm_mul, hep, norm_star]; ring
  obtain ⟨c₀, hc₀, hdegs⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r (PI.BesselPeriodGGP.eps48 k r) μG
    hSide.2.2.2.2.2.2.1
  have hKS : PI.KFinSmooth := hH.1.2.2.1
  have d0 : dg ν = c₀ * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := by
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hKS k r _ _ _ hDS).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [← hdeg w hw0, (hdegs _ _ hDS).1 w hw0]
  have d1 : dg (ν - Pi.single s 1) = c₀ * Formalism.QuantumDeterminants.fdegHC
      (fun a => lam a + ((ν - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ)) := by
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hKS k r _ _ _ (hDS1 s)).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [← hdeg1 w hw0, (hdegs _ _ (hDS1 s)).1 w hw0]
  have hratio := (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hNum ν hν0).2.2 s
  have hp7 := GlobalTheory.PieriBound.lowering_bound k r lam u b bv ga h q0 hNum ν hν0 s
  have hgap := ((GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum).2 ν hν0).2.2.2
  have hB : (∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))|) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun t ht => abs_ne_zero.2 ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ht) with h' | h'
    · have := hgap t s h'
      linarith
    · have := hgap s t h'
      linarith
  rw [Finset.prod_div_distrib] at hratio
  have hq : dg ν / dg (ν - Pi.single s 1)
      = (∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))|) /
        ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| := by
    rw [d0, d1, mul_div_mul_left _ _ hc₀.ne', ← inv_div, hratio, inv_div]
  rw [mul_div_assoc, hq, e3, hc, mul_assoc, div_mul_div_cancel₀ hB]
  exact mul_le_mul_of_nonneg_left hp7 hSide.2.1.le

end GlobalTheory.DualStepBound
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselOrbital

theorem bessel_integral_eq_smul : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  classical
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hok hl hl'
  have hpt : ∀ γ ∈ JF.Om k r D.z D.z', ∃ O : Wq →L[ℂ] Wp, ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ X : Wq →L[ℂ] Wp,
      B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ = ⟪l x, X (l' y)⟫_ℂ • O := by
    intro γ hγ
    obtain ⟨A, hA1, hA2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨Bb, hB1, hB2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨O, hO⟩ := GlobalTheory.T.factorisation_of_conjHomogeneous_and_homogeneous R.TK Wp Wq (fun x => l x) (fun y => l' y)
      (fun x y X => B.JF D (fun g => ⟪(x : R.H), R.σ g y⟫_ℂ • X) γ)
      (fun y => A y) (fun x => Bb x) (fun y => hA1 y) (fun x => hB1 x)
      (fun x y X c => hA2 x x.2 y y.2 X c) (fun x y X c => hB2 x x.2 y y.2 X c)
    exact ⟨O, fun x hx y hy X => hO ⟨x, hx⟩ ⟨y, hy⟩ X⟩
  choose! OO hOO using hpt
  have hint : ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z',
      Integrable (JF.integrand D F γ) D.μSS := by
    intro F s hF γ hγ
    exact (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ F (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hok).1
      ((GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH k r ε mu h R Wp Wq l l' F s hDS hgap hok hF).2 0)).1 γ hγ
  refine ⟨OO, fun F s hF γ hγ => ⟨hint F s hF γ hγ, ?_⟩⟩
  obtain ⟨m, x, y, X, hxy, hFe, hs⟩ := hF
  have hγG : γ ∈ GG k r := hγ.1
  obtain ⟨hloc, -, hsum, -⟩ := GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum k r Wp Wq D γ hγG
  rw [(hloc F (fun g => ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i) hFe).1,
    hsum (Fin m) (fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i) ?_, hs, Finset.sum_smul]
  · exact Finset.sum_congr rfl fun i _ => hOO γ hγ _ (hxy i).1 _ (hxy i).2 _
  · intro i
    refine hint _ ⟪l (x i), X i (l' (y i))⟫_ℂ ⟨1, fun _ => x i, fun _ => y i, fun _ => X i,
      fun _ => hxy i, fun g _ => ?_, ?_⟩ γ hγ
    · simp
    · simp

end GlobalTheory.BesselOrbital
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMoveIso

open scoped Matrix

theorem transport {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A)
    (Lh : G → AddSubgroup (Fin n → A)) (hL : ∀ g z, z ∈ Lh g ↔ ∃ y ∈ Lh 1, (f g).1 *ᵥ y = z) (N : ℕ) (δ u k : G)
    (hk : Lh k = Lh 1) :
    (∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k)) ∧
      ∀ x x' a b, (∃ w ∈ Lh 1, (f k).1 *ᵥ a = b + N • w) → (∃ w ∈ Lh u, x - (f u).1 *ᵥ b = N • w) →
        (∃ w ∈ Lh (δ * u * k), x' - (f (δ * u * k)).1 *ᵥ a = N • w) →
        ∃ w ∈ Lh (δ * u * k), (f δ).1 *ᵥ x - x' = N • w := by
  have hmul : ∀ (a b : G) z, (f (a * b)).1 *ᵥ z = (f a).1 *ᵥ ((f b).1 *ᵥ z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1 *ᵥ z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  have h1 : ∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k) := by
    intro z
    rw [hL u, hL (δ * u * k)]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (hL k y).1 (hk ▸ hy)
      exact ⟨w, hw, by rw [hmul, hmul]⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨(f k).1 *ᵥ y, hk ▸ (hL k _).2 ⟨y, hy, rfl⟩, ?_⟩
      have := congrArg (fun v => (f δ⁻¹).1 *ᵥ v) h
      simp only [← hmul, inv_mul_cancel, hone] at this
      rw [← this, ← hmul, mul_assoc, inv_mul_cancel_left]
  refine ⟨h1, ?_⟩
  rintro x x' a b ⟨y, hy, ey⟩ ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  refine ⟨(f δ).1 *ᵥ w - (f δ).1 *ᵥ ((f u).1 *ᵥ y) - w',
    sub_mem (sub_mem ((h1 w).1 hw) ((h1 _).1 ((hL u _).2 ⟨y, hy, rfl⟩))) hw', ?_⟩
  rw [sub_eq_iff_eq_add.1 e, sub_eq_iff_eq_add.1 e', hmul, hmul, ey]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel

theorem map_mem_half {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] (I : Ideal R) (s : A →ₗ[R] A) :
    ∀ a ∈ I • (⊤ : Submodule R A), s a ∈ I • (⊤ : Submodule R A) := by
  intro a ha
  refine Submodule.smul_induction_on ha (fun m hm b _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul hm trivial
  · rw [map_add (f := _)]
    exact add_mem hx hy



theorem marked_isometry : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (X X' : Data D.host.E r) (A A' : Datum H) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (h γ κ : GA D V), ModelW V hr X → ModelW V hr X' → (∀ a b, ((A.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → (∀ a b, ((A'.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → D.host.E) (φ' b))) → γ ∈ GQ V → latGHat V κ = latGHat V 1 → (∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s a)) + l.M • w) → Marked V hr io l X.Λ (fun a => (φ (t a) : Fin r → D.host.E)) h → Marked V hr io l X'.Λ (fun a => (φ' (t' a) : Fin r → D.host.E)) (γ * h * κ) → ∃ gam : A.La ≃ₗ[𝓞 D.host.E] A'.La, (∀ a b, A'.EF (gam a) (gam b) = A.EF a b) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ x, gam (t (s a)) = t' a + l.M • x := by
  intro D V H Dw l r hr io X X' A A' φ φ' t t' s h γ κ hW hW' hE hE' hγ hκ hs hm hm'
  subst hr
  obtain ⟨hΛ, hm⟩ := hm
  obtain ⟨hΛ', hm'⟩ := hm'
  obtain ⟨δ, hδu, hδf, -⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨ht1, ht2⟩ := transport (finHom V) (latGHat V) (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) l.M γ h κ hκ
  have hmem : ∀ v, v ∈ X.Λ ↔ finVec V v ∈ latGHat V h := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V h).1, ← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hmem' : ∀ v, v ∈ X'.Λ ↔ finVec V v ∈ latGHat V (γ * h * κ) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hΛ']
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ X.Λ ↔ δ.1 *ᵥ v ∈ X'.Λ := fun v => by
    rw [hmem, hmem', ht1, hδf]
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let ψ : X.Λ ≃ₗ[𝓞 D.host.E] X'.Λ :=
    { toFun := fun v => ⟨δ.1 *ᵥ v.1, (hlat _).1 v.2⟩
      invFun := fun v => ⟨(δ⁻¹).1 *ᵥ v.1, (hlat _).2 (by rw [hri]; exact v.2)⟩
      map_add' := fun u v => Subtype.ext (Matrix.mulVec_add δ.1 u.1 v.1)
      map_smul' := fun a v => Subtype.ext (Matrix.mulVec_smul δ.1 a v.1)
      left_inv := fun v => Subtype.ext (hli _)
      right_inv := fun v => Subtype.ext (hri _) }
  let gam : A.La ≃ₗ[𝓞 D.host.E] A'.La := φ.trans (ψ.trans φ'.symm)
  have hgam : ∀ a, (φ' (gam a) : Fin V.rank → D.host.E) = δ.1 *ᵥ (φ a : Fin V.rank → D.host.E) := by
    intro a
    simp [gam, ψ]
  have hG : X.Gm = -V.gram.transpose := hW.1
  have hG' : X'.Gm = -V.gram.transpose := hW'.1
  have hξ : X'.ξ0 = X.ξ0 := hW'.2.trans hW.2.symm
  refine ⟨gam, fun a b => ?_, fun a ha => ?_⟩
  · have h1 := hE' (gam a) (gam b)
    rw [hgam, hgam, hG', hξ, hδu, ← hG, ← hE a b] at h1
    exact_mod_cast h1
  · obtain ⟨z, hz, e⟩ := ht2 (finVec V (φ (t (s a)) : Fin V.rank → D.host.E))
      (finVec V (φ' (t' a) : Fin V.rank → D.host.E)) _ _ (hs a) (hm _ (map_mem_half _ s a ha)) (hm' a ha)
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div V l.M hM0 (δ.1 *ᵥ (φ (t (s a)) : Fin V.rank → D.host.E) -
      (φ' (t' a) : Fin V.rank → D.host.E)) z (by
        rw [← e, hδf]
        funext i
        exact TensorProduct.tmul_sub _ _ _)
    refine ⟨φ'.symm ⟨w, (hmem' w).2 (hw ▸ hz)⟩, φ'.injective (Subtype.ext ?_)⟩
    rw [hgam, sub_eq_iff_eq_add'.1 e', map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
    rfl

end GlobalTheory.ShortMoveIso
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.CharDepth

theorem twoPlaces_host : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), H.d = D.host.d → ∀ (p : ℕ) [Fact p.Prime], p ∈ D.host.small → UpperTheory.Depth.SplitAt H.d p ∧ UpperTheory.Depth.SplitPlaces p H D.R.f (D.host.vdH p) ∧ 0 ≤ D.host.vdH p ∧ D.host.vdH p ≤ vd2 D := by
  intro D H hd p _ hp
  have hpp : p.Prime := Fact.out
  have hs : UpperTheory.Depth.SplitAt H.d p := by
    by_cases h2 : p = 2
    · exact Or.inl h2
    · exact Or.inr (by rw [hd]; exact D.host.QS_split p hpp h2 (D.host.mem_small_iff.1 hp).2)
  obtain ⟨h1, -, -, -, h5⟩ := UpperTheory.cmDatum_discriminantDepth_bounds D.host.toHostAx
  refine ⟨hs, ?_, D.host.vdH_nonneg p, (h1 p hp).1.trans (h1 p hp).2⟩
  rw [h5 p]
  exact UpperTheory.splitPlaces_discriminantDepth_of_splitAt p D.host.E H hs D.R.f D.host.finrank_E'

end GlobalTheory.CharDepth
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.exists_dual_matrix_frame_fvec : ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (e : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1)), inWb k r z' → 0 < Tz k r z' → ∃ Q : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ, Q.det ≠ 0 ∧ (∀ (i j : Fin (r + 1)), ∑ d, Q (Fin.castAdd (r + k) i) d * fvec k r z' j (e d) = if i = j then 1 else 0) ∧ ∀ (i : Fin (r + k)) (j : Fin (r + 1)), ∑ d, Q (Fin.natAdd (r + 1) i) d * fvec k r z' j (e d) = 0 := by
  first | exact @GlobalTheory.HatNF.DualFrame.exists_dual_matrix | exact GlobalTheory.HatNF.DualFrame.exists_dual_matrix | (intros; apply GlobalTheory.HatNF.DualFrame.exists_dual_matrix <;> assumption)
end

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem casimir_eigenspace_irred_dual_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + (n : ℂ)) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ Module.End.eigenspace Om (β + L l + (n : ℂ)) ≤ CapSp Et (shf β (Function.update L l (L l - 1))) := by
  intro V _ _ _ n E Et Om β L l hH hA hEt hOm
  classical
  obtain ⟨hgl, hAt, -, hcomm⟩ := tensor_dual_standard_rel V n E Et Om hH.gl hA hEt hOm
  set S := Module.End.eigenspace Om (β + L l + (n : ℂ)) with hS
  have hstab : Stab Et S := by
    intro a b v hv
    rw [hS, Module.End.mem_eigenspace_iff] at hv ⊢
    have := LinearMap.congr_fun (hcomm a b) v
    simp only [Module.End.mul_apply] at this
    rw [this, hv, map_smul]
  have hdec : SDec (shf β L) := by
    intro a b hab
    have h := hH.anti hab
    refine ⟨(L a - L b - 1).toNat, ?_⟩
    have h2 : (((L a - L b - 1).toNat : ℕ) : ℤ) = L a - L b - 1 := Int.toNat_of_nonneg (by omega)
    have h3 : (((L a - L b - 1).toNat : ℕ) : ℂ) = (L a : ℂ) - L b - 1 := by exact_mod_cast h2
    rw [h3]; simp only [shf]; ring
  have hwt : ∀ (ν : Fin (n + 1) → ℂ) (v : V), v ≠ 0 → IsHW E ν v →
      ∀ j, ν j = β + L j + ((j : ℕ) : ℂ) := by
    intro ν v hv hw j
    have hm : v ∈ CapSp E (shf β L) := mem_CapSp.mpr fun w => hH.cap w v
    have hne : CapSp E (shf β L) ≠ ⊥ := fun h => hv (by rw [h] at hm; simpa using hm)
    exact (Formalism.FourierDecayAlt.P.capelli_singular V (n + 1) E _ hH.gl hne).2 hdec ν v hm hv hw j
  have hkey : ∀ (θ : Fin (n + 1) → ℂ) (y : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S → y ≠ 0 →
      IsHW Et θ y → y l ≠ 0 ∧ IsHW E (fun j => β + L j + ((j : ℕ) : ℂ)) (y l) ∧
        θ = fun j => β + L j + ((j : ℕ) : ℂ) - if j = l then 1 else 0 := by
    intro θ y hy hy0 hw
    rw [hS, Module.End.mem_eigenspace_iff] at hy
    obtain ⟨c, hc, hwc, hlam⟩ :=
      hw_component_tensor_dual_standard V n E Et Om θ _ y hEt hOm hy0 hw hy
    have h1 := hwt _ _ hc hwc
    have h2 := h1 c
    simp only [if_true] at h2
    have h3 : (L l : ℂ) = L c := by linear_combination hlam + h2
    have h4 : l = c := hH.anti.injective (by exact_mod_cast h3)
    subst h4
    refine ⟨hc, ?_, ?_⟩
    · have : (fun j => β + L j + ((j : ℕ) : ℂ)) = fun a => θ a + if a = l then 1 else 0 :=
        funext fun j => (h1 j).symm
      rw [this]; exact hwc
    · funext j
      rw [← h1 j]; ring
  have hsub : ∀ (ν : Fin (n + 1) → ℂ) (v : V), IsHW E ν v →
      IsHW (subA E) (fun a => ν a.castSucc) v := by
    intro ν v hw
    exact ⟨fun a => hw.1 _, fun a b hab => hw.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)⟩
  have hprop : ∀ (θ θ' : Fin (n + 1) → ℂ) (y y' : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S →
      y ≠ 0 → IsHW Et θ y → y' ∈ S → y' ≠ 0 → IsHW Et θ' y' → ∃ t : ℂ, y' = t • y := by
    intro θ θ' y y' hy hy0 hw hy' hy0' hw'
    obtain ⟨a1, a2, a3⟩ := hkey θ y hy hy0 hw
    obtain ⟨b1, b2, b3⟩ := hkey θ' y' hy' hy0' hw'
    obtain ⟨t, ht⟩ := Formalism.FourierDecayAlt.P.multiplicity_one V n E _ _ _ hH.gl hH.irr (hsub _ _ a2)
      (hsub _ _ b2) a1
    refine ⟨t, ?_⟩
    by_contra hne
    have hθ : θ' = θ := b3.trans a3.symm
    rw [hθ] at hw'
    have hz : IsHW Et θ (y' - t • y) := by
      refine ⟨fun a => ?_, fun a b hab => ?_⟩
      · rw [map_sub, map_smul, hw.1, hw'.1, smul_sub, smul_comm]
      · rw [map_sub, map_smul, hw.2 a b hab, hw'.2 a b hab, smul_zero, sub_zero]
    have := (hkey θ _ (S.sub_mem hy' (S.smul_mem t hy)) (sub_ne_zero.mpr hne) hz).1
    apply this
    rw [PiLp.sub_apply, PiLp.smul_apply, ht, sub_self]
  have hirr : ∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' →
      S' = ⊥ ∨ S' = S := by
    intro S' hle hst
    by_contra hcon
    push_neg at hcon
    obtain ⟨h0, h1⟩ := hcon
    have hT : S'ᗮ ⊓ S ≠ ⊥ := by
      intro h
      have := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
      rw [h, sup_bot_eq] at this
      exact h1 this
    have hTs : Stab Et (S'ᗮ ⊓ S) := by
      intro a b v hv
      refine ⟨?_, hstab a b v hv.2⟩
      have hv1 : v ∈ S'ᗮ := hv.1
      change Et a b v ∈ S'ᗮ
      rw [Submodule.mem_orthogonal] at hv1 ⊢
      intro u hu
      rw [← hAt]
      exact hv1 _ (hst b a u hu)
    obtain ⟨θ, y, hy, hy0, hw, -⟩ :=
      Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S' hst h0
    obtain ⟨θ', y', hy', hy0', hw', -⟩ :=
      Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl _ hTs hT
    obtain ⟨t, ht⟩ := hprop θ θ' y y' (hle hy) hy0 hw hy'.2 hy0' hw'
    have hm : y' ∈ S' := ht ▸ S'.smul_mem t hy
    have hm2 : y' ∈ S'ᗮ := hy'.1
    exact hy0' (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hm2 y' hm))
  refine ⟨hstab, hirr, ?_⟩
  by_cases h0 : S = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨θ, y, hy, hy0, hw, -⟩ :=
    Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S hstab h0
  obtain ⟨-, -, hθ⟩ := hkey θ y hy hy0 hw
  have hcap : y ∈ CapSp Et (shf β (Function.update L l (L l - 1))) := by
    rw [mem_CapSp]
    intro w
    rw [qDetHW _ (n + 1) Et θ y hgl hw w]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hθ]
    by_cases hk : k = l
    · subst hk
      simp only [if_true, Function.update_self]
      push_cast; ring
    · simp only [hk, if_false, Function.update_of_ne hk]
      ring
  have hcs := (Formalism.FourierDecayAlt.P.capelli_stabilizer _ (n + 1) Et
    (shf β (Function.update L l (L l - 1))) hgl).1
  rcases hirr (CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S) inf_le_right
    (fun a b v hv => ⟨hcs a b v hv.1, hstab a b v hv.2⟩) with h | h
  · have : y ∈ CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S := ⟨hcap, hy⟩
    rw [h] at this
    exact absurd (by simpa using this) hy0
  · exact inf_eq_right.mp h

end GlobalTheory
end
