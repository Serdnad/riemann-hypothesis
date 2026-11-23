module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle011
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle015
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle053
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle013
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle010
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle006
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentEstimateStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselOrbital

theorem bessel_integral_eq_smul : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
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
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPairing

theorem integrable_inner_of_memLp {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) μ := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  refine h.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem add_mem_sm {k r : ℕ} (R : BranchingSupport.Rep k r) {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    v + w ∈ R.sm := by
  simp only [BranchingSupport.Rep.sm, PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec] at hv hw ⊢
  letI : NormedAddCommGroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedSpace
  intro g₀ h₀
  obtain ⟨U1, F1, hU1, h1, hF1, e1⟩ := hv g₀ h₀
  obtain ⟨U2, F2, hU2, h2, hF2, e2⟩ := hw g₀ h₀
  refine ⟨U1 ∩ U2, fun x => F1 x + F2 x, hU1.inter hU2, ⟨h1, h2⟩,
    (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  show (R.σ g) (v + w) = F1 g + F2 g
  rw [map_add (f := _)]
  exact congrArg₂ (· + ·) (e1 g hg.1 hgH) (e2 g hg.2 hgH)

private theorem smul_mem_sm' {k r : ℕ} (R : BranchingSupport.Rep k r) (c : ℂ) {v : R.H} (hv : v ∈ R.sm) :
    c • v ∈ R.sm := by
  simp only [BranchingSupport.Rep.sm, PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec] at hv ⊢
  letI : NormedAddCommGroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedSpace
  intro g₀ h₀
  obtain ⟨U1, F1, hU1, h1, hF1, e1⟩ := hv g₀ h₀
  refine ⟨U1, fun x => c • F1 x, hU1, h1, hF1.const_smul c, fun g hg hgH => ?_⟩
  show (R.σ g) (c • v) = c • F1 g
  rw [map_smul]
  exact congrArg (c • ·) (e1 g hg hgH)

private theorem zero_mem_sm {k r : ℕ} (R : BranchingSupport.Rep k r) : (0 : R.H) ∈ R.sm := by
  simp only [BranchingSupport.Rep.sm, PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec]
  letI : NormedAddCommGroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedSpace
  intro g₀ _
  refine ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
  show (R.σ g) 0 = 0
  exact map_zero _

theorem pairing : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  intro hyp k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ z π u μW μN μG νq om Bm BI β hR hRI hinj hT hS
    hB hOr hev I hIso y hy a w hw
  have hK : PI.KFinSmooth := hyp.1.2.2.1
  have hpr : ∀ J c, BranchingSupport.SmMap R (RI J) (pr J c) := by
    cases hT
    assumption
  have hv : ∀ J, (∑ c, pr J c (BranchingSupport.tm R a w c)) ∈ (RI J).sm := by
    intro J
    refine Finset.sum_induction _ (· ∈ (RI J).sm) (fun p q hp hq => add_mem_sm (RI J) hp hq)
      (zero_mem_sm (RI J)) ?_
    intro c _
    obtain ⟨hmem, -, -, -⟩ := hpr J c
    exact hmem _ (smul_mem_sm' R (a c) hw)
  have hae := (Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hR hS).1
  have hpt : ∀ᵐ x ∂νq, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ =
      ∑ J, β J * ⟪BI I ((RI I).σ (Matrix.of x) y), BI J ((RI J).σ (Matrix.of x) (∑ c, pr J c (BranchingSupport.tm R a w c)))⟫_ℂ := by
    filter_upwards [hae] with x hx
    rw [Gp91.GlobalTheory.T.tensor_bessel_transfer hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp om Bm BI β hR hRI hT hB.1 hB.2.1 hev a w hw
      (Matrix.of x) hx, inner_sum]
    simp only [inner_smul_right]
  refine (MeasureTheory.integral_congr_ae hpt).trans ?_
  rw [MeasureTheory.integral_finsetSum]
  · rw [Finset.sum_eq_single I]
    · rw [MeasureTheory.integral_const_mul,
        (Gp91.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (BI I) (hRI I) hS hIso).2 _ (hv I) y hy]
    · intro J _ hJI
      rw [MeasureTheory.integral_const_mul]
      rcases hOr J with hJ | hJ
      · rw [Gp91.GlobalTheory.T.isometric_bessel_compare hyp k r ε (muI J) (muI I) (RI J) (RI I) Wp z π u μW μN μG νq (BI J) (BI I)
          (hRI J) (hRI I) (fun h => hJI (hinj h)) hS hJ hIso _ (hv J) y hy, mul_zero]
      · rw [hJ, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ I) h
  · intro J _
    rcases hOr J with hJ | hJ
    · exact (integrable_inner_of_memLp
        ((Gp91.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (BI I) (hRI I) hS hIso).1 y hy)
        ((Gp91.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI J) (RI J) Wp z π u μW μN μG νq (BI J) (hRI J) hS hJ).1 _
          (hv J))).const_mul (β J)
    · simp only [hJ, zero_mul]
      exact MeasureTheory.integrable_zero _ _ _

end GlobalTheory.BesselPairing
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  first | exact @GlobalTheory.BesselConv.be_conv | exact GlobalTheory.BesselConv.be_conv | (intros; apply GlobalTheory.BesselConv.be_conv <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.integrable_coefficient_mul_star_translate : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, Integrable (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ) (μG.prod (μW.prod μN)) := by
  first | exact @GlobalTheory.BesselFubini.integrable_GS | exact GlobalTheory.BesselFubini.integrable_GS | (intros; apply GlobalTheory.BesselFubini.integrable_GS <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

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

theorem dual_step_bound : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s κ₀ hκ
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hν1 : ∀ t, n1 (ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) ≤ q0 :=
    fun t => (lOneNorm_sub_single_one_le ν t).trans hν
  have hDS : (R ν).IsDG _ _ := hFam ν hν0
  have hDS1 : ∀ t, (R (ν - Pi.single t 1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
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
  have hDS2 : ∀ t, (R (ν - Pi.single t 1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
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
end Gp91
end
