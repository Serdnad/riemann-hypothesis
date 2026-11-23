module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle014
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorBesselMoment
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SumNonneg
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle098
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ Bb : R.H → Wp → Wq → Wp, (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = Bb x (X (l' y)) c := by
  first | exact @GlobalTheory.besselJ_coef_through_right | exact GlobalTheory.besselJ_coef_through_right | (intros; apply GlobalTheory.besselJ_coef_through_right <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ A : R.H → Wq → Wq → Wp, (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = A y (ContinuousLinearMap.adjoint X (l x)) c := by
  first | exact @GlobalTheory.BesselFirstLeft.bessel_integrate_left | exact GlobalTheory.BesselFirstLeft.bessel_integrate_left | (intros; apply GlobalTheory.BesselFirstLeft.bessel_integrate_left <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.isometric_bessel_compare : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp) (Bm' : R'.H → Wp), R.IsDG ε mu → R'.IsDG ε mu' → mu ≠ mu' → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → IsIsoB R' z π νq Bm' → ∀ w ∈ R.sm, ∀ y ∈ R'.sm, ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = 0 := by
  first | exact @GlobalTheory.bessel_orth_of_param_ne | exact GlobalTheory.bessel_orth_of_param_ne | (intros; apply GlobalTheory.bessel_orth_of_param_ne <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.dual_tensor_bessel_moment : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (RI : Fin (2 * r + k + 1) → Rep k r) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp), 1 ≤ k → R.IsDG ε mu → (∀ s, (RI s).IsDG ε (mu - Pi.single s 1)) → TensRaw dualM R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π l → ∀ s, ∃ c : ℂ, ‖c‖ = Formalism.QuantumDeterminants.Tz k r z * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ v ∈ R.sm, l (ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (fun c' => io s c' (∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d)))) = c • l v := by
  first | exact @GlobalTheory.bessel_ev_projector_value | exact GlobalTheory.bessel_ev_projector_value | (intros; apply GlobalTheory.bessel_ev_projector_value <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselFubini

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity



theorem integrable_of_growth (hGG : GrowthG) (hGS : GrowthS) : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, Integrable (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ) (μG.prod (μW.prod μN)) := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS v hv w hw
  obtain ⟨hz, hT, -, -, hWh, hNh, hGh, hq⟩ := hS
  have := hWh.1; have := hNh.1; have := hGh.1
  obtain ⟨C0, Ws, -, hdec⟩ := GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok v hv
  set a := aOf r h - 1 with ha_def
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have ha4 := hok.2.2.2
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have ha : 0 < a := by linarith
  have ha2 : AG k r < a / 2 := by linarith
  have hsub : ∀ x y : Mx k r, B.gN (x * y) ≤ B.gN x * B.gN y := fun x y => PI.PolynomialProperness.GN.gN_mul_le x y
  have hNIG : ∀ x ∈ GG k r, B.gN x⁻¹ = B.gN x ∧ 1 ≤ B.gN x :=
    fun x hx => PI.PolynomialProperness.GN.polynomial_normInv k r x hx
  have gN0 : ∀ g : Mx k r, 0 ≤ B.gN g := fun g => Real.sqrt_nonneg _
  set C := max (C0 * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum) 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  have hb : ∀ g ∈ GG k r, ‖⟪v, R.σ g w⟫_ℂ‖ ≤ C * B.gN g ^ (-a) := by
    intro g hg
    have e : -a = 1 - aOf r h := by rw [ha_def]; ring
    rw [e]
    exact (hdec w hw g hg).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN0 g) _))
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hQae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
      Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of q.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hPae)
  have sUH : ∀ p1 p2 : Formalism.QuantumDeterminants.Mt k r, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z → Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r →
      Matrix.of p1 * Matrix.of p2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    fun p1 p2 h1 h2 => DDSmoothness.uh_mul h1.1 h2.1
  have hφ : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) := by
    have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.2.1 : Mx k r)) := continuous_fst.comp continuous_snd
    have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.2.2 : Mx k r)) := continuous_snd.comp continuous_snd
    have h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.1 : Mx k r)) := continuous_fst
    exact (h1.matrix_mul h2).matrix_mul h3
  have hTm : MeasurableSet ((fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (isClosed_UH.preimage hφ).measurableSet
  have hTae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ ((fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    filter_upwards [hQae] with q hq
    exact DDSmoothness.uh_mul (sUH _ _ hq.2.1 hq.2.2) hq.1
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hR.2 w
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hc1 : AEStronglyMeasurable (fun y : Formalism.QuantumDeterminants.Mt k r => ⟪v, R.σ (Matrix.of y) w⟫_ℂ) μG := by
    refine aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r) (μ := μG)
      (s := {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}) ?_ ?_ hGae
    · have h0 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r => R.σ (Matrix.of y) w)
          {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
        hcs.comp hof.continuousOn (fun y hy => hy)
      exact continuousOn_const.inner h0
    · exact (isClosed_UH.preimage hof).measurableSet
  have hc2 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      ⟪v, R.σ (Matrix.of q.2.1 * Matrix.of q.2.2 * Matrix.of q.1) w⟫_ℂ) (μG.prod (μW.prod μN)) :=
    aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μ := μG.prod (μW.prod μN))
      (continuousOn_const.inner (hcs.comp hφ.continuousOn (fun q hq => hq))) hTm hTae
  have h1' : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      ⟪v, R.σ (Matrix.of q.1) w⟫_ℂ) (μG.prod (μW.prod μN)) :=
    AEStronglyMeasurable.comp_fst (μ := μG) (ν := μW.prod μN) hc1
  have hMi : Integrable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (C * C) * (B.gN (Matrix.of q.1) ^ (-(a / 2)) *
        B.gN (Matrix.of q.2.1 * Matrix.of q.2.2) ^ (-(a / 2)))) (μG.prod (μW.prod μN)) :=
    Integrable.const_mul (Integrable.mul_prod (hGG k r μG (a / 2) hGh ha2)
      (hGS k r z μW μN μG νq (a / 2) hz hT hWh hNh hGh hq ha2)) _
  refine Integrable.mono' hMi (h1'.mul (continuous_star.comp_aestronglyMeasurable hc2)) ?_
  filter_upwards [hQae] with q hq
  obtain ⟨hy, hp1, hp2⟩ := hq
  have hs := sUH _ _ hp1 hp2
  set s := Matrix.of q.2.1 * Matrix.of q.2.2 with hs_def
  set Y : Mx k r := Matrix.of q.1 with hY_def
  have hg : s * Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hs hy
  have hY1 := (hNIG Y hy).2
  have hg1 := (hNIG _ hg).2
  have hs1 := (hNIG s hs).2
  have hSle : B.gN s ≤ B.gN (s * Y) * 1 * B.gN Y := by
    have e : s = (s * Y) * Y⁻¹ := by
      rw [Matrix.mul_assoc, (uh_inv hy).2.1, Matrix.mul_one]
    calc B.gN s = B.gN ((s * Y) * Y⁻¹) := by rw [← e]
      _ ≤ B.gN (s * Y) * B.gN Y⁻¹ := hsub _ _
      _ = _ := by rw [(hNIG _ hy).1, mul_one]
  have key := key_bound hg1 le_rfl hY1 (by linarith) ha hSle
  rw [Real.one_rpow, one_mul] at key
  rw [norm_mul, norm_star]
  calc ‖⟪v, R.σ Y w⟫_ℂ‖ * ‖⟪v, R.σ (s * Y) w⟫_ℂ‖
      ≤ (C * B.gN Y ^ (-a)) * (C * B.gN (s * Y) ^ (-a)) :=
        mul_le_mul (hb Y hy) (hb _ hg) (norm_nonneg _) (mul_nonneg hC0 (Real.rpow_nonneg (gN0 _) _))
    _ = (C * C) * (B.gN Y ^ (-a) * B.gN (s * Y) ^ (-a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg hC0 hC0)

theorem integrable_GS : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, Integrable (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ) (μG.prod (μW.prod μN)) :=
  integrable_of_growth GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable GlobalTheory.T.besselGrowth_stabilizer_unipotent

end GlobalTheory.BesselFubini
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselConv

open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

section

variable {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem ae_mem_prod {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have := hW.1; have := hN.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)

theorem pi_inv_contOn [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    ContinuousOn (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} := by
  rw [continuousOn_clm_apply]
  intro ξ
  have hm : Continuous (fun p1 : Formalism.QuantumDeterminants.Mt k r =>
      Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hmaps : Set.MapsTo (fun p1 : Formalism.QuantumDeterminants.Mt k r =>
      Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} (Formalism.QuantumDeterminants.UWset k r z) := by
    intro p1 hp1
    have e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r :=
      PI.HwUniqW.inv_eq_UH hp1.1
    show Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r ∈ Formalism.QuantumDeterminants.UWset k r z
    rw [← e]; exact (uw_inv hp1).1
  refine ((piW_cont hT hπ ξ).comp hm.continuousOn hmaps).congr ?_
  intro p1 hp1
  have e : (Matrix.of p1 : Mx k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r :=
    PI.HwUniqW.inv_eq_UH hp1.1
  simp only [Function.comp]
  rw [e]

theorem beInt_aesm [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (w v : H) :
    AEStronglyMeasurable (beInt z c π σ w v) (μW.prod μN) := by
  have := hW.1; have := hN.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.1 : Mx k r)) := continuous_fst
  have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.2 : Mx k r)) := continuous_snd
  have hφ : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.1 : Mx k r) * Matrix.of q.2) := h1.matrix_mul h2
  have hTm : MeasurableSet ((fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.1 : Mx k r) * Matrix.of q.2) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (isClosed_UH.preimage hφ).measurableSet
  have hTae : ∀ᵐ q ∂(μW.prod μN), q ∈ ((fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.1 : Mx k r) * Matrix.of q.2) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    filter_upwards [ae_mem_prod hW hN] with q hq
    exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hq.1.1 hq.2.1
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w
  have hc2 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ⟪v, σ (Matrix.of q.1 * Matrix.of q.2) w⟫_ℂ) (μW.prod μN) :=
    aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (μ := μW.prod μN)
      (continuousOn_const.inner (hcs.comp hφ.continuousOn (fun q hq => hq))) hTm hTae
  have hc3 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of q.2))) (μW.prod μN) :=
    (continuous_star.comp ((psi_cont z c).comp h2)).aestronglyMeasurable
  have hV : AEStronglyMeasurable (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹) μW := by
    have := (pi_inv_contOn hT hπ).aestronglyMeasurable (μ := μW) ((isClosed_UW z).preimage hof).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem
      (s := {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z}) hWae] at this
  have hV1 : AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p.1)⁻¹)
      (μW.prod μN) := AEStronglyMeasurable.comp_fst (μ := μW) (ν := μN) hV
  exact (hc2.mul hc3).smul hV1

theorem norm_beInt_le (σ : Mx k r → (H →L[ℂ] H)) {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    (w v : H) (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z) :
    ‖beInt z c π σ w v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ := by
  have h1 : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by
      rw [piW_unitary hT hπ _ (uw_inv hp).1 ξ, one_mul]
  unfold beInt
  rw [norm_smul, norm_mul, norm_star, psi_norm, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end

theorem be_conv_of_growth (hG : GrowthS) : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  intro Hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS v hv
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, hGh, hq⟩ := hS
  obtain ⟨C, Ws, hWs, hb⟩ := GlobalTheory.BesselDecay.decay_TK Hy k r ε mu h R hR hgap hok v hv
  have hA : AG k r < aOf r h - 1 := by
    have h4 := hok.2.2.2
    have : 0 ≤ AG k r := by unfold AG; positivity
    have : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  have hI := hG k r z μW μN μG νq _ hz hT hW hN hGh hq hA
  rw [neg_sub] at hI
  have hbd : ∀ w ∈ R.sm, ∀ᵐ p ∂(μW.prod μN), ‖beInt z Formalism.QuantumDeterminants.cStd π R.σ w v p‖ ≤
      C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum *
        B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) := by
    intro w hw
    filter_upwards [ae_mem_prod hW hN] with p hp
    exact (norm_beInt_le R.σ _ hT hπ w v p hp.1).trans
      (hb w hw _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hp.1.1 hp.2.1))
  refine ⟨fun w hw => ?_, C * ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
    B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) ∂(μW.prod μN), Ws, hWs, fun w hw => ?_⟩
  · exact Integrable.mono' (hI.const_mul _) (beInt_aesm hR.2 _ hT hπ hW hN w v) (hbd w hw)
  · refine (norm_integral_le_of_norm_le (hI.const_mul _) (hbd w hw)).trans (le_of_eq ?_)
    rw [integral_const_mul]; ring

theorem be_conv : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) :=
  be_conv_of_growth GlobalTheory.T.besselGrowth_stabilizer_unipotent

end GlobalTheory.BesselConv
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.cayley_endomorphisms_modular : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  first | exact @GlobalTheory.isMod_smooth_of_isDS | exact GlobalTheory.isMod_smooth_of_isDS | (intros; apply GlobalTheory.isMod_smooth_of_isDS <;> assumption)
end Gp91
end
