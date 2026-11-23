module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle016
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.RingTheory.PiTensorProduct
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

namespace GlobalTheory

theorem besselIntegral_sesquilinear : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  intro hG k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDG hGap hOK hSide
  have hI := Gp91.GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hG k r ε mu h R Wp z π u μW μN μG νq hDG hGap hOK hSide
  refine ⟨fun v hv w hw w' hw' a => ⟨?_, ?_⟩, fun w hw v hv v' hv' a => ⟨?_, ?_⟩⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_add ((hI v hv).1 w hw) ((hI v hv).1 w' hw')]
    congr 1
    funext p
    simp only [beInt, map_add, inner_add_right, add_mul, add_smul]
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_smul]
    congr 1
    funext p
    simp only [beInt, map_smul, inner_smul_right, smul_smul]
    congr 1
    ring
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_add ((hI v hv).1 w hw) ((hI v' hv').1 w hw)]
    congr 1
    funext p
    simp only [beInt, inner_add_left, add_mul, add_smul]
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_smul]
    congr 1
    funext p
    simp only [beInt, inner_smul_left, smul_smul]
    congr 1
    simp only [← Complex.star_def]
    ac_rfl

end GlobalTheory
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  first | exact @GlobalTheory.BesselOrbital.bessel_integral_eq_smul | exact GlobalTheory.BesselOrbital.bessel_integral_eq_smul | (intros; apply GlobalTheory.BesselOrbital.bessel_integral_eq_smul <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  first | exact @GlobalTheory.DualStepBound.dual_step_bound | exact GlobalTheory.DualStepBound.dual_step_bound | (intros; apply GlobalTheory.DualStepBound.dual_step_bound <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.tensor_moment_transfer : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  first | exact @GlobalTheory.BesselPairing.pairing | exact GlobalTheory.BesselPairing.pairing | (intros; apply GlobalTheory.BesselPairing.pairing <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselEquiv

theorem integral_smul_comp_of_measurePreserving {X Wp : Type} [MeasurableSpace X] [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [CompleteSpace Wp] {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    {F F' : X → (Wp →L[ℂ] Wp)} (hF : Integrable F μ) (c : ℂ) (A : Wp →L[ℂ] Wp)
    (h : ∀ᵐ p ∂μ, F' p = c • A.comp (F (T p))) :
    ∫ p, F' p ∂μ = c • A.comp (∫ p, F p ∂μ) := by
  have hFT : Integrable (fun p => F (T p)) μ := hT.integrable_comp_of_integrable hF
  have e1 : ∫ p, F (T p) ∂μ = ∫ p, F p ∂μ := by
    have := integral_map (μ := μ) (φ := T) (f := F) hT.measurable.aemeasurable
      (by rw [hT.map_eq]; exact hF.aestronglyMeasurable)
    rw [hT.map_eq] at this
    exact this.symm
  rw [integral_congr_ae h, integral_smul, ← e1]
  congr 1
  exact (ContinuousLinearMap.compL ℂ Wp Wp Wp A).integral_comp_comm hFT

theorem be_equivariant : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (g * m) w) v = Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv w hw g hg m hm
  have hint := (GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv).1 w hw
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨hψ1, hψm, -, hψc, hUW, hNG⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hmp, -, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hok.1 hz hT hW hN
  have hσ := (GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS).1
  have hπm := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ).2.1
  have hGm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [ha', hb']
  unfold be
  refine integral_smul_comp_of_measurePreserving (hmp g hg m hm).1 hint _ _ ?_
  filter_upwards [hae] with p hp
  obtain ⟨ha, hn⟩ := hp
  have key : ∀ a ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r,
      (⟪v, R.σ (a * n) (R.σ (g * m) w)⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd n)) • π a⁻¹ =
      Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp
        ((⟪v, R.σ (a * g * (g⁻¹ * n * g * m)) w⟫_ℂ *
          star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (g⁻¹ * n * g * m))) • π (a * g)⁻¹) := by
    intro a ha n hn
    obtain ⟨hag, -, haG⟩ := hUW a ha g hg
    have hgG := (hUW g hg g hg).2.2
    obtain ⟨-, hgg, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hg
    obtain ⟨hagi, -, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hag
    obtain ⟨-, hc, -, hcψ⟩ := hψc g hg n hn
    have e1 : a * g * (g⁻¹ * n * g * m) = a * n * (g * m) := by
      calc a * g * (g⁻¹ * n * g * m) = a * (g * g⁻¹) * n * (g * m) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg, Matrix.mul_one]
    have e2 : g * (a * g)⁻¹ = a⁻¹ := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
    have e3 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ1 m]; simp
    rw [e1, hσ _ (hGm a haG n (hNG n hn)) _ (hGm g hgG m (hNG m hm)), (hψm _ hc m hm).2, hcψ,
      ContinuousLinearMap.comp_smul, ← hπm g hg _ hagi, e2, smul_smul, star_mul']
    congr 1
    linear_combination (-(⟪v, R.σ (a * n) (R.σ (g * m) w)⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd n))) * e3
  exact key _ ha _ hn

end GlobalTheory.BesselEquiv
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselNormSq

theorem integral_comp_mp {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) {F : X → ℂ} (hF : Integrable F μ) :
    ∫ x, F x ∂μ = ∫ x, F (f x) ∂μ := by
  have h1 : AEStronglyMeasurable F (μ.map f) := by rw [hf.map_eq]; exact hF.1
  rw [← integral_map hf.measurable.aemeasurable h1, hf.map_eq]

theorem inner_integral_apply {X Wp : Type} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {F : X → (Wp →L[ℂ] Wp)} (hF : Integrable F μ) (ξ η : Wp) :
    ⟪η, (∫ x, F x ∂μ) ξ⟫_ℂ = ∫ x, ⟪η, F x ξ⟫_ℂ ∂μ ∧
    ⟪(∫ x, F x ∂μ) ξ, η⟫_ℂ = ∫ x, ⟪F x ξ, η⟫_ℂ ∂μ ∧ Integrable (fun x => ⟪F x ξ, η⟫_ℂ) μ := by
  have h1 : Integrable (fun x => F x ξ) μ := hF.apply_continuousLinearMap ξ
  have h2 : ⟪η, (∫ x, F x ∂μ) ξ⟫_ℂ = ∫ x, ⟪η, F x ξ⟫_ℂ ∂μ := by
    rw [ContinuousLinearMap.integral_apply hF, integral_inner h1]
  refine ⟨h2, ?_, h1.inner_const η⟩
  rw [← inner_conj_symm, h2, ← integral_conj]
  simp only [inner_conj_symm]

end GlobalTheory.BesselNormSq


open GlobalTheory.BesselNormSq in

theorem GlobalTheory.bessel_norm_sq_double_integral : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ ξ : Wp, ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ‖ ^ 2 : ℝ) : ℂ) = ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, (∫ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, ⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star ⟪v, R.σ (Matrix.of q.1 * Matrix.of q.2 * (Matrix.of p.1 * Matrix.of p.2)) w⟫_ℂ * (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of q.2) * ⟪π (Matrix.of q.1)⁻¹ ξ, ξ⟫_ℂ) ∂(μW.prod μN)) ∂(μW.prod μN) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv w hw ξ
  have hint := (GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv).1 w hw
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨hψ1, hψm, -, hψc, hUW, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hmp, -, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hok.1 hz hT hW hN
  obtain ⟨-, hmul, hunit, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ
  have e0 : ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ‖ ^ 2 : ℝ) : ℂ) =
      ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e0]
  refine ((GlobalTheory.BesselNormSq.inner_integral_apply hint ξ _).1).trans (integral_congr_ae ?_)
  filter_upwards [hae] with p hp
  obtain ⟨-, h2, h3⟩ := GlobalTheory.BesselNormSq.inner_integral_apply hint ξ (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v p ξ)
  refine h2.trans ((GlobalTheory.BesselNormSq.integral_comp_mp (hmp _ hp.1 _ hp.2).1 h3).trans (integral_congr_ae ?_))
  filter_upwards [hae] with q hq
  obtain ⟨⟨p1, p2⟩, hp1, hp2⟩ : ∃ p' : Mx k r × Mx k r, p'.1 = Matrix.of p.1 ∧ p'.2 = Matrix.of p.2 :=
    ⟨(_, _), rfl, rfl⟩
  obtain ⟨⟨q1, q2⟩, hq1, hq2⟩ : ∃ p' : Mx k r × Mx k r, p'.1 = Matrix.of q.1 ∧ p'.2 = Matrix.of q.2 :=
    ⟨(_, _), rfl, rfl⟩
  simp only at hp1 hp2 hq1 hq2
  have key : ∀ A : Mx k r, Matrix.of (fun i j => A i j) = A := fun A => rfl
  unfold beInt
  simp only [key]
  rw [← hp1, ← hp2] at hp
  rw [← hq1, ← hq2] at hq
  rw [← hp1, ← hp2, ← hq1, ← hq2]
  obtain ⟨hpi, hpp, hpp'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.1
  obtain ⟨hqi, -, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hq.1
  have e1 : q1 * p1 * (p1⁻¹ * q2 * p1 * p2) = q1 * q2 * (p1 * p2) := by
    calc q1 * p1 * (p1⁻¹ * q2 * p1 * p2) = q1 * (p1 * p1⁻¹) * q2 * (p1 * p2) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpp, Matrix.mul_one]
  have e2 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (p1⁻¹ * q2 * p1 * p2) =
      Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd q2 * Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2 := by
    obtain ⟨-, a2, -, a4⟩ := hψc p1 hp.1 q2 hq.2
    rw [(hψm _ a2 _ hp.2).2, a4]
  have e3 : π (q1 * p1)⁻¹ = (π p1⁻¹).comp (π q1⁻¹) := by
    rw [Matrix.mul_inv_rev, hmul _ hpi _ hqi]
  have hiso : ∀ a b, ⟪π p1⁻¹ a, π p1⁻¹ b⟫_ℂ = ⟪a, b⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map ((π p1⁻¹ : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (hunit _ hpi)
  have e4 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2 * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ1]; simp
  rw [e1, e2, e3]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_left, inner_smul_right,
    hiso, map_mul, starRingEnd_apply, star_mul', star_star]
  linear_combination (⟪v, R.σ (p1 * p2) w⟫_ℂ * star ⟪v, R.σ (q1 * q2 * (p1 * p2)) w⟫_ℂ *
    (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd q2 * ⟪π q1⁻¹ ξ, ξ⟫_ℂ)) * e4
end Gp91
end
