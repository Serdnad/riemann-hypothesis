module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle020
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle179
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

open Complex Matrix

namespace GlobalTheory.CompanionTheory.Metric

theorem mean_sq_fixes_norm_const :
    ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (Λ : Submodule ℤ (Fin g → ℂ))
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ) (b : ℝ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, c i = 0 ∨ c i = 1 / 2) →
    (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ, h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z)) →
    (∀ l ∈ Λ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z, θ (z + l) = ε *
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z) →
    0 < b →
    (∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
      b ^ 2 = (∫ w in Fd, (‖θ w‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm w w).re)) ^ 2) / (volume Fd).toReal) →
    b ^ 2 = ‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ h Hm a c Λ θ κ b hs hp hh ha hc hΛ hH hθ hper hb hmean
  have h₁ : ∀ i, (fun i => (a i : ℂ)) i = 0 ∨ (fun i => (a i : ℂ)) i = 1 / 2 := fun i => by
    rcases ha i with e | e <;> simp [e]
  have h₂ : ∀ i, (fun i => (c i : ℂ)) i = 0 ∨ (fun i => (c i : ℂ)) i = 1 / 2 := fun i => by
    rcases hc i with e | e <;> simp [e]
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  obtain ⟨Fd, hFd, -⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g τ h
    (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) Λ.toAddSubgroup hs hp hh h₁ h₂ hΛ
  have hFdΛ : IsAddFundamentalDomain Λ Fd volume := hFd
  have hb2 := hmean Fd hFdΛ
  have hsq := GlobalTheory.Dict.VacNorm.norm_sq_of_mean (τ := τ) (h := h) (A := Λ.toAddSubgroup)
    (H := hermForm Hm) (θ := fun z => θ z / b) (a := κ / b) ⟨hs, hp⟩ hh h₁ h₂ hΛ
    (fun z w => by
      rw [hH]
      rfl)
    (fun z => by
      simp only [hθ, GlobalTheory.CanTh.canTh, GlobalTheory.CanTh.imInv]
      ring)
    (fun p hp' => by
      obtain ⟨ε, hε, hz⟩ := hper p hp'
      have hε0 : ε ≠ 0 := by
        intro e
        simp [e] at hε
      refine ⟨ε⁻¹, by simp [hε], fun z => ?_⟩
      have e2 : hermForm Hm (z + (1 / 2 : ℂ) • p) p = hermForm Hm z p + 1 / 2 * hermForm Hm p p := by
        simp only [hermForm, add_dotProduct, smul_dotProduct, smul_eq_mul]
      simp only [hz, e2]
      have e3 : Complex.exp (-(((1 : ℕ) : ℂ) * Real.pi * (hermForm Hm z p + 1 / 2 * hermForm Hm p p))) *
          Complex.exp (Real.pi * hermForm Hm z p + Real.pi / 2 * hermForm Hm p p) = 1 := by
        rw [← Complex.exp_add]
        simp only [Nat.cast_one]
        ring_nf
        simp
      have e1 : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε0
      linear_combination (θ z / b * Complex.exp (-(((1 : ℕ) : ℂ) * Real.pi * (hermForm Hm z p + 1 / 2 * hermForm Hm p p))) *
        Complex.exp (Real.pi * hermForm Hm z p + Real.pi / 2 * hermForm Hm p p)) * e1 + (θ z / b) * e3)
    hFd
    (by
      have hint : ∀ z, ‖θ z / (b : ℂ)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) = (b ^ 2)⁻¹ *
          (‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re)) ^ 2 := by
        intro z
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, mul_pow, div_pow,
          ← Real.exp_nat_mul]
        have : ((2 : ℕ) : ℝ) * (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) =
            -Real.pi * (hermForm Hm z z).re := by
          push_cast
          ring
        rw [this]
        ring
      simp only [hint]
      rw [MeasureTheory.integral_const_mul, mul_div_assoc, ← hb2]
      exact inv_mul_cancel₀ (pow_ne_zero _ hb.ne'))
  have hD : 0 < Real.sqrt (2 ^ g * (τ.map Complex.im).det) :=
    Real.sqrt_pos.2 (mul_pos (by positivity) hp.det_pos)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, div_pow,
    div_eq_iff (pow_ne_zero _ hb.ne')] at hsq
  rw [hsq]
  field_simp

end GlobalTheory.CompanionTheory.Metric
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem archInt_toZ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (hN : ∀ τ, (wZ N t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf) (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), ((toZ N t hN).ArchIntegrable (toZ M t hM) e hr ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → (toZ N t hN).archInt (toZ M t hM) e hr = N.archInt M e hr) := by
  intro k _ X _ p t D hX N M hN hM e r hr
  have W := fun τ : ℤ →+* ℂ => GlobalTheory.T.archIntegrable_iff_over_integers k X p t τ D hX N M (wZ N t τ) (wZ M t τ)
    (wOver_wZ N t τ) (wOver_wZ M t τ) (hN τ) e r hr
  let τ₀ : ℤ →+* ℂ := Int.castRingHom ℂ
  have hu : ∀ τ : ℤ →+* ℂ, τ = τ₀ := fun τ => Subsingleton.elim _ _
  refine ⟨⟨fun h => (W τ₀).1.1 (h τ₀), fun h τ => (W τ).1.2 h⟩, fun h => ?_⟩
  haveI : Unique (ℤ →+* ℂ) := ⟨⟨τ₀⟩, hu⟩
  unfold HermLB.archInt
  rw [finsum_unique]
  exact (W default).2 h

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_analytic_dimension_count : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_model_analytic_data_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (FlagAn BM d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists | exact GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists <;> assumption)
end
