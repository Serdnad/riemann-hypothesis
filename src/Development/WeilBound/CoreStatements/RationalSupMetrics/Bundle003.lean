module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.WeilBound.CoreStatements.RationalSupMetrics.Bundle001
public import Development.WeilBound.CoreStatements.RationalSupMetrics.Bundle002
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem MultiProjectiveCoordinates.valuation_unique_on_forms : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w := by
  intro K _ ι _ Ω _ y 𝕜 _ a s z w hz hw
  obtain ⟨dg0, dh0, g0, h0, hg0, hh0, hd0, e0, hne, e1⟩ := hw
  have key : ∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh →
      (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h := by
    intro dg dh g h hg hh hd e
    have hdeg : dg0 + dh = dg + dh0 := by
      funext k
      have h1 := hd k
      have h2 := hd0 k
      simp only [Pi.add_apply]
      omega
    have f1 := MultiProjectiveCoordinates.Val.mh_mul hg hh0
    have f2 := MultiProjectiveCoordinates.Val.mh_mul hg0 hh
    rw [hdeg] at f2
    have h3 := MultiProjectiveCoordinates.Val.form_vanish y hz (MultiProjectiveCoordinates.Val.mh_sub f1 f2) (by
      rw [map_sub, map_mul, map_mul, e, e0]
      ring)
    rw [map_sub, map_mul, map_mul, e1] at h3
    apply mul_right_cancel₀ hne
    linear_combination h3
  refine ⟨key, ?_⟩
  rintro w' ⟨dg, dh, g, h, hg, hh, hd, e, hn, e'⟩
  have := key dg dh g h hg hh hd e
  exact mul_right_cancel₀ hn (e'.symm.trans this)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem MultiProjectiveCoordinates.levi_shift {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) (t : ℝ)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun z => Real.log ((shiftH A t).h z)) z w = leviForm (fun z => Real.log (A.h z)) z w := by
  have h1 : (fun z => Real.log ((shiftH A t).h z)) =ᶠ[𝓝 z] fun z => t + Real.log (A.h z) := by
    filter_upwards [MultiProjectiveCoordinates.isOpen_blocks.mem_nhds hz] with z' hz'
    show Real.log (Real.exp t * A.h z') = _
    rw [Real.log_mul (Real.exp_pos t).ne' (A.pos z' hz').ne', Real.log_exp]
  have h2 : fderiv ℝ (fun z => t + Real.log (A.h z)) = fderiv ℝ (fun z => Real.log (A.h z)) :=
    funext fun z => fderiv_const_add t
  unfold leviForm
  rw [h1.fderiv.fderiv_eq, h2]

theorem MultiProjectiveCoordinates.shiftH_smooth_nef_gen : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) := by
  intro K _ ι _ P A t Λ
  have hs : IsSmoothHerm A → IsSmoothHerm (shiftH A t) := fun h => contDiffOn_const.mul h
  have hp : (∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P A) →
      ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P (shiftH A t) := by
    rintro ⟨P0, h0, h1, h2⟩
    refine ⟨P0, h0, hs h1, fun z hz w hw => ?_⟩
    rw [MultiProjectiveCoordinates.levi_shift A t hz.1]
    exact h2 z hz w hw
  have hc : IsConjInvariantH A → IsConjInvariantH (shiftH A t) := fun h z => by
    show Real.exp t * _ = Real.exp t * _
    rw [h z]
  refine ⟨hs, fun h => ⟨hp h.semipos, hc h.conj, h.nef⟩, fun h =>
    ⟨mul_pos h.pos (Real.exp_pos _), hp h.semipos, hc h.conj, ?_⟩⟩
  obtain ⟨a, ha, hm⟩ := h.mono
  refine ⟨a, ha, fun z hz μ hμ => (hm z hz μ hμ).trans_eq ?_⟩
  show Λ * A.h z = Λ * Real.exp (-t) * (Real.exp t * A.h z)
  rw [mul_assoc, ← mul_assoc (Real.exp (-t)), ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
end
