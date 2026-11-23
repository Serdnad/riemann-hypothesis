module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle219
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPTypicalTangent
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle016
public import ReciprocityTheory.SemistableReduction.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import ReciprocityTheory.SemistableReduction.Bundle005
public import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
public import ReciprocityTheory.SemistableReduction.Bundle027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle058

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory.DepthStages.RebaseBasis

theorem rebase_isBasis : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (X : Matrix (Fin d) (Fin d) C),
      IsBasis G p ty γ → (∀ a b, IsIntV v (X a b)) → v X.det = 0 →
      (∀ a b, X a b ≠ 0 → ty b = ty a) →
      IsBasis G p ty (rebase G X γ) ∧
        (∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b)) ∧
        ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n := by
  intro C _ _ _ v p hp hv d h ty G γ X hB hX hdet hty
  obtain ⟨hγc, hγty, hγdet⟩ := hB
  have key : ∀ a, _ := fun a => pt6' C v p hp hv d d G γ (X a) hγc (hX a)
  have hlc : ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n :=
    fun a n => (key a).2.2.1 n
  have htan : ∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b) := fun a => (key a).2.1
  refine ⟨⟨fun a => (key a).1, fun a => ⟨(key a).2.2.2 fun b => (hγty b).1, ?_⟩, ?_⟩, htan, hlc⟩
  · intro n c hc
    rw [hlc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hXab : X a b = 0
    · rw [hXab, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul]
    · have hb := hty a b hXab
      rw [(hγty b).2 n c (by rw [hb]; exact hc), mul_zero]
  · have hM : (Matrix.of fun a b => tangent (rebase G X γ a) b) =
        X * Matrix.of fun a b => tangent (γ a) b := by
      ext a b
      rw [Matrix.of_apply, htan, Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hM, Matrix.det_mul, v.map_mul, hdet, hγdet, add_zero]

end GlobalTheory.DepthStages.RebaseBasis
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.TypicalCurveBases

theorem typical_curves_tangent_and_bases : TypicalCurveEigenspace ∧ TypicalCurveBasisExists :=
  have h2 : TypicalCurveEigenspace :=
    GlobalTheory.TypicalCurve.typicalCurves_of_type_of_typical_tangents GlobalTheory.PTypicalTangent.exists_pTypical_tangent
  ⟨h2, GlobalTheory.typicalBasis_coordinates h2⟩

end GlobalTheory.TypicalCurveBases
end

section

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.SphereMeanNull

theorem exists_blockSphere_eval_ne_zero {B n : ℕ} (hn : 0 < n) {a : Fin B → ℕ}
    {g : MvPolynomial (Fin B × Fin n) ℂ} (hg0 : g ≠ 0) (hg : IsMultiHomogeneous a g) :
    ∃ u : BlockSphere B n, eval (blockPoint u) g ≠ 0 := by
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hg0
  obtain ⟨z, hz1, hz⟩ := exists_torus_coeff_le g s
  set r : ℝ := (Real.sqrt n)⁻¹ with hrdef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hnR)
  have hr2 : r ^ 2 * n = 1 := by
    rw [hrdef, inv_pow, Real.sq_sqrt hnR.le, inv_mul_cancel₀ hnR.ne']
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => (r : ℂ) * z (b, j)), by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, hz1, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm, hr2,
      Real.sqrt_one]⟩
  have hbp : blockPoint u = fun p => (r : ℂ) * z p := rfl
  have heval : eval (blockPoint u) g = (r : ℂ) ^ (∑ b, a b) * eval z g := by
    rw [hbp]; exact eval_mul_of_isMultiHomogeneous hg _ z
  have hne : eval z g ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hs) hz)
  exact ⟨u, by rw [heval]; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hr.ne')) hne⟩

theorem blockSphereProb_zeroSet_eq_zero : ∀ (B n : ℕ) (a : Fin B → ℕ)
    (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g →
    blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  intro B n a g hn hg0 hg
  obtain ⟨u, hu⟩ := exists_blockSphere_eval_ne_zero hn hg0 hg
  exact null_of_logBound hn ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
    (blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable hn B)
    a g u hg hu

end GlobalTheory.SphereMeanNull
end
end
