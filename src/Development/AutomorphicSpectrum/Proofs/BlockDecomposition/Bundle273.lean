module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle260
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle263
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle264
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle265
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.lubin_tate_endomorphism_series_exists : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ a : ↥(OL K),
    ∃ φ : PowerSeries ↥(OL K), PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exists_series_comm | exact GlobalTheory.CompanionTheory.LTPer.exists_series_comm | (intros; apply GlobalTheory.CompanionTheory.LTPer.exists_series_comm <;> assumption)
end
end

section


theorem _root_.GlobalTheory.T.kernel_adjoint_smooth : GlobalTheory.CompanionTheory.KerFc.AdjSmooth := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.adjSmooth | exact GlobalTheory.CompanionTheory.KerFc.adjSmooth | (intros; apply GlobalTheory.CompanionTheory.KerFc.adjSmooth <;> assumption)
end

section


theorem _root_.GlobalTheory.T.kernel_row_left_invariant : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm → GlobalTheory.CompanionTheory.KerFc.RowLeft := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowLeft | exact GlobalTheory.CompanionTheory.KerFc.rowLeft | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowLeft <;> assumption)
end

section


theorem _root_.GlobalTheory.T.wave_uniqueness : GlobalTheory.CompanionTheory.KerFc.WaveUniq := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveUniq | exact GlobalTheory.CompanionTheory.KerFc.waveUniq | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveUniq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.kernel_action_formula : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm → GlobalTheory.CompanionTheory.KerFc.ActFormula := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.actFormula | exact GlobalTheory.CompanionTheory.KerFc.actFormula | (intros; apply GlobalTheory.CompanionTheory.KerFc.actFormula <;> assumption)
end

section


theorem _root_.GlobalTheory.T.kernel_row_matrix : GlobalTheory.CompanionTheory.KerFc.RowMatrix := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds | exact GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds <;> assumption)
end

section


theorem _root_.GlobalTheory.T.left_translate_commutes : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob | exact GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob | (intros; apply GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob <;> assumption)
end

section


theorem _root_.GlobalTheory.T.phi_resolvent_identity : GlobalTheory.CompanionTheory.KerFc.PhiRes := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.phiRes_holds | exact GlobalTheory.CompanionTheory.KerFc.phiRes_holds | (intros; apply GlobalTheory.CompanionTheory.KerFc.phiRes_holds <;> assumption)
end

section


theorem _root_.GlobalTheory.T.wave_representation : GlobalTheory.CompanionTheory.KerFc.WaveRep := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveRep | exact GlobalTheory.CompanionTheory.KerFc.waveRep | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveRep <;> assumption)
end

section


theorem _root_.GlobalTheory.T.wave_integral_identity : GlobalTheory.CompanionTheory.KerFc.WaveInt := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveInt | exact GlobalTheory.CompanionTheory.KerFc.waveInt | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveInt <;> assumption)
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem norm_lConv_sub_le : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → (∀ y, 0 ≤ φ y) → (∫ y : G n, φ y.val ∂μ = 1) → ∀ (x : Lp V 2 μ) (ε : ℝ), (∀ y : G n, φ y.val ≠ 0 → ‖lT μ V y x - x‖ ≤ ε) → ‖lConv μ V φ x - x‖ ≤ ε := by
  intro n _ _ μ _ V _ _ _ hU φ hφ hpos h1 x ε hε
  have hemb := GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n
  have hφc : Continuous fun y : G n => φ y.val := hφ.1.continuous.comp hemb.continuous
  have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine (hemb.isInducing.isCompact_preimage_iff ?_).2 hφ.2.1
    intro z hz
    have hdet : z.det ≠ 0 := hφ.2.2 hz
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det z).2 (isUnit_iff_ne_zero.2 hdet)
    exact ⟨u, rfl⟩
  have hcs : HasCompactSupport (fun y : G n => φ y.val) :=
    HasCompactSupport.of_support_subset_isCompact hK (fun y hy => subset_tsupport φ hy)
  have hL := (translations_strongly_continuous n μ V hU x).2
  have hint1 : Integrable (fun y : G n => φ y.val) μ := hφc.integrable_of_hasCompactSupport hcs
  have hf : Integrable (fun y : G n => φ y.val • lT μ V y x) μ :=
    (hφc.smul hL).integrable_of_hasCompactSupport hcs.smul_right
  have hg : Integrable (fun y : G n => φ y.val • x) μ := hint1.smul_const x
  have e : lConv μ V φ x - x = ∫ y : G n, φ y.val • (lT μ V y x - x) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hf hg, integral_smul_const, h1, one_smul]
    rfl
  rw [e]
  calc ‖∫ y : G n, φ y.val • (lT μ V y x - x) ∂μ‖ ≤ ∫ y : G n, φ y.val * ε ∂μ := by
        refine norm_integral_le_of_norm_le (hint1.mul_const ε) (ae_of_all _ fun y => ?_)
        by_cases h0 : φ y.val = 0
        · simp [h0]
        · rw [norm_smul, Real.norm_of_nonneg (hpos _)]
          exact mul_le_mul_of_nonneg_left (hε y h0) (hpos _)
    _ = ε := by rw [integral_mul_const, h1, one_mul]

end GlobalTheory.CompanionTheory.PresSobA
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.mollification_right_translate : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (φ : Mat n → ℝ) (h : G n) (x : Lp V 2 μ) (z : Mat n), Mol μ φ (⇑(rR μ V h x)) z = Mol μ φ (⇑x) (z * h.val) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq | exact GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq | (intros; apply GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq <;> assumption)
end
end
