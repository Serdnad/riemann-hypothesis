module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Bundle001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle030
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle029
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseJacobsonPowers.SfrMulMemJHfr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Bundle002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem mem_pow_smul_top_iff {N : ℕ} (la : HeightOneSpectrum (𝓞 B.KO)) (w : Fin N → B.Cusp j wL)
    {u : WeightFamilies.Wt D j} {a : ℕ} {x : ↥(HK X la w u)} :
    x ∈ Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) ↔ (x : Lw X la w) ∈ JHfr X la w u a := by
  rw [mem_Jid_pow_smul_top X la w, mem_JHfr X la w]

theorem hasse_preserves_kernel (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : HKPres G la := fun β x hx =>
  (mem_HK X la G.w).2 (hasse_presentation X la G.w wF β x ((mem_HK X la G.w).1 hx))

theorem leading_coeff_eq_zero_of_jet {N : ℕ} (la : HeightOneSpectrum (𝓞 B.KO)) (w : Fin N → B.Cusp j wL)
    {u : WeightFamilies.Wt D j} (x : ↥(HK X la w u)) (hx : (x : Lw X la w) ∈ JHfr X la w u 1) : toA0K X la w u x = 0 := by
  rw [reduction_eq_zero_iff_mem_ideal_smul, ← pow_one (Jid X la w), mem_pow_smul_top_iff la w]
  exact hx

theorem vanishingOnQuadric (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Vanish G la := by
  intro k β x hx hβ
  unfold rD
  split_ifs with h
  · refine leading_coeff_eq_zero_of_jet la G.w _ ?_
    have h1 := hasse_jid_power X la G.w wF β k _ ((mem_pow_smul_top_iff la G.w).1 hx)
    exact PI.HJP.JHfr_anti X la G.w wF (by omega) h1
  · rfl

end PI.PoleLengthCount
end
end

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem coe_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (col : Fin G.N) :
    (PoleLengthBounds.wfr G la col : Lw X la G.w) =
      algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wL (G.w col))) * w0inv X la G.w := by
  simp only [PoleLengthBounds.wfr, coe_weightZeroFraction, frac_apply, pow_one]

theorem uSpec_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    uSpec G la (fun col => toOsK X la G.w (PoleLengthBounds.wfr G la col)) :=
  fun col => ⟨PoleLengthBounds.wfr G la col, coe_wfr G la col, rfl⟩

theorem sum_T_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    ∑ col, algebraMap (Kp X la G.N) ↥(Frac0 X la G.w)
      (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col))) *
        PoleLengthBounds.wfr G la col = 1 := by
  apply Subtype.ext
  have h : ∀ col, ((algebraMap (Kp X la G.N) ↥(Frac0 X la G.w)
      (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col))) *
        PoleLengthBounds.wfr G la col : ↥(Frac0 X la G.w)) : Lw X la G.w) =
      frac X la G.w 1 ((@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col))) •
        emb X la G.N (X.inc wL (G.w col))) := by
    intro col
    rw [LinearMap.map_smul, Algebra.smul_def]
    rfl

  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_congr rfl fun col _ => h col, ← map_sum]
  show frac X la G.w 1 (sec X la G.w 0) = _
  rw [frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl

theorem sum_T_u (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    ∑ col, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col)) *
      toOsK X la G.w (PoleLengthBounds.wfr G la col) = 1 := by
  have := congrArg (toOsK X la G.w) (sum_T_wfr G la)

  rw [map_one, map_sum] at this
  rw [← this]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [map_mul, AlgHom.commutes]
  rfl

theorem unitCols_of (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (hOrd : ∀ (ζ : PtsG G la) (col : Fin G.N), 0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w (PoleLengthBounds.wfr G la col))) :
    UnitCols G la :=
  ⟨fun col => toOsK X la G.w (PoleLengthBounds.wfr G la col), uSpec_wfr G la, sum_T_u G la, hOrd⟩

theorem unitCols_of_column (hCol : PoleLengthBounds.Column) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la)
    (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) (hOk : Q.Ok S CRm T c) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) :
    UnitCols G la :=
  unitCols_of G la fun ζ col => (hCol G la Q S CRm T c hOk hw ζ).1 col

end PI.PoleLengthCount
end
end

section

noncomputable section

namespace PI.PoleLengthCount

theorem pole_ballQuot : BallQuot := ball_quotient_length

end PI.PoleLengthCount
end
end
