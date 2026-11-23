module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Bundle001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle030
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseJacobsonPowers.SfrMulMemJHfr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Bundle003
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem u_eq_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) {u : Fin G.N → OsK X la G.w}
    (hu : uSpec G la u) (col : Fin G.N) : u col = toOsK X la G.w (PoleLengthBounds.wfr G la col) := by
  obtain ⟨f, hf, hfu⟩ := hu col
  have : f = PoleLengthBounds.wfr G la col := by
    apply Subtype.ext
    rw [hf]
    simp only [PoleLengthBounds.wfr, coe_weightZeroFraction, frac_apply, pow_one]
  rw [← hfu, this]

theorem uC_eq_pow (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (col : Fin G.N) {k : ℕ}
    (α : Mon (WeightFamilies.dimY D j) k) :
    PoleLengthBounds.uC G la col α.1 = toOsK X la G.w (PoleLengthBounds.wfr G la col) ^ k := by
  have h := α.2
  rw [Finset.Nat.mem_antidiagonalTuple] at h
  rw [PoleLengthBounds.uC, Finset.prod_pow_eq_pow_sum, h]

theorem colDeriv_of (hTH : PoleLengthBounds.TaylorHasse) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    ColDeriv G la := by
  classical
  intro u hu k α α' col cf
  have hx : ((yPow X la G.w α.1 • cf : ↥(HK X la G.w wF)) : Lw X la G.w) ∈ HK X la G.w wF :=
    (yPow X la G.w α.1 • cf).2
  have h := hasse_preserves_kernel G la (colIdx D j col α'.1) _ hx
  let cf' : (Fin (WeightFamilies.dimY D j) → ℕ) → ↥(HK X la G.w wF) := fun β => if β = α.1 then cf else 0
  have hrem : (yPow X la G.w α.1 • cf : ↥(HK X la G.w wF)) -
      ∑ β ∈ PoleLengthBounds.mon D j k, PoleLengthBounds.ym G la β • cf' β ∈
        (Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) := by
    have : ∑ β ∈ PoleLengthBounds.mon D j k, PoleLengthBounds.ym G la β • cf' β = yPow X la G.w α.1 • cf := by
      rw [Finset.sum_eq_single α.1]
      · simp only [cf', if_pos rfl]; rfl
      · intro b _ hb; simp only [cf', if_neg hb, smul_zero]
      · intro hn; exact absurd α.2 hn
    rw [this, sub_self]
    exact Submodule.zero_mem _
  have key := hTH G la k _ cf' hrem col α'.1 α'.2 h
  rw [rD, dite_eq_left h]
  refine Eq.trans key ?_
  rw [uC_eq_pow G la col α', u_eq_wfr G la hu col]
  by_cases hαα : α = α'
  · subst hαα
    simp only [cf', ↓reduceIte]
  · have hne : α'.1 ≠ α.1 := fun e => hαα (Subtype.ext e.symm)
    simp only [cf', if_neg hne, if_neg hαα, map_zero, smul_zero]

end PI.PoleLengthCount
end
end

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem algebraMap_Op_mul {N : ℕ} (la : HeightOneSpectrum (𝓞 B.KO)) (w : Fin N → B.Cusp j wL) (a : Op X la N)
    (y : Lw X la w) :
    algebraMap (Rp X la N) (Lw X la w) (algebraMap (Op X la N) (Rp X la N) a) * y =
      @algebraMap (Op X la N) (Kp X la N) _ _ _ a • y := by
  rw [algebraMap_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply (Op X la N) (Rp X la N) (Lw X la w)]

theorem restricted_derivative_linear (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : LinOp G la := by
  intro k β r x hx hβ
  have hP := hasse_preserves_kernel G la
  set c := @algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ r with hc
  have h1 : hasse X la G.w β ((c • x : ↥(HK X la G.w wF)) : Lw X la G.w) ∈ HK X la G.w wF := hP β _ (c • x).2
  have h2 : hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF := hP β _ x.2
  change rD G la β (c • x) = r • rD G la β x
  unfold rD
  rw [dite_eq_left h1, dite_eq_left h2]
  show _ = c • toA0K X la G.w wF ⟨_, h2⟩
  rw [← LinearMap.map_smul_of_tower, ← sub_eq_zero, ← map_sub]
  refine leading_coeff_eq_zero_of_jet la G.w _ ?_
  have hA : ∀ (q : Idx D j G.N →₀ ℕ) (a : Op X la G.N), PI.HJP.H X la G.w q
      (algebraMap (Rp X la G.N) (Lw X la G.w) (algebraMap (Op X la G.N) (Rp X la G.N) a)) =
      algebraMap (Rp X la G.N) (Lw X la G.w) (algebraMap (Op X la G.N) (Rp X la G.N) (hasseOp X la G.N q a)) :=
    fun q a => hasse_algebraMap_Op X la G.w q a
  have e0 : ((c • x : ↥(HK X la G.w wF)) : Lw X la G.w) =
      algebraMap (Rp X la G.N) (Lw X la G.w) (algebraMap (Op X la G.N) (Rp X la G.N) r) * (x : Lw X la G.w) :=
    (algebraMap_Op_mul la G.w r x).symm
  show PI.HJP.H X la G.w β ((c • x : ↥(HK X la G.w wF)) : Lw X la G.w) -
    c • PI.HJP.H X la G.w β (x : Lw X la G.w) ∈ JHfr X la G.w wF 1
  rw [e0, PI.HJP.H_mul]
  simp only [hA, algebraMap_Op_mul la G.w]
  have hmem : ((0 : Idx D j G.N →₀ ℕ), β) ∈ antidiagonal β := by simp
  rw [← Finset.add_sum_erase _ _ hmem, hasseOp_zero, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun q hq => ?_
  obtain ⟨hne, hq⟩ := Finset.mem_erase.1 hq
  rw [mem_antidiagonal] at hq
  have hq1 : q.1 ≠ 0 := by
    rintro h0
    apply hne
    ext1
    · exact h0
    · simpa [h0] using hq
  have hdeg : Finsupp.degree q.2 < k := by
    have e1 : Finsupp.degree β = Finsupp.degree q.1 + Finsupp.degree q.2 := by rw [← hq, map_add (f := _)]
    have e2 : Finsupp.degree q.1 ≠ 0 := fun h => hq1 ((Finsupp.degree_eq_zero_iff q.1).1 h)
    rw [PI.HJP.sum_eq_degree] at hβ
    omega
  refine Submodule.smul_mem _ _ ?_
  show hasse X la G.w q.2 (x : Lw X la G.w) ∈ _
  have h3 := hasse_jid_power X la G.w wF q.2 k _ ((mem_pow_smul_top_iff la G.w).1 hx)
  rw [PI.HJP.sum_eq_degree] at h3
  exact PI.HJP.JHfr_anti X la G.w wF (by omega) h3

end PI.PoleLengthCount
end
end
