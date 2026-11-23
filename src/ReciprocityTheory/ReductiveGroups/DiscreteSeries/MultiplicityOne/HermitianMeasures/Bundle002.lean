module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.Bundle001
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem psiGen_norm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat k r) :
    ‖Formalism.MainNotions.S.psiGen k r z c g‖ = 1 := by
  unfold Formalism.MainNotions.S.psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem ellA_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {m m' : Mat k r}
    (hm : m ∈ Nset k r) (hm' : m' ∈ Nset k r) (a : Fin r) :
    Formalism.MainNotions.S.ellA k r z (m * m') a = Formalism.MainNotions.S.ellA k r z m a + Formalism.MainNotions.S.ellA k r z m' a := by
  have hc := ((nset_iff m).1 hm).2
  have hc' := ((nset_iff m').1 hm').2
  have hi : (Formalism.QuantumDeterminants.eI k r a).val < r := a.isLt
  unfold Formalism.MainNotions.S.ellA
  split_ifs with h
  · exact mul_apply_add hc hc' _ _ hi
      (show (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩).val ≤ r + k by show a.val + 1 ≤ r + k; omega)
      (show (Formalism.QuantumDeterminants.eI k r a).val < (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩).val by
        show a.val < a.val + 1; omega)
      (Or.inl (show (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩).val ≤ (Formalism.QuantumDeterminants.eI k r a).val + 1 by
        show a.val + 1 ≤ a.val + 1; omega))
  · simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : r ≤ q.val ∧ q.val ≤ r + k
    · rw [mul_apply_add hc hc' _ _ hi hq.2
        (show (Formalism.QuantumDeterminants.eI k r a).val < q.val by show a.val < q.val; omega)
        (Or.inr (show r ≤ (Formalism.QuantumDeterminants.eI k r a).val + 1 by show r ≤ a.val + 1; omega)), add_mul]
    · have hz0 : z q = 0 := hz q (by omega)
      rw [hz0, mul_zero, mul_zero, mul_zero, add_zero]

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem ellA_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) (a : Fin r) :
    Formalism.MainNotions.S.ellA k r z (h * m * h⁻¹) a = Formalism.MainNotions.S.ellA k r z m a := by
  have hb := uw_block hh
  have hb' := uw_block (uw_inv hh)
  have hz' : h⁻¹ *ᵥ z = z := (uw_inv hh).2.2
  have hrow : ∀ p, h (Formalism.QuantumDeterminants.eI k r a) p = if Formalism.QuantumDeterminants.eI k r a = p then 1 else 0 :=
    fun p => hb.2 _ p (Or.inl (show (Formalism.QuantumDeterminants.eI k r a).val < r from a.isLt))
  unfold Formalism.MainNotions.S.ellA
  split_ifs with h1
  · have hcol : ∀ q, h⁻¹ q (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h1⟩) =
        if q = Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h1⟩ then 1 else 0 :=
      fun q => hb'.1 q _ (Or.inl (show (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h1⟩).val < r from h1))
    rw [mul_apply_of_col _ _ _ hcol, mul_apply_of_row _ _ _ hrow]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_apply_of_row _ _ hrow, hz']

theorem psiGen_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) {m m' : Mat k r}
    (hm : m ∈ Nset k r) (hm' : m' ∈ Nset k r) :
    Formalism.MainNotions.S.psiGen k r z c (m * m') = Formalism.MainNotions.S.psiGen k r z c m * Formalism.MainNotions.S.psiGen k r z c m' := by
  unfold Formalism.MainNotions.S.psiGen
  rw [← Complex.exp_add]
  have e : ∑ a, c a * Formalism.MainNotions.S.ellA k r z (m * m') a =
      (∑ a, c a * Formalism.MainNotions.S.ellA k r z m a) + ∑ a, c a * Formalism.MainNotions.S.ellA k r z m' a := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ellA_mul hz hm hm' a, mul_add]
  rw [e, Complex.add_re, Complex.ofReal_add, mul_add]

theorem psiGen_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) :
    Formalism.MainNotions.S.psiGen k r z c (h * m * h⁻¹) = Formalism.MainNotions.S.psiGen k r z c m := by
  unfold Formalism.MainNotions.S.psiGen
  have e : ∑ a, c a * Formalism.MainNotions.S.ellA k r z (h * m * h⁻¹) a = ∑ a, c a * Formalism.MainNotions.S.ellA k r z m a :=
    Finset.sum_congr rfl fun a _ => by rw [ellA_conj hz hh hm a]
  rw [e]

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem haarUp (hSF : HaarUniqueSF) {k r : ℕ} {U : Set (Mat k r)} {μ₀ μ : Measure (Mt k r)}
    (hU : IsClosedSubgroup U) (h₀ : Formalism.FourierDecayAlt.B.IsHaarOn U μ₀) (hμ : Formalism.MainNotions.S.IsHaarOn U μ) :
    Formalism.FourierDecayAlt.B.IsHaarOn U μ := by
  obtain ⟨c, hc0, rfl⟩ := hSF k r U μ₀ μ hU h₀ hμ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.smul_apply, h₀.conc, smul_zero]
  · intro a ha
    have hcont : Continuous (lmulM a : Mt k r → Mt k r) := by
      unfold lmulM
      exact Continuous.matrix_mul continuous_const continuous_id
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h₀.left a ha]
  · intro a ha
    have hcont : Continuous (rmulF a : Mt k r → Mt k r) := by
      unfold rmulF
      exact Continuous.matrix_mul continuous_id continuous_const
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h₀.right a ha]
  · intro K hK
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h₀.finite_compact K hK)
  · exact smul_ne_zero hc0 h₀.ne_zero

theorem isHaarOn_fourier_of_isHaarOn_main (hSF : HaarUniqueSF) (hCW : ClosedW) (hHW : HaarWExists) {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hμ : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW := by
  obtain ⟨μ₀, h₀⟩ := hHW k r z hz hT
  exact haarUp hSF (hCW k r z) h₀ hμ

theorem haarUp_N (hSF : HaarUniqueSF) (hCN : ClosedN) (hHN : HaarNExists) {k r : ℕ}
    {μN : Measure (Mt k r)} (hμ : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN := by
  obtain ⟨μ₀, h₀⟩ := hHN k r
  exact haarUp hSF (hCN k r) h₀ hμ

theorem haar_measure_univ_lt_infinity_of_compactW (hCpW : CompactW) {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hμ : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW) : μW Set.univ < ∞ := by
  have hK : μW (UWset k r z : Set (Mt k r)) < ∞ := hμ.finite_compact _ (hCpW k r z hz hT)
  have hc : μW (UWset k r z : Set (Mt k r))ᶜ = 0 := hμ.conc
  refine lt_of_le_of_lt (measure_univ_le_add_compl (μ := μW) (UWset k r z : Set (Mt k r))) ?_
  exact ENNReal.add_lt_top.2 ⟨hK, hc ▸ ENNReal.zero_lt_top⟩

theorem conjInv_N (hSF : HaarUniqueSF) (hCN : ClosedN) (hHN : HaarNExists) (hc : ConjInvRaw) {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {μN : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hμ : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN :=
  hc k r z μN hz hT (haarUp_N hSF hCN hHN hμ)

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem nIntAt_zero (hNB : NBase) (k : ℕ) : NIntAt k 0 := by
  intro μN hH b _
  have hc := hH.conc
  rw [hNB k] at hc
  have hae : ∀ᵐ x ∂μN, x ∈
      ({(show Mt k 0 from (1 : Matrix (Fin (2 * 0 + k + 1)) (Fin (2 * 0 + k + 1)) ℂ))} : Set (Mt k 0)) := by
    rw [ae_iff]
    exact hc
  rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_singleton]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hH.finite_compact _ isCompact_singleton)

theorem nIntAt_all (hNB : NBase) (hNR : NRecHaar) (hHU : HaarUnique) (hCN : ClosedN) (hHN : HaarNExists)
    (hGL : GNLower) (k r : ℕ) : NIntAt k r := by
  induction r with
  | zero => exact nIntAt_zero hNB k
  | succ r' ih =>
    have h := nIntAt_step hNR hHU hCN hHN hGL k r' ih
    rwa [Nat.add_comm 1 r'] at h

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
end
end
