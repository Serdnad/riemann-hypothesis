module

import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IsClosedSLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open MeasureTheory Topology Filter Matrix
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem inS_pres {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : ℕ) :
    ∀ y ∈ spanLt e a, g *ᵥ y ∈ spanLt e a := by
  apply Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HC.spanLt_pres <;> assumption

theorem inS_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hh : InS e z h) : InS e z (g * h) := by
  have key : ∀ v : Fin n → ℂ, (g * h - 1) *ᵥ v = g *ᵥ ((h - 1) *ᵥ v) + (g - 1) *ᵥ v := fun v => by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  refine ⟨fun a => ?_, ?_⟩
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg a.1 _ (hh.1 a)) (hg.1 a)
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg r _ hh.2) hg.2

theorem inS_one : InS e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun a => by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _,
    by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _⟩

def SG : Subgroup (Formalism.REAL.UJ ε) where
  carrier := SLoc ε e z
  one_mem' := inS_one e z
  mul_mem' {a b} ha hb := inS_mul e z ha hb
  inv_mem' {a} ha := Formalism.L2.SG.RealObj.InfCut.inS_inv _ _ (Formalism.MainNotions.S.uMat a) (Formalism.MainNotions.S.uMat a⁻¹)
    (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' a) ha

theorem coe_SG : (SG ε e z : Set (Formalism.REAL.UJ ε)) = SLoc ε e z := rfl

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  ((Formalism.REAL.uJEmb n ε).1).continuous

theorem SG_closed : IsClosed (SG ε e z : Set (Formalism.REAL.UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ v) := fun v =>
    ((continuous_uMat ε).sub continuous_const).matrix_mulVec continuous_const
  have e1 : (SG ε e z : Set (Formalism.REAL.UJ ε)) =
      (⋂ a : Fin r, (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ e a) ⁻¹' (spanLt e a.1 : Set (Fin n → ℂ))) ∩
        (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ z) ⁻¹' (spanLt e r : Set (Fin n → ℂ)) := by
    ext g
    simp only [coe_SG, SLoc, InS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
  rw [e1]
  exact (isClosed_iInter fun a => (Submodule.closed_of_finiteDimensional _).preimage (hc _)).inter
    ((Submodule.closed_of_finiteDimensional _).preimage (hc _))

section Sub

variable {ε e z}

end Sub

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end

section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem bruhatHaar_of (hI : IterGauge) (hS : GaugeShift) (hR : RhsLim) : BruhatHaar := by
  intro k r μ μb hμ hμb φ hφ
  obtain ⟨C, hC, hF⟩ := hI k r μ μb hμ hμb
  have hlim1 : Tendsto (fun ρ : ℝ => (μ (gBall k r ρ)).toReal / gVol k r ρ) (𝓝[>] 0) (𝓝 1) := hμ.2
  have hlim2 := (hR k r μb hμb).const_mul (C : ℝ)
  have heq : ∀ᶠ ρ in 𝓝[>] (0:ℝ), (μ (gBall k r ρ)).toReal / gVol k r ρ =
      (C : ℝ) * ((rhs k r μb ((wBall k r ρ).indicator 1)).toReal / gVol k r ρ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    obtain ⟨hm, he⟩ := hS k r μ hμ.1 ρ hρ
    have h1 : ∫⁻ x, (wBall k r ρ).indicator 1 x ∂μ = μ (wBall k r ρ) := lintegral_indicator_one hm
    have h2 := hF _ (measurable_one.indicator hm)
    rw [h1, he] at h2
    rw [h2, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_div_assoc]
  have hu := tendsto_nhds_unique (hlim1.congr' heq) hlim2
  have h2r : (0:ℝ) < 2 ^ r := by positivity
  have hCr : (C : ℝ) = 2 ^ r := by
    field_simp at hu
    linarith
  have hCe : (C : ℝ≥0∞) = ENNReal.ofReal (2 ^ r) := by
    rw [← hCr, ENNReal.ofReal_coe_nnreal]
  rw [hF φ hφ, hCe]
  rfl

theorem bruhatHaar_of_iterGauge (hI : IterGauge) (hS : GaugeShift) (hW : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of hI hS (rhsLim_of hW hV)

end Formalism.L2.SG.Pf.BH
end
end

section

namespace Formalism.L2.SG.Pf

theorem ooLintSumC_outright : OOLintSumC :=
  ooLintSumC_holds_slab Formalism.L2.SG.Pf.SlabMajPt.pointwise_majorant_by_columns Formalism.L2.SG.Pf.SlabCount.countC_holds

theorem absConvC_outright : Formalism.L2.SG.Full.AbsConvC := absConvC_holds_of ooLintSumC_outright

end Formalism.L2.SG.Pf
end

section

noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.RealObj.EnergyIntTor

variable {k r : ℕ}

theorem tE_eq_one_of_mem_middle_block (μ : ℂ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : tE μ k r i = 1 := by
  unfold Formalism.L2.SG.Pf.Choice.tE
  rw [if_neg (by omega), if_neg (by omega)]

theorem torS_apply (μ : ℂ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (torS μ k r * m * torS μ⁻¹ k r) i j = tE μ k r i * m i j * tE μ⁻¹ k r j := by
  have e1 : torS μ k r = Matrix.diagonal (tE μ k r) := rfl
  have e2 : torS μ⁻¹ k r = Matrix.diagonal (tE μ⁻¹ k r) := rfl
  rw [e1, e2, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem tor_comm (μ : ℂ) {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : torS μ k r * h = h * torS μ k r := by
  have hb := WeylGroupFacts.uw_block hh
  ext i j
  rw [torS_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hb.2 i j hi]
    by_cases hij : i = j
    · subst hij; simp [mul_comm]
    · simp [hij]
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hb.1 i j hj]
      by_cases hij : i = j
      · subst hij; simp [mul_comm]
      · simp [hij]
    · rw [tE_eq_one_of_mem_middle_block μ i (by omega) (by omega), tE_eq_one_of_mem_middle_block μ j (by omega) (by omega), one_mul, mul_one]

theorem tor_conj_uw {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    torS μ k r * h * torS μ⁻¹ k r = h := by
  rw [tor_comm μ hh, Matrix.mul_assoc, torS_mul_inv μ hμ, Matrix.mul_one]

theorem tor_mulVec_wb (μ : ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : torS μ k r *ᵥ z = z := by
  funext i
  rw [show torS μ k r = Matrix.diagonal (tE μ k r) from rfl, Matrix.mulVec_diagonal]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · push_neg at h
    rw [tE_eq_one_of_mem_middle_block μ i h.1 h.2, one_mul]

theorem ell_tor {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (torS μ k r * m * torS μ⁻¹ k r) = μ * ell k r z m := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [torS_apply, tE_eI, show eI k r ⟨a.val + 1, ha⟩ = eI k r ⟨a.val + 1, ha⟩ from rfl, tE_eI]
    simp only []
    have e : r - (a : ℕ) = (r - ((a : ℕ) + 1)) + 1 := by omega
    rw [e, pow_succ, inv_pow]
    field_simp
  · have hv : (torS μ k r * m * torS μ⁻¹ k r) *ᵥ z = torS μ k r *ᵥ (m *ᵥ z) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tor_mulVec_wb μ⁻¹ hz]
    rw [hv, torS_eq, Matrix.mulVec_diagonal, tE_eI]
    have e : r - (a : ℕ) = 1 := by have := a.isLt; omega
    rw [e, pow_one]

theorem psi_tor {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psi k r z c (torS μ k r * m * torS μ⁻¹ k r) = psi k r z (c * μ) m := by
  unfold Formalism.QuantumDeterminants.psi
  rw [ell_tor hμ hz m, ← mul_assoc]

theorem tor_mem_UH {μ : ℂ} (hμ : μ ≠ 0) : torS μ k r ∈ UH (Hpk k r) := torS_gram μ hμ

theorem UH_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r))
    (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b by
    simp only [Matrix.mul_assoc], ha', hb']

theorem tor_conj_N {μ : ℂ} (hμ : μ ≠ 0) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) : torS μ k r * a * torS μ⁻¹ k r ∈ Nset k r := by
  obtain ⟨hU, hc1, hc2⟩ := ha
  refine ⟨UH_mul (UH_mul (tor_mem_UH hμ) hU) (tor_mem_UH (inv_ne_zero hμ)), fun b i hbi => ?_, fun i j h1 h2 h3 => ?_⟩
  · rw [torS_apply, hc1 b i hbi]
    split_ifs with h
    · subst h; rw [mul_one, tE_mul_inv μ hμ]
    · simp
  · rw [torS_apply, hc2 i j h1 h2 h3]
    split_ifs with h
    · subst h; rw [mul_one, tE_mul_inv μ hμ]
    · simp

end Formalism.L2.SG.RealObj.EnergyIntTor
end
end
