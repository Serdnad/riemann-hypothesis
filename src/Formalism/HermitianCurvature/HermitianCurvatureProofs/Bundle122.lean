module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GNMulRpow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L1QuotientIntegralBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylCellRange.ReflectionMultiplicationOnBigCell
public import Formalism.FormalDegreeBessel.Bundle002
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle080
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem l_le_I {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {l : H → Wp} (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be z c π σ μW μN x y = (innerSL ℂ (l y)).smulRight (l x))
    {v : H} (hv : v ∈ DDsp σ w0) (hlv : l v ≠ 0) (hw0DD : w0 ∈ DDsp σ w0)
    {e1 : Mx k r → ℂ} (hee1 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e1 g = ⟪v, σ g w0⟫_ℂ)
    {zz : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ (‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) *
      ∫⁻ p, (fun m : Formalism.QuantumDeterminants.Mt k r => ‖e1 (Matrix.of m)‖ₑ)
        (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) i j) ∂(μW.prod μN) := by
  have b1 := l_enorm_le (c := c) hds hT hπ hW hN hbe hv hlv hw0DD hz
  refine b1.trans (le_of_eq ?_)
  congr 1
  apply lintegral_congr_ae
  filter_upwards [prod_ae hW hN] with p hp
  show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) w0⟫_ℂ‖ₑ =
    ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz)‖ₑ
  rw [hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hz)]

theorem e_weight {e : Mx k r → ℂ} {C a b : ℝ}
    (hb : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e y‖ ≤ C * B.gN y ^ (-a))
    {x : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hpos : 0 < B.gN x) :
    ‖e x‖ₑ * ENNReal.ofReal (B.gN x ^ b) ≤ ENNReal.ofReal |C| * ‖B.gN x ^ (-(a - b))‖ₑ := by
  have h1 := hb x hx
  have h2 : ‖e x‖ * B.gN x ^ b ≤ |C| * B.gN x ^ (-(a - b)) := by
    have e2 : B.gN x ^ (-(a - b)) = B.gN x ^ (-a) * B.gN x ^ b := by
      rw [← Real.rpow_add hpos]
      ring_nf
    rw [e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hpos.le _)))
      (Real.rpow_nonneg hpos.le _)
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _),
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h2

def Iint (A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (z : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) ∂μ

def Aext (e : Mx k r → ℂ) (m : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ := ‖e (Matrix.of m)‖ₑ

theorem Aext_meas {e : Mx k r → ℂ} (he : Continuous e) : Measurable (Aext e) := by
  unfold Aext
  exact (Continuous.enorm (he.comp (show Continuous (fun m : Formalism.QuantumDeterminants.Mt k r => Matrix.of m) from continuous_id))).measurable

theorem Iint_meas {A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μ] : Measurable (Iint A μ) := by
  unfold Iint
  refine Measurable.lintegral_prod_right' (f := fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
    A (fun i j => (Matrix.of q.2.1 * Matrix.of q.2.2 * Matrix.of q.1) i j)) ?_
  refine hA.comp (Continuous.measurable ?_)
  exact ((continuous_snd.fst.matrix_mul continuous_snd.snd).matrix_mul continuous_fst)

theorem unfold_Iint {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {A Ψ : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A) (hΨ : Measurable Ψ)
    (hinv : ∀ᵐ z ∂νq, ∀ᵐ p ∂(μW.prod μN),
      Ψ (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) = Ψ z) :
    ∫⁻ z, Iint A (μW.prod μN) z * Ψ z ∂νq = ∫⁻ x, A x * Ψ x ∂μG := by
  have hcont : ∀ z : Formalism.QuantumDeterminants.Mt k r,
      Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of s * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    fun z => Continuous.matrix_mul continuous_id continuous_const
  have hg : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    (show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul continuous_fst continuous_snd).measurable
  rw [hq (fun x => A x * Ψ x) (hA.mul hΨ)]
  refine lintegral_congr_ae ?_
  filter_upwards [hinv] with z hz
  unfold Iint Formalism.FourierDecayAlt.ThreeDimData.muSof
  rw [lintegral_map (f := fun s : Formalism.QuantumDeterminants.Mt k r => A (fun i j => (Matrix.of s * Matrix.of z) i j) *
      Ψ (fun i j => (Matrix.of s * Matrix.of z) i j))
    (by exact (hA.comp (hcont z).measurable).mul (hΨ.comp (hcont z).measurable)) hg]
  have hmA : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j)) :=
    hA.comp ((show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul (Continuous.matrix_mul continuous_fst continuous_snd) continuous_const).measurable)
  rw [← lintegral_mul_const _ hmA]
  refine lintegral_congr_ae ?_
  filter_upwards [hz] with p hp
  exact congrArg _ hp.symm

theorem pull2 {νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)} (F G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
    (M : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hm : ∀ z, Measurable fun z' => G z' * M z z') :
    ∫⁻ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' ∂νq = K * ∫⁻ z, F z * ∫⁻ z', G z' * M z z' ∂νq' ∂νq := by
  have h1 : ∀ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' = K * (F z * ∫⁻ z', G z' * M z z' ∂νq') := by
    intro z
    have e1 : (fun z' => K * (F z * (G z' * M z z'))) = fun z' => (K * F z) * (G z' * M z z') := by
      funext z'
      ring
    rw [e1, lintegral_const_mul _ (hm z), mul_assoc]
  simp_rw [h1]
  exact lintegral_const_mul' K _ hK

theorem final2 {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (hF : Measurable Fx)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG ∂μG = c * ((∫⁻ x, Fx x ∂μG) * ∫⁻ y, Fx y ∂μG) := by
  have h1 : ∀ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG = (c * Fx x) * ∫⁻ y, Fx y ∂μG := by
    intro x
    simp_rw [← mul_assoc]
    exact lintegral_const_mul _ hF
  simp_rw [h1]
  rw [lintegral_mul_const _ (hF.const_mul c), lintegral_const_mul _ hF, mul_assoc]

end Formalism.FourierDecayAlt.P.S3dx4
end
end

section

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.Rad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma thr_big (k r m : ℕ) :
    JF.TransportedAlt k r (6 * (r : ℝ) * (m : ℝ) + 9 * ((r : ℝ) + 1) * (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1)) m := by
  unfold JF.TransportedAlt
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [show (0 : ℝ) ≤ (r : ℝ) from Nat.cast_nonneg r]

theorem jf_smoothLev {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) :
    SmoothLev k r 0 (OmPlus k r D.z D.z') (B.JF D F) := by
  refine smoothLev_of_ck (Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus _ _) fun m => ?_
  exact (Formalism.FourierDecayAlt.P.jacquet_derivative_formula k r Wp Wq D _ m F (thr_big k r m) (hF _ m)).1

lemma μE_one (i j : ℕ) : PI.QnWCellW.μE (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j =
    if i < k + 1 ∧ j < k + 1 ∧ i = j then 1 else 0 := by
  unfold PI.QnWCellW.μE
  by_cases h : i < k + 1 ∧ j < k + 1
  · rw [dif_pos h, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [h]
    · rw [if_neg (by simpa [Fin.ext_iff] using hij), if_neg (by tauto)]
  · rw [dif_neg h, if_neg (by tauto)]

theorem wCell_last_eq (c : Fin r → ℂ) : wCell k r (Fin.last r) c = bigCell k r c 1 := by
  rw [PI.QnWCellW.wCell_last]
  ext p q
  rw [PI.QnWCellW.Wm_range_apply, PI.QnWCellW.bigCell_apply]
  simp only [μE_one, PI.QnWCellW.cf, Fin.ext_iff, PI.QnWCellW.swp_val]
  have hp := p.isLt
  have hq := q.isLt
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 3; omega) | (rw [show 2 * r + k - (q : ℕ) = (p : ℕ) by omega])

lemma glev_last_uwb {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) : g ∈ B2.UWb k r := by
  exact ⟨hg.1, fun a => hg.2 a (by simp)⟩

lemma zetaL_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    zetaL k r z z' (Fin.last r) g = herm (Hpk k r) (g *ᵥ z') z := by
  simp only [zetaL, Formalism.FourierDecayAlt.P.Qx5.fvec_last]

theorem wCell_mem_omPlus {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r z z' g) :
    wCell k r (Fin.last r) c * g ∈ OmPlus k r z z' := by
  have hgz' : inWb k r (g *ᵥ z') := by
    intro i hi
    have hi0 := i.isLt
    rcases hi with hi | hi
    · have e1 := Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right (Hpk k r) (g *ᵥ z') (esI k r ⟨i.val, hi⟩)
      rw [← (hg.2 ⟨i.val, hi⟩ (by simpa using hi)).2, Formalism.FourierDecayAlt.P.Qx5.herm_UH hg.1,
        Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right] at e1
      have key : ∀ v : Fin (2 * r + k + 1) → ℂ, (Hpk k r *ᵥ v) (esI k r ⟨i.val, hi⟩) = v i := by
        intro v
        simp only [mulVec, dotProduct, Formalism.FourierDecayAlt.P.Qx3.hpk_row_es, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rfl
      rw [key, key] at e1
      rw [← e1]
      exact hz' i (Or.inl hi)
    · have ha : 2 * r + k - i.val < r := by omega
      have e1 := Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right (Hpk k r) (g *ᵥ z') (eI k r ⟨_, ha⟩)
      rw [← (hg.2 ⟨_, ha⟩ (by simpa using ha)).1, Formalism.FourierDecayAlt.P.Qx5.herm_UH hg.1,
        Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right] at e1
      have hi' : esI k r ⟨_, ha⟩ = i := Fin.ext (by simp only [esI]; omega)
      have key : ∀ v : Fin (2 * r + k + 1) → ℂ, (Hpk k r *ᵥ v) (eI k r ⟨_, ha⟩) = v i := by
        intro v
        simp only [mulVec, dotProduct, Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hi']
      rw [key, key] at e1
      rw [← e1]
      exact hz' i (Or.inr hi)
  have hwv : ∀ v, inWb k r v → bigCell k r c 1 *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv]
    rw [Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, Matrix.one_mulVec, Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv]
  have hZ : Zhat k r z z' (wCell k r (Fin.last r) c * g) = Matrix.diagonal fun a : Fin (r + 1) =>
      if h : a.val < r then c ⟨a.val, h⟩ else zetaL k r z z' (Fin.last r) g := by
    rw [zetaL_last, ← hwv _ hgz', ← Formalism.QuantumDeterminants.bigCellZhat k r z (g *ᵥ z') c 1 hz hgz', wCell_last_eq]
    ext a b
    simp only [Zhat]
    by_cases hb : b.val < r
    · simp only [fvec, dif_pos hb, ← mulVec_mulVec, (hg.2 ⟨b.val, hb⟩ (by simpa using hb)).1]
    · simp only [fvec, dif_neg hb, mulVec_mulVec]
  have hD := fun l => Formalism.QuantumDeterminants.BruhatBigCell.dmin_diag z z' _ _ hZ l
  have h0 : Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨r, by omega⟩ = ∏ a : Fin r, c a := by
    rw [hD]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Fin.val_castLE, a.isLt, dif_pos]
  have h1 : Dmin k r z z' (wCell k r (Fin.last r) c * g) (Fin.last (r + 1)) =
      (∏ a : Fin r, c a) * zetaL k r z z' (Fin.last r) g := by
    rw [hD]
    refine (Fin.prod_univ_castSucc _).trans ?_
    congr 1
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp only [Fin.val_castLE, Fin.val_castSucc, a.isLt, dif_pos]
    · simp
  have hP : (∏ a : Fin r, c a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc a
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [hD]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    have hi : (Fin.castLE (Nat.le_of_lt_succ l.isLt) i).val < r := by
      have := i.isLt
      simp only [Fin.val_castLE]
      omega
    simp only [dif_pos hi]
    exact hc _
  · unfold Gf
    rw [h1, h0, Complex.normSq_mul]
    have hP' : 0 < Complex.normSq (∏ a : Fin r, c a) := Complex.normSq_pos.mpr hP
    have hG' := hG
    unfold GGl at hG'
    nlinarith [mul_pos hP' hG']

theorem GGl_uw {z z' : Fin (2 * r + k + 1) → ℂ} {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (g : Mx k r) : GGl k r z z' (h * g * h') = GGl k r z z' g := by
  simp only [GGl, Formalism.FourierDecayAlt.P.Qx5.zeta_inv hh hh']

theorem domR_uw {z z' : Fin (2 * r + k + 1) → ℂ} {x : (Fin r → ℂ) × Mx k r} (hx : x ∈ DomR k r z z')
    {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    (x.1, h * x.2 * h') ∈ DomR k r z z' := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨h1, ?_, ?_⟩
  · exact Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.UW_Glev hh _) h2)
      (Formalism.FourierDecayAlt.P.Qx5.UW_Glev hh' _)
  · show 0 < GGl k r z z' (h * x.2 * h')
    rw [GGl_uw hh hh']
    exact h3

theorem sf_resG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} {J : Mx k r → E}
    (hJ : SmoothLev k r 0 D J) :
    SmoothFam k r (Fin.last r) {x | x.1 ∈ OmX r ∧ wCell k r (Fin.last r) x.1 * x.2 ∈ D}
      (resG k r (Fin.last r) J) := by
  have hWs : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => wCell k r (Fin.last r) c) (OmX r) := by
    unfold wCell
    exact Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _
  have hWG : ∀ c ∈ OmX r, wCell k r (Fin.last r) c ∈ Glev k r 0 := by
    intro c hc
    unfold wCell
    exact Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hG0 : ∀ x : (Fin r → ℂ) × Mx k r, x.1 ∈ OmX r → x.2 ∈ Glev k r (Fin.last r) →
      wCell k r (Fin.last r) x.1 * x.2 ∈ Glev k r 0 := fun x h1 h2 =>
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (hWG _ h1) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) h2)
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hfF⟩ := hJ _ ⟨hG0 x₀ hx₀.1 hg₀, hx₀.2⟩
  have hM : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => wCell k r (Fin.last r) x.1 * x.2)
      {x | x.1 ∈ OmX r} :=
    Formalism.FourierDecayAlt.P.Qx3.cdo_mul (hWs.comp contDiffOn_fst (fun x hx => hx)) contDiffOn_snd
  have hρ : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ))
      (OmX r) := by
    have hp : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
        ∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1 : ℝ)) (OmX r) :=
      contDiffOn_prod fun a _ => by
        simp only [Fin.val_last, a.isLt, ↓reduceIte]
        exact Formalism.FourierDecayAlt.P.Qx3.cd_normPow a _
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hp
  refine ⟨{x | x.1 ∈ OmX r} ∩ (fun x => wCell k r (Fin.last r) x.1 * x.2) ⁻¹' U,
    fun x => ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
      F (wCell k r (Fin.last r) x.1 * x.2),
    hM.continuousOn.isOpen_inter_preimage ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).preimage continuous_fst) hU,
    ⟨hx₀.1, hmem⟩, ?_, ?_⟩
  · exact (hρ.comp contDiffOn_fst (fun (x : (Fin r → ℂ) × Mx k r) (hx : x ∈ {x : (Fin r → ℂ) × Mx k r | x.1 ∈ OmX r} ∩ (fun x : (Fin r → ℂ) × Mx k r => wCell k r (Fin.last r) x.1 * x.2) ⁻¹' U) => hx.1)).smul
      (hF.comp (hM.mono Set.inter_subset_left) (fun x hx => hx.2))
  · intro x hx hxg
    simp only [resG]
    rw [hfF _ hx.2 (hG0 x hx.1 hxg)]

end Formalism.FourierDecayAlt.P5.Rad
end
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_eq_sum (A C : Wq →L[ℂ] Wp) :
    B.hsInner A C = ∑ m, ⟪C (stdOrthonormalBasis ℂ Wq m), A (stdOrthonormalBasis ℂ Wq m)⟫_ℂ := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply]

end HS

section Adj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_t_adj_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (hK : ∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
      ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (Y : ℂ) (a b : Fin 2)
    (h1 : ∀ m, Integrable (fun x : Mt P.k P.r =>
      ⟪(Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m),
        (X.t Y a b Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m)⟫_ℂ) μ)
    (h2 : ∀ m, Integrable (fun x : Mt P.k P.r =>
      ⟪(X.t (star Y) b a Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m),
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m)⟫_ℂ) μ) :
    pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c := by
  have hA := Formalism.FourierDecayAlt.P.actual_adjointness Wp Wq P z z' π π' hP X μ hμ Φ Ψ c hc hK Y a b
  simp only [pairAt, hsInner_eq_sum]
  rw [integral_finsetSum _ (fun m _ => h1 m), integral_finsetSum _ (fun m _ => h2 m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e := congrArg (starRingEnd ℂ) (hA (stdOrthonormalBasis ℂ Wq m))
  rw [← integral_conj, ← integral_conj] at e
  simp only [inner_conj_symm] at e
  exact e

end Adj

end Formalism.FourierDecayAlt.P5.HerA
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem toSm_of_mem (P : M.Par) {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) (q : MA.Qp P.r P.TT) :
    (MA.toSm P u : MA.Qp P.r P.TT → ℂ) q = u q := by
  unfold MA.toSm
  rw [dite_eq_left h]

theorem assumption_on_sections_holds : AsmSec := by
  intro hFL hGQ hML hRS hRaw hQL Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl
  obtain ⟨e, he, hQQ⟩ := hGQ Wp Wq P Bs hPl hk hsec X
  refine ⟨e, he, fun Dc Φ hΦ Y a b ρ => ?_⟩
  apply Subtype.ext
  funext q
  have hLsm := hRaw Wp Wq P Bs hPl hk e he Dc _ (hQL Wp Wq P Bs hPl hk Dc Φ hΦ Y a b) ρ
  rw [toSm_of_mem P hLsm q]
  obtain ⟨Φt, V, hV, hagree⟩ := hFL Wp Wq P Bs hPl hk X Dc Φ hΦ q
  have h1 : rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ q =
      rawR P Bs.μsec e ((X.t (Y : ℂ) a b Φt : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
    unfold rawR
    rw [((hagree q.1.2 (mem_of_mem_nhds hV)).2 (Y : ℂ) a b).symm]
  rw [h1, ← toSm_of_mem P (hRS Wp Wq P Bs hPl hk e he (X.t (Y : ℂ) a b Φt) ρ) q]
  show (trR P Bs e (X.t (Y : ℂ) a b Φt) ρ : MA.Qp P.r P.TT → ℂ) q = _
  rw [hQQ Φt (Y : ℂ) a b]
  refine hML P (trR P Bs e Φt) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) q.1.1 (interior V) isOpen_interior
    (fun ρ' q' hq'c hq'V => ?_) (Y : ℂ) a b ρ q rfl (mem_interior_iff_mem_nhds.2 hV)
  show (MA.toSm P (rawR P Bs.μsec e (Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ') : MA.Qp P.r P.TT → ℂ) q' =
    (MA.toSm P (rawR P Bs.μsec e Φ ρ') : MA.Qp P.r P.TT → ℂ) q'
  rw [toSm_of_mem P (hRS Wp Wq P Bs hPl hk e he Φt ρ') q',
    toSm_of_mem P (hRaw Wp Wq P Bs hPl hk e he Dc Φ hΦ ρ') q']
  unfold rawR
  rw [hq'c, (hagree q'.1.2 (interior_subset hq'V)).1]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
