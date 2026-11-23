module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

namespace KThetaFirstCoordSplit

theorem term_le {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ)
    (hY : Y.PosDef) (hρ : 0 < ρ) (hρY : Y⁻¹ 0 0 = ρ ^ 2) (k : Fin g → ℤ) :
    exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := by
  set v := intVec k + (a + u₁) with hv
  have hassoc : intVec k + a + u₁ = v := add_assoc _ _ _
  rw [hassoc]
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) with hδ
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg
  have hv0 : v 0 = (k 0 : ℝ) + (a 0 + u₁ 0) := by simp [hv, intVec]
  have hδle : δ ≤ |v 0| := by
    have h := Metric.infDist_le_dist_of_mem (x := u₁ 0 + a 0)
      (Set.mem_range_self (f := ((↑) : ℤ → ℝ)) (-(k 0)))
    refine h.trans (le_of_eq ?_)
    rw [Real.dist_eq, hv0]
    congr 1
    push_cast
    ring
  have hδsq : δ ^ 2 ≤ v 0 ^ 2 := by
    rw [← sq_abs (v 0)]
    exact pow_le_pow_left₀ hδ0 hδle 2
  have hcoord : v 0 ^ 2 ≤ ρ ^ 2 * qf Y v := by
    have := KCoord.sq_coord_le Y hY 0 v
    rwa [hρY] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hkey : δ ^ 2 / ρ ^ 2 ≤ qf Y v := by
    rw [div_le_iff₀ hρ2]
    linarith [mul_comm (ρ ^ 2) (qf Y v)]
  have hexp : exp (-(π / 2) * qf Y v) ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := by
    apply exp_le_exp.2
    have h1 : (π / (2 * ρ ^ 2)) * δ ^ 2 = (π / 2) * (δ ^ 2 / ρ ^ 2) := by
      field_simp
    have h2 : (π / 2) * (δ ^ 2 / ρ ^ 2) ≤ (π / 2) * qf Y v :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    linarith
  have hsplit : exp (-π * qf Y v) = exp (-(π / 2) * qf Y v) * exp (-(π / 2) * qf Y v) := by
    rw [← exp_add]
    ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hexp (exp_pos _).le

end KThetaFirstCoordSplit

theorem ThetaFirstCoordSplit.proof : ThetaFirstCoordSplit.Statement := by
  intro g _ Y ρ a u₁ hY hρ hρY
  have hs1 : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hs2 : Summable fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + (a + u₁))) :=
    KTheta.summable_exp_qf Y hY (π / 2) (by positivity) (a + u₁)
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun k => KThetaFirstCoordSplit.term_le Y ρ a u₁ hY hρ hρY k) hs1 (hs2.mul_left _)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

namespace KThetaInnerMean

theorem thetaSummand_shift {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ)
    (k : Fin g → ℤ) :
    thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k =
      Complex.exp (((2 * π * ∑ i, a i * u₂ i : ℝ) : ℂ) * Complex.I) *
        (thetaSummand X Y a b
            (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k *
          torusChar k u₂) := by
  unfold thetaSummand torusChar
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [dotProduct, Pi.add_apply, Pi.zero_apply, intVec, Complex.ofReal_zero, add_zero,
    mul_add, add_mul, Finset.sum_add_distrib, Complex.ofReal_add, Complex.ofReal_intCast,
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat]
  ring

end KThetaInnerMean


open KThetaInnerMean in
theorem ThetaInnerMean.proof (h₁ : ThetaSummandNorm.Statement) (h₂ : ThetaCubeParseval.Statement) :
    ThetaInnerMean.Statement := by
  intro g X Y a b u₁ hY
  have hS : Y.IsSymm := by
    have h := hY.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set E : ℝ := exp (-π * qf Y u₁) with hE
  have hEpos : 0 < E := exp_pos _
  set c : (Fin g → ℤ) → ℂ := fun k => thetaSummand X Y a b
    (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k with hc
  have hcE : ∀ k, ‖c k‖ * E = exp (-π * qf Y (intVec k + a + u₁)) := fun k =>
    h₁ g X Y a b u₁ 0 k hS
  have hcs : Summable fun k => ‖c k‖ := by
    have hs := (KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)).mul_right E⁻¹
    refine hs.congr fun k => ?_
    rw [← add_assoc, ← hcE k, mul_assoc, mul_inv_cancel₀ hEpos.ne', mul_one]
  have hN : ∀ u₂, thetaNorm X Y a b u₁ u₂ ^ 2 = ‖∑' k, c k * torusChar k u₂‖ ^ 2 * E ^ 2 := by
    intro u₂
    have h : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ * E := rfl
    rw [h, tsum_congr (fun k => thetaSummand_shift X Y a b u₁ u₂ k), tsum_mul_left, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_pow _ _ _
  simp only [hN]
  rw [integral_mul_const, h₂ g c hcs, ← tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [← mul_pow, hcE k, ← exp_nat_mul]
  congr 1
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

namespace KThetaMean

variable {g : ℕ}

theorem continuous_exp_qf_add (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (a : Fin g → ℝ) :
    Continuous fun x : Fin g → ℝ => exp (-c * qf Y (x + a)) := by
  have h1 : Continuous fun x : Fin g → ℝ => x + a := continuous_id.add continuous_const
  have h2 : Continuous fun x : Fin g → ℝ => qf Y (x + a) := by
    unfold qf
    exact h1.dotProduct (continuous_const.matrix_mulVec h1)
  exact (continuous_const.mul h2).rexp

end KThetaMean

theorem ThetaMean.proof (h : ThetaInnerMean.Statement) : ThetaMean.Statement := by
  intro g X Y a b hY
  set F : (Fin g → ℝ) → ℝ := fun x => exp (-(2 * π) * qf Y (x + a)) with hF
  have hinner : ∀ u₁ : Fin g → ℝ,
      ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1, thetaNorm X Y a b u₁ u₂ ^ 2 =
        ∑' k : Fin g → ℤ, F (intVec k + u₁) := by
    intro u₁
    rw [h g X Y a b u₁ hY]
    congr 1
    simp [hF, add_assoc, add_comm, add_left_comm]
  simp_rw [hinner]
  have hs : ∀ u : Fin g → ℝ, Summable fun k : Fin g → ℤ => F (intVec k + u) := by
    intro u
    simp only [hF, add_assoc]
    exact KTheta.summable_exp_qf Y hY (2 * π) (by positivity) (u + a)
  rw [KTheta.integral_cube_tsum F (fun x => (exp_pos _).le)
    (KThetaMean.continuous_exp_qf_add Y (2 * π) a) hs]
  rw [hF, integral_add_right_eq_self (fun x : Fin g → ℝ => exp (-(2 * π) * qf Y x)) a]
  exact KTheta.integral_exp_two_pi_qf Y hY

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

namespace KThetaNormMajorant

theorem isSymm_of_posDef {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) : Y.IsSymm := by
  have h := hY.isHermitian
  unfold Matrix.IsHermitian at h
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

end KThetaNormMajorant

theorem ThetaNormMajorant.proof (h : ThetaSummandNorm.Statement) : ThetaNormMajorant.Statement := by
  intro g X Y a b u₁ u₂ hY
  have hS := KThetaNormMajorant.isSymm_of_posDef hY
  set z : Fin g → ℂ := periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ) with hz
  set E : ℝ := exp (-π * qf Y u₁) with hE
  have hEpos : 0 < E := exp_pos _
  have hterm : ∀ k : Fin g → ℤ,
      ‖thetaSummand X Y a b z k‖ = exp (-π * qf Y (intVec k + a + u₁)) * E⁻¹ := by
    intro k
    rw [← h g X Y a b u₁ u₂ k hS, mul_inv_cancel_right₀ hEpos.ne']
  have hG : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π Real.pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hsum : Summable fun k : Fin g → ℤ => ‖thetaSummand X Y a b z k‖ := by
    simp_rw [hterm]
    exact hG.mul_right _
  have hN : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b z k‖ * E := rfl
  rw [hN]
  calc ‖∑' k, thetaSummand X Y a b z k‖ * E
      ≤ (∑' k, ‖thetaSummand X Y a b z k‖) * E :=
        mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsum) hEpos.le
    _ = ∑' k, ‖thetaSummand X Y a b z k‖ * E := (tsum_mul_right).symm
    _ = ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) := by
        congr 1; funext k
        rw [hterm, inv_mul_cancel_right₀ hEpos.ne']

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder

noncomputable section

def GrassGeomDegChart.Statement : Prop :=
  ∀ n : ℕ, ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
    geomDeg (grassIdeal 1 1 n) (fsMulti (plBlocks 1 1 n)) n = chartMass (Bᴴ * B)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyCongruence

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_ne_zero_of_star_mul_self {U : Matrix n n ℂ} (hU : star U * U = 1) : U.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hU
  rw [det_mul, h, mul_zero, det_one] at this
  exact zero_ne_one this

theorem exists_congr_eq_one {N : Matrix n n ℂ} (hN : N.PosDef) :
    ∃ C : Matrix n n ℂ, C.det ≠ 0 ∧ Cᴴ * N * C = 1 := by
  set U : Matrix n n ℂ := (hN.1.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set μ := hN.1.eigenvalues
  set d : n → ℂ := fun j => (((Real.sqrt (μ j))⁻¹ : ℝ) : ℂ) with hd
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hN' : N = U * diagonal (fun j => (μ j : ℂ)) * star U := hN.1.spectral_theorem
  have hμ : ∀ j, 0 < μ j := hN.eigenvalues_pos
  refine ⟨U * diagonal d, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine mul_ne_zero (det_ne_zero_of_star_mul_self hU) (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
    have := Real.sqrt_pos.mpr (hμ j)
    simp only [hd, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact this.ne'
  · have hstar : Uᴴ = star U := rfl
    rw [hN', conjTranspose_mul, diagonal_conjTranspose, hstar]
    calc diagonal (star d) * star U * (U * diagonal (fun j => (μ j : ℂ)) * star U) * (U * diagonal d)
        = diagonal (star d) * (star U * U) * diagonal (fun j => (μ j : ℂ)) * (star U * U) * diagonal d := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          funext j
          have hs := Real.sqrt_pos.mpr (hμ j)
          have hsq := Real.sq_sqrt (hμ j).le
          simp only [hd, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
          congr 1
          field_simp
          linarith

theorem det_congr (C X : Matrix n n ℂ) :
    (Cᴴ * X * C).det = (Complex.normSq C.det : ℂ) * X.det := by
  rw [det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end ChartEnergyCongruence


open ChartEnergyCongruence in
theorem ChartEnergy.proof (hI : ChartEnergyLinearInvariant.Statement) (hD : ChartEnergyDiagonal.Statement) :
    ChartEnergy.Statement := by
  intro e M N hM hN
  obtain ⟨C, hC, hCN⟩ := exists_congr_eq_one hN
  have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)
  have hM' : (Cᴴ * M * C).PosDef := hM.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hCu)
  set M' := Cᴴ * M * C with hM'def
  set V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := (hM'.1.eigenvectorUnitary : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
  set Λ := hM'.1.eigenvalues
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVd : V.det ≠ 0 := det_ne_zero_of_star_mul_self hVV
  have hdiag : Vᴴ * M' * V = diagonal (fun j => (Λ j : ℂ)) := by
    have := hM'.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  have hone : Vᴴ * 1 * V = 1 := by rw [Matrix.mul_one]; exact hVV
  have hterm : ∀ k, chartMixedEnergy M N k = chartMixedEnergy (diagonal fun j => (Λ j : ℂ)) 1 k := by
    intro k
    rw [← hI e M N C hM hN hC k, hCN, ← hI e M' 1 V hM' PosDef.one hVd k, hdiag, hone]
  rw [Finset.sum_congr rfl fun k _ => hterm k, hD e Λ hM'.eigenvalues_pos]

  have hMpos := (Complex.pos_iff.mp hM.det_pos).1
  have hNpos := (Complex.pos_iff.mp hN.det_pos).1
  have hns : 0 < Complex.normSq C.det := Complex.normSq_pos.mpr hC
  have hM're : M'.det.re = Complex.normSq C.det * M.det.re := by
    rw [hM'def, det_congr, Complex.re_ofReal_mul]
  have hN're : 1 = Complex.normSq C.det * N.det.re := by
    have := congrArg Complex.re (det_congr C N)
    rw [hCN, det_one, Complex.one_re, Complex.re_ofReal_mul] at this
    exact this
  have hprod : M'.det.re = ∏ j, Λ j := by
    rw [hM'.1.det_eq_prod_eigenvalues]
    change (∏ j, ((Λ j : ℝ) : ℂ)).re = _
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have hlog : ∑ j, Real.log (Λ j) = Real.log M.det.re - Real.log N.det.re := by
    rw [← Real.log_prod fun j _ => (hM'.eigenvalues_pos j).ne', ← hprod, hM're,
      Real.log_mul hns.ne' hMpos.ne']
    have h1 : Real.log (Complex.normSq C.det) + Real.log N.det.re = 0 := by
      rw [← Real.log_mul hns.ne' hNpos.ne', ← hN're, Real.log_one]
    linarith
  rw [hlog]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace NefOfNonnegAlt

theorem geoNum_zero_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 V a := by
  unfold geoNum
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem geoNum_one_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 V (fun _ => a) := by
  unfold geoNum
  split_ifs
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    refine finsum_nonneg fun W => finsum_nonneg fun _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (geoNum_zero_nonneg _ _)
  · exact le_rfl

end NefOfNonnegAlt

theorem NefOfNonneg.proof : NefOfNonneg.Statement := by
  intro K _ ι _ P a ha W _ _ _ _
  exact NefOfNonnegAlt.geoNum_one_nonneg W a ha

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

def PtsIntegralZeroLowerNE.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ),
    IsMultiHomogIdeal W → Finite (McClasses W) →
    (∀ (u : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, u k ≠ 0) → z ∈ mcPts W →
      g (fun p => u p.1 * z p) = g z) →
    (∀ z ∈ mcPts W, c ≤ g z) →
    c * degC W ≤ ptsIntegral (e := 0) W φ g

theorem anchor_minor {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 = Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

end

end GroundTheory.Heights₂.Heights
end
