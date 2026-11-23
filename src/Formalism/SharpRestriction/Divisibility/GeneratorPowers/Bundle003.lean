module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle001
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.RingTheory.PowerSeries.Exp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

theorem bessel2 {d : ℕ} (v p q : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) (hp : p ⬝ᵥ p = 1)
    (hpq : p ⬝ᵥ q = 0) (hq : 0 < q ⬝ᵥ q) :
    (v ⬝ᵥ p) ^ 2 * (q ⬝ᵥ q) + (v ⬝ᵥ q) ^ 2 ≤ q ⬝ᵥ q := by
  have hr : 0 ≤ ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q) ⬝ᵥ
      ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hqp : q ⬝ᵥ p = 0 := by rw [dotProduct_comm]; exact hpq
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm p v, dotProduct_comm q v, hv, hp, hpq, hqp] at hr
  nlinarith [hr, hq]

theorem halfTrace_holds : HalfTraceStatement := by
  intro d L G K R hLR hR hG hKG hKL hK x
  have hRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  have hRt : Rᵀ * (R⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, hiR, Matrix.transpose_one]
  have htR : (R⁻¹)ᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRi, Matrix.transpose_one]

  have hCpsd : (R * G * Rᵀ).PosSemidef := by
    have := hG.mul_mul_conjTranspose_same R
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hCtr : trace (R * G * Rᵀ) = trace (L * G) := by
    rw [Matrix.trace_mul_cycle, hLR]
  have hJ' : (R⁻¹)ᵀ * K * Rᵀ = -(R * Kᵀ * R⁻¹) := by
    have h2 : (R⁻¹)ᵀ * (K * L) * R⁻¹ = (R⁻¹)ᵀ * (-(L * Kᵀ)) * R⁻¹ := by rw [hKL]
    rw [hLR] at h2
    have e1 : (R⁻¹)ᵀ * (K * (Rᵀ * R)) * R⁻¹ = (R⁻¹)ᵀ * K * Rᵀ := by
      simp only [Matrix.mul_assoc, hRi, Matrix.mul_one]
    have e2 : (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * R⁻¹ = -(R * Kᵀ * R⁻¹) := by
      rw [Matrix.mul_neg, Matrix.neg_mul]
      congr 1
      simp only [← Matrix.mul_assoc, htR, Matrix.one_mul]
    rw [← e1, h2, e2]
  have hJskew : ((R⁻¹)ᵀ * K * Rᵀ)ᵀ = -((R⁻¹)ᵀ * K * Rᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, hJ', neg_neg, Matrix.mul_assoc]
  have hCJ : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) := by
    have l1 : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = R * (G * K) * Rᵀ := by
      calc (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = R * G * (Rᵀ * (R⁻¹)ᵀ) * K * Rᵀ := by
            simp only [Matrix.mul_assoc]
        _ = R * (G * K) * Rᵀ := by rw [hRt, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have l2 : ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) = R * (G * K) * Rᵀ := by
      calc ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) = (R⁻¹)ᵀ * (K * (Rᵀ * R)) * G * Rᵀ := by
            simp only [Matrix.mul_assoc]
        _ = (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * G * Rᵀ := by rw [← hLR, hKL, hLR]
        _ = -(((R⁻¹)ᵀ * Rᵀ) * R * (Kᵀ * G) * Rᵀ) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = R * (G * K) * Rᵀ := by
            rw [htR, hKG, Matrix.one_mul]
            simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [l1, l2]
  have hJdet : IsUnit ((R⁻¹)ᵀ * K * Rᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]
    exact ((Matrix.isUnit_nonsing_inv_det R hR).mul hK).mul hR
  set C := R * G * Rᵀ with hCdef
  set J := (R⁻¹)ᵀ * K * Rᵀ with hJdef
  have hJinj : ∀ v : Fin d → ℝ, J *ᵥ v = 0 → v = 0 := by
    intro v hv
    have : (J⁻¹ * J) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rwa [Matrix.nonsing_inv_mul J hJdet, Matrix.one_mulVec] at this
  have hH : C.IsHermitian := hCpsd.1
  have hCt : Cᵀ = C := by
    have := hH.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsym : ∀ v w : Fin d → ℝ, (C *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (C *ᵥ w) := by
    intro v w
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hCt, dotProduct_comm]

  let ev : Fin d → (Fin d → ℝ) := fun j => ⇑(hH.eigenvectorBasis j)
  let lam : Fin d → ℝ := hH.eigenvalues
  have hCev : ∀ j, C *ᵥ ev j = lam j • ev j := fun j => hH.mulVec_eigenvectorBasis j
  have hort : ∀ i j, ev i ⬝ᵥ ev j = if j = i then 1 else 0 := by
    intro i j
    have := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa [ev, star_trivial] using this
  have hinner : ∀ (v : Fin d → ℝ) j,
      inner ℝ (WithLp.toLp 2 v) (hH.eigenvectorBasis j) = ev j ⬝ᵥ v := by
    intro v j
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [ev, star_trivial]
  have hinner' : ∀ (v : Fin d → ℝ) j,
      inner ℝ (hH.eigenvectorBasis j) (WithLp.toLp 2 v) = ev j ⬝ᵥ v := by
    intro v j
    rw [real_inner_comm]; exact hinner v j
  have hquad : ∀ v : Fin d → ℝ, v ⬝ᵥ (C *ᵥ v) = ∑ j, lam j * (ev j ⬝ᵥ v) ^ 2 := by
    intro v
    have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 (C *ᵥ v))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h
    rw [dotProduct_comm, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_comm (ev j), ← hsym, hCev, smul_dotProduct, smul_eq_mul, dotProduct_comm v]
    ring
  have hpars : ∀ v : Fin d → ℝ, ∑ j, (ev j ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := by
    intro v
    have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 v)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => hCpsd.eigenvalues_nonneg j
  have htr : trace C = ∑ j, lam j := by simpa using hH.trace_eq_sum_eigenvalues

  have hlam : ∀ i, lam i ≤ trace C / 2 := by
    intro i
    set u := J *ᵥ ev i with hu
    have hCu : C *ᵥ u = lam i • u := by
      rw [hu, Matrix.mulVec_mulVec, hCJ, ← Matrix.mulVec_mulVec, hCev, Matrix.mulVec_smul]
    have hvu : ev i ⬝ᵥ u = 0 := by
      have h1 : ev i ⬝ᵥ u = (Jᵀ *ᵥ ev i) ⬝ᵥ ev i := by
        rw [hu, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      rw [hJskew, Matrix.neg_mulVec, neg_dotProduct, ← hu, dotProduct_comm] at h1
      have h2 : u ⬝ᵥ ev i = 0 := by linarith
      rw [dotProduct_comm]; exact h2
    have hv1 : ev i ⬝ᵥ ev i = 1 := by rw [hort, if_pos rfl]
    have hu0 : u ≠ 0 := by
      intro h0
      have : ev i = 0 := hJinj _ (by rw [← hu, h0])
      rw [this, dotProduct_zero] at hv1
      exact zero_ne_one hv1
    have huu : 0 < u ⬝ᵥ u := by
      rcases (show 0 ≤ u ⬝ᵥ u from Finset.sum_nonneg fun k _ => mul_self_nonneg _).lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hu0
    have hq1 : u ⬝ᵥ (C *ᵥ u) = lam i * (u ⬝ᵥ u) := by
      rw [hCu, dotProduct_smul, smul_eq_mul]
    have hq2 := hquad u
    have hsum1 : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u)) = lam i * (u ⬝ᵥ u) := by
      simp only [hort]
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hbes : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u) + (ev j ⬝ᵥ u) ^ 2) ≤
        ∑ j, lam j * (u ⬝ᵥ u) := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hlam0 j)
      exact bessel2 (ev j) (ev i) u (by rw [hort, if_pos rfl]) hv1 hvu huu
    simp only [mul_add, Finset.sum_add_distrib] at hbes
    rw [hsum1, ← hq2, hq1, ← Finset.sum_mul, ← htr] at hbes
    nlinarith

  have hcore : ∀ w : Fin d → ℝ, w ⬝ᵥ (C *ᵥ w) ≤ trace C / 2 * (w ⬝ᵥ w) := by
    intro w
    rw [hquad, ← hpars, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hlam j) (sq_nonneg _)

  have hx : x ⬝ᵥ (G *ᵥ x) = ((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ (C *ᵥ ((R⁻¹)ᵀ *ᵥ x)) := by
    have e1 : C *ᵥ ((R⁻¹)ᵀ *ᵥ x) = R *ᵥ (G *ᵥ x) := by
      rw [hCdef, Matrix.mulVec_mulVec, Matrix.mul_assoc, hRt, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    rw [e1, Matrix.dotProduct_mulVec ((R⁻¹)ᵀ *ᵥ x) R, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, hRt, Matrix.one_mulVec]
  rw [hx]
  have := hcore ((R⁻¹)ᵀ *ᵥ x)
  rw [hCtr] at this
  linarith

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

theorem whiten_holds : WhitenStatement := by
  intro d L hL
  have hH := hL.isHermitian
  set U : Matrix (Fin d) (Fin d) ℝ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU
  set s : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) with hs
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hsq : s * s = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Real.mul_self_sqrt (hL.eigenvalues_pos i).le]
  refine ⟨s * Uᵀ, ?_, ?_⟩
  · have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    have h1 : (star U).det * U.det = 1 := by
      rw [← Matrix.det_mul, hUU, Matrix.det_one]
    have hdU : IsUnit U.det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h1)
    rw [Matrix.det_mul, Matrix.det_transpose]
    refine IsUnit.mul ?_ hdU
    rw [hs, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact (Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (hL.eigenvalues_pos i)).ne'
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.diagonal_transpose, ← hs,
      Matrix.mul_assoc, ← Matrix.mul_assoc s s, hsq, ← Matrix.mul_assoc, ← hstar]
    exact hspec

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem cc_smul_q {S σ : Type} [CommRing S] {q : MvPowerSeries σ S} (hq : MvPowerSeries.constantCoeff q = 0)
    (r : S) : MvPowerSeries.constantCoeff (r • q) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq, mul_zero]

theorem exp_pow_eq {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) : ∀ k : ℕ,
    PowerSeries.subst q (PowerSeries.exp S) ^ k = PowerSeries.subst ((k : S) • q) (PowerSeries.exp S)
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_smul, exp_zero]
  | k + 1 => by
    rw [pow_succ, exp_pow_eq q hq k, ← exp_add (ha := cc_smul_q hq (k : S)) (hb := hq), Nat.cast_succ, add_smul,
      one_smul]

theorem exp_pow_mul_exp_neg {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) (k : ℕ) :
    PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1 := by
  have hneg : MvPowerSeries.constantCoeff (-((k : S) • q)) = 0 := by
    rw [map_neg, cc_smul_q hq, neg_zero]
  rw [exp_pow_eq q hq k, ← exp_add (cc_smul_q hq _) hneg, add_neg_cancel, exp_zero]

end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

end Sym

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

end Sym

namespace Sym

variable {k : Type} [CommRing k]

private theorem const_subst_lemma {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (g : MvPowerSeries σ k) :
    constantCoeff (subst a g) = constantCoeff g := by
  have hA : HasSubst a := by
    first
      | exact hasSubst_of_constantCoeff_zero ha
      | exact HasSubst.of_constantCoeff_zero' ha
      | exact hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
      | exact HasSubst.of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
  rw [constantCoeff_subst hA, finsum_eq_single _ (0 : σ →₀ ℕ)]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact he (Finsupp.ext fun t => by simpa using hc t)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]
    · simp
    · rw [map_pow, ha s, zero_pow hs]

theorem const_ev {m n d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p q, constantCoeff (a p q) = 0) (g : PS k m d) :
    constantCoeff (ev a g) = constantCoeff g := by
  unfold ev
  exact const_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) g

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPolynomial Formalism.L2.Pj

section Crude

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ)

end Crude

section Germ

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def addF (k : Type) [CommRing k] (d : ℕ) : Fin d → PS k 2 d :=
  fun j => MvPowerSeries.X ((0 : Fin 2), j) + MvPowerSeries.X ((1 : Fin 2), j)

end Germ

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
