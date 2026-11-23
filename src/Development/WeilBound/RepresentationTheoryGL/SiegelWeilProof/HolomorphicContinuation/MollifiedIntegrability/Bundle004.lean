module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle001
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR.I

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm, star_add, star_div₀, star_mul', Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem normSq_herm (y : E n) (i j : Fin n) :
    Complex.normSq (herm y i j) = (y i j ^ 2 + y j i ^ 2) / 2 := by
  simp only [herm, Complex.normSq_apply]
  simp
  ring

theorem sum_normSq_herm (y : E n) :
    ∑ i, ∑ j, Complex.normSq (herm y i j) = ∑ a, ∑ b, y a b ^ 2 := by
  simp_rw [normSq_herm, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => y j i ^ 2)]
  ring

theorem one_add_sum_le_prod (s : Finset (Fin n)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have h0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
    nlinarith [ha j]

theorem dP_eq_prod (y : E n) :
    dP y = ∏ i, (1 + (herm_isHermitian y).eigenvalues i ^ 2) ∧
      ∑ a, ∑ b, y a b ^ 2 = ∑ i, (herm_isHermitian y).eigenvalues i ^ 2 := by
  set hA := herm_isHermitian y
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hUs : star U * U = 1 := Unitary.coe_star_mul_self _
  have hsU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : herm y = U * D * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hsq : 1 + herm y * herm y = U * (1 + D * D) * star U := by
    rw [hspec]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    rw [hsU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
  have hDD : 1 + D * D = diagonal fun i => ((1 + hA.eigenvalues i ^ 2 : ℝ) : ℂ) := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]
    congr 1
    funext i
    simp [pow_two]
  have hdetU : U.det * (star U).det = 1 := by rw [← det_mul, hsU, det_one]
  constructor
  · unfold dP
    rw [hsq, det_mul, det_mul, hDD, det_diagonal]
    rw [mul_comm U.det, mul_assoc, hdetU, mul_one, ← Complex.ofReal_prod, Complex.ofReal_re]
  · have hsq2 : herm y * herm y = U * (D * D) * star U := by
      rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
    have htr : (herm y * herm y).trace = ∑ i, ((hA.eigenvalues i ^ 2 : ℝ) : ℂ) := by
      rw [hsq2, trace_mul_comm, ← Matrix.mul_assoc, hUs, Matrix.one_mul, hD, diagonal_mul_diagonal, trace_diagonal]
      simp [pow_two]
    have hre : (herm y * herm y).trace.re = ∑ i, ∑ j, Complex.normSq (herm y i j) := by
      rw [trace]
      simp only [diag_apply, Matrix.mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hji : herm y j i = star (herm y i j) := by
        have := congrFun (congrFun hA.eq j) i
        rw [conjTranspose_apply] at this
        exact this.symm
      rw [hji, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    rw [← sum_normSq_herm, ← hre, htr, Complex.re_sum]
    simp only [Complex.ofReal_re]

theorem dP_ge (y : E n) : 1 + ∑ a, ∑ b, y a b ^ 2 ≤ dP y := by
  obtain ⟨h1, h2⟩ := dP_eq_prod y
  rw [h1, h2]
  exact one_add_sum_le_prod _ _ fun i => sq_nonneg _

theorem dP_pos (y : E n) : 0 < dP y := by
  have h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  linarith [dP_ge y]

theorem continuous_herm : Continuous (herm : E n → Matrix (Fin n) (Fin n) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold herm
  fun_prop

theorem continuous_dP : Continuous (dP : E n → ℝ) := by
  unfold dP
  have : Continuous fun y : E n => 1 + herm y * herm y := continuous_const.add (continuous_herm.matrix_mul continuous_herm)
  exact Complex.continuous_re.comp this.matrix_det

theorem norm_sq_le_sum (y : E n) : ‖y‖ ^ 2 ≤ ∑ a, ∑ b, y a b ^ 2 := by
  have h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hle : ‖y‖ ≤ Real.sqrt (∑ a, ∑ b, y a b ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    calc y a b ^ 2 ≤ ∑ b', y a b' ^ 2 := Finset.single_le_sum (fun b' _ => sq_nonneg (y a b')) (Finset.mem_univ b)
      _ ≤ ∑ a', ∑ b', y a' b' ^ 2 :=
        Finset.single_le_sum (f := fun a' => ∑ b', y a' b' ^ 2) (fun a' _ => Finset.sum_nonneg fun b' _ => sq_nonneg _)
          (Finset.mem_univ a)
  calc ‖y‖ ^ 2 ≤ Real.sqrt (∑ a, ∑ b, y a b ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := Real.sq_sqrt h0

theorem integr : Integr := by
  intro n
  refine ⟨⟨1, one_pos, fun y => by simpa using dP_ge y⟩, fun σ hσ => ?_⟩
  have hfin : (Module.finrank ℝ (E n) : ℝ) = (n : ℝ) ^ 2 := by
    have h : Module.finrank ℝ (Fin n → Fin n → ℝ) = n * n := by
      rw [Module.finrank_pi_fintype]
      simp
    change ((Module.finrank ℝ (Fin n → Fin n → ℝ) : ℕ) : ℝ) = (n : ℝ) ^ 2
    rw [h]
    push_cast
    ring
  have hr : (Module.finrank ℝ (E n) : ℝ) < 2 * σ := by rw [hfin]; linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (E n))) hr
  have hσ0 : 0 ≤ σ := by nlinarith [sq_nonneg (n : ℝ)]
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (continuous_dP.rpow_const fun y => Or.inl (dP_pos y).ne').aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dP_pos y).le _)]
    have h1 : 1 + ‖y‖ ^ 2 ≤ dP y := by linarith [norm_sq_le_sum y, dP_ge y]
    have h2 : 0 < 1 + ‖y‖ ^ 2 := by positivity
    rw [show -(2 * σ) / 2 = -σ by ring]
    exact Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)

end PositivityTheory.Rg.Sw.WR.I
end
end

section

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G.GI

open PositivityTheory.Rg.Sw

lemma abs_pow_exp (b : ℝ) (hb : 0 < b) (k : ℕ) :
    Integrable fun x : ℝ => |x| ^ k * Real.exp (-b * x ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ))
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  simp_rw [Real.rpow_natCast] at h
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) : (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ k ≤ (2 * b) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * b ^ k := mul_pow 2 b k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg ha k
          gcongr; linarith
  · calc (a + b) ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * a ^ k := mul_pow 2 a k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg hb k
          gcongr; linarith

lemma cplx (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Integrable fun z : ℂ => ‖z‖ ^ k * Real.exp (-c * ‖z‖ ^ 2) := by
  have hP : Integrable (fun p : ℝ × ℝ => (2 : ℝ) ^ k * ((|p.1| ^ k * Real.exp (-c * p.1 ^ 2)) *
      Real.exp (-c * p.2 ^ 2) + Real.exp (-c * p.1 ^ 2) * (|p.2| ^ k * Real.exp (-c * p.2 ^ 2)))) := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact (abs_pow_exp c hc k).mul_prod (integrable_exp_neg_mul_sq hc)
    · exact (integrable_exp_neg_mul_sq hc).mul_prod (abs_pow_exp c hc k)
  have hC : Integrable (fun z : ℂ => (2 : ℝ) ^ k * ((|z.re| ^ k * Real.exp (-c * z.re ^ 2)) *
      Real.exp (-c * z.im ^ 2) + Real.exp (-c * z.re ^ 2) * (|z.im| ^ k * Real.exp (-c * z.im ^ 2)))) := by
    have := (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hP
    simpa [Function.comp_def, Complex.measurableEquivRealProd] using this
  refine hC.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have he : Real.exp (-c * ‖z‖ ^ 2) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2) := by
    rw [hz, ← Real.exp_add]; ring_nf
  have h1 : ‖z‖ ^ k ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) :=
    (pow_le_pow_left₀ (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z) k).trans
      (add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) k)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), he]
  have e1 := Real.exp_pos (-c * z.re ^ 2)
  have e2 := Real.exp_pos (-c * z.im ^ 2)
  calc ‖z‖ ^ k * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2))
      ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)) := by
        gcongr
    _ = _ := by ring

lemma prodG (m n : ℕ) (c : ℝ) (hc : 0 < c) (D : Fin m → Fin n → ℕ) :
    Integrable fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, (‖x a i‖ ^ D a i * Real.exp (-c * ‖x a i‖ ^ 2)) := by
  refine Integrable.fintype_prod (f := fun a (r : Fin n → ℂ) => ∏ i, (‖r i‖ ^ D a i * Real.exp (-c * ‖r i‖ ^ 2)))
    (μ := fun _ => volume) (fun a => ?_)
  exact Integrable.fintype_prod (f := fun i (z : ℂ) => ‖z‖ ^ D a i * Real.exp (-c * ‖z‖ ^ 2))
    (μ := fun _ => volume) (fun i => cplx c hc _)

abbrev fx {m n : ℕ} (x : Fin m → Fin n → ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

lemma continuous_evX {m n : ℕ} (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  have : Continuous fun x : Fin m → Fin n → ℂ => fx x := by
    refine continuous_pi fun k => ?_
    by_cases h : k.2.2
    · simp only [fx, h, if_true]; fun_prop
    · simp only [fx, h, if_false, Bool.false_eq_true]; fun_prop
  exact (MvPolynomial.continuous_eval P).comp this

lemma continuous_gs {m n : ℕ} (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  unfold gs; fun_prop

lemma norm_gs {m n : ℕ} (c : ℝ) (x : Fin m → Fin n → ℂ) :
    ‖gs c x‖ = ∏ a, ∏ i, Real.exp (-c * ‖x a i‖ ^ 2) := by
  unfold gs
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  have : -(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) = ∑ a, ∑ i, (-c * ‖x a i‖ ^ 2) := by
    simp [Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
  rw [this, Real.exp_sum]
  exact Finset.prod_congr rfl fun a _ => Real.exp_sum _ _

lemma norm_mono {m n : ℕ} (d : (Fin m × Fin n × Bool) →₀ ℕ) (x : Fin m → Fin n → ℂ) :
    ‖evX (monomial d 1) x‖ = ∏ a, ∏ i, ‖x a i‖ ^ (d (a, i, false) + d (a, i, true)) := by
  unfold evX
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, norm_prod]
  simp_rw [norm_pow]
  rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
    simp [Finsupp.notMem_support_iff.mp hk])]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  simp [pow_add, mul_comm]

theorem integP : IntegP := by
  intro m n c hc P
  have key : ∀ d : (Fin m × Fin n × Bool) →₀ ℕ,
      Integrable fun x : Fin m → Fin n → ℂ => evX (monomial d 1) x * gs c x := by
    intro d
    refine (prodG m n c hc (fun a i => d (a, i, false) + d (a, i, true))).mono'
      ((continuous_evX _).mul (continuous_gs c)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    rw [norm_mul, norm_mono, norm_gs, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_mul_distrib]
  have hP : (fun x => evX P x * gs c x) =
      fun x => ∑ d ∈ P.support, AddMonoidAlgebra.coeff P d * (evX (monomial d 1) x * gs c x) := by
    funext x
    simp only [evX]
    rw [MvPolynomial.eval_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, mul_assoc]
  rw [hP]
  exact integrable_finsetSum _ fun d _ => (key d).const_mul _

end PositivityTheory.Rg.Sw.WR.G.GI
end
end
