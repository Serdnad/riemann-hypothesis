module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.LocalRing.LocalSubring

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PG

open MvPolynomial

variable {D : ℕ}

noncomputable def lineHom (a w : Fin D → ℂ) : MvPolynomial (Fin D) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval fun i => Polynomial.C (a i) + Polynomial.C (w i) * Polynomial.X

theorem eval_lineHom (a w : Fin D → ℂ) (F : MvPolynomial (Fin D) ℂ) (s : ℂ) :
    (lineHom a w F).eval s = eval (fun i => a i + w i * s) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [lineHom]
  | add p q hp hq => rw [map_add (f := _), Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    simp [lineHom]

end ReciprocityTheory.ChartRestriction.G.AR.Up.PG
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix
open scoped ComplexConjugate

noncomputable section

variable {n : ℕ}

private lemma blockTriangular_inv_of_det_ne_zero {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.BlockTriangular id)
    (hd : M.det ≠ 0) : M⁻¹.BlockTriangular id := by
  letI := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM

private lemma eq_of_mul_mul_eq_of_det_ne_zero {P Q X Y : Matrix (Fin n) (Fin n) ℂ} (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (h : P * X * Q = P * Y * Q) : X = Y := by
  have hP' := isUnit_iff_ne_zero.mpr hP
  have hQ' := isUnit_iff_ne_zero.mpr hQ
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z = P⁻¹ * (P * Z * Q) * Q⁻¹ := by
    intro Z
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP', Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]
  calc X = P⁻¹ * (P * X * Q) * Q⁻¹ := e X
    _ = P⁻¹ * (P * Y * Q) * Q⁻¹ := by rw [h]
    _ = Y := (e Y).symm

theorem gram_upper_unique {ε : Fin n → ℂ} (hε : ∀ a, ε a * ε a = 1)
    {β β' : Matrix (Fin n) (Fin n) ℂ} (hβ : β.BlockTriangular id) (hβ' : β'.BlockTriangular id)
    (hd : β.det ≠ 0) (hd' : β'.det ≠ 0)
    (h : β'ᵀ * diagonal ε * β'.map (starRingEnd ℂ) = βᵀ * diagonal ε * β.map (starRingEnd ℂ)) :
    ∃ D : Fin n → ℂ, (∀ a, ‖D a‖ = 1) ∧ β' = diagonal D * β := by
  classical
  have hε0 : ∀ a, ε a ≠ 0 := fun a h0 => by
    have := hε a
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hu := isUnit_iff_ne_zero.mpr hd
  obtain ⟨γ, hγdef⟩ : ∃ γ : Matrix (Fin n) (Fin n) ℂ, γ = β' * β⁻¹ := ⟨_, rfl⟩
  have hγ : γ.BlockTriangular id := hγdef ▸ hβ'.mul (blockTriangular_inv_of_det_ne_zero hβ hd)
  have hγβ : β' = γ * β := by
    rw [hγdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have hγd : γ.det ≠ 0 := by
    intro h0
    apply hd'
    rw [hγβ, Matrix.det_mul, h0, zero_mul]
  have hbar : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := fun M => by
    rw [RingHom.map_det]; rfl

  have key : γᵀ * diagonal ε * γ.map (starRingEnd ℂ) = diagonal ε := by
    apply eq_of_mul_mul_eq_of_det_ne_zero (P := βᵀ) (Q := β.map (starRingEnd ℂ))
    · rwa [Matrix.det_transpose]
    · rw [hbar]; exact (map_ne_zero _).mpr hd
    · rw [← h, hγβ, Matrix.transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
  have hγinv := blockTriangular_inv_of_det_ne_zero hγ hγd
  have hγtu : IsUnit γᵀ.det := by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hγd

  have key2 : diagonal ε * γ.map (starRingEnd ℂ) = (γ⁻¹)ᵀ * diagonal ε := by
    rw [Matrix.transpose_nonsing_inv]
    conv_rhs => rw [← key]
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγtu, Matrix.one_mul]
  have hoff : ∀ i j, i ≠ j → γ i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have e := congrFun (congrFun key2 i) j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hγinv hlt, zero_mul,
        Matrix.map_apply] at e
      exact (map_eq_zero _).mp ((mul_eq_zero.mp e).resolve_left (hε0 i))
    · exact hγ hlt
  have hγdiag : γ = diagonal (fun a => γ a a) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  refine ⟨fun a => γ a a, fun a => ?_, by rw [← hγdiag]; exact hγβ⟩
  have e := congrFun (congrFun key a) a
  rw [hγdiag] at e
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at e
  have h2 : γ a a * starRingEnd ℂ (γ a a) = 1 := by
    have : ε a * (γ a a * starRingEnd ℂ (γ a a)) = ε a * 1 := by linear_combination e
    exact mul_left_cancel₀ (hε0 a) this
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖γ a a‖ ^ 2 = 1 := by exact_mod_cast h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h3

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

theorem amgm {k x y : ℝ} (hk : 0 < k) : x * y ≤ (x ^ 2 / k + k * y ^ 2) / 2 := by
  have h : 0 ≤ (x - k * y) ^ 2 / k := by positivity
  have e : (x - k * y) ^ 2 / k = x ^ 2 / k - 2 * (x * y) + k * y ^ 2 := by
    field_simp
    ring
  linarith

theorem I_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : α → ℝ} {g u : α → ℂ}
    {w : α → ℝ≥0∞} {q : ℝ} (hk : ∀ᵐ a ∂μ, 0 < k a) (hw : ∀ᵐ a ∂μ, w a < ⊤) (hq1 : q < 1)
    (hq0 : 0 ≤ q) (hkm : AEMeasurable k μ) (hgm : AEMeasurable g μ) (hum : AEMeasurable u μ)
    (hwm : AEMeasurable w μ)
    (hI : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ < ⊤)
    (hJ : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ ≤
      ENNReal.ofReal q * ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ)
    (h0 : ∫ a, ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ) ∂μ = 0) :
    ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ = 0 := by
  have hWm : AEMeasurable (fun a => (w a).toReal) μ := hwm.ennreal_toReal
  have hF1m : AEMeasurable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    (hkm.mul (hgm.norm.pow_const 2)).mul hWm
  have hF2m : AEMeasurable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ((hum.norm.pow_const 2).div hkm).mul hWm
  have hF1nn : 0 ≤ᵐ[μ] fun a => k a * ‖g a‖ ^ 2 * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) ENNReal.toReal_nonneg
  have hF2nn : 0 ≤ᵐ[μ] fun a => ‖u a‖ ^ 2 / k a * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (div_nonneg (sq_nonneg _) ha.le) ENNReal.toReal_nonneg
  have hA : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (mul_nonneg ha.le (sq_nonneg _)), ENNReal.ofReal_toReal hwa.ne]
  have hB : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) ha.le), ENNReal.ofReal_toReal hwa.ne]
  rw [hA] at hI hJ ⊢
  rw [hB] at hJ
  have hJfin : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ < ⊤ :=
    lt_of_le_of_lt hJ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)
  have hF1i : Integrable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    ⟨hF1m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF1nn).2 hI⟩
  have hF2i : Integrable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ⟨hF2m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF2nn).2 hJfin⟩
  have hint1 : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF1nn hF1m.aestronglyMeasurable
  have hint2 : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF2nn hF2m.aestronglyMeasurable
  have hPm : AEStronglyMeasurable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    ((hum.mul (Complex.continuous_conj.measurable.comp_aemeasurable hgm)).mul
      (Complex.measurable_ofReal.comp_aemeasurable hWm)).aestronglyMeasurable
  have hPbd : ∀ᵐ a ∂μ, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ≤
      (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 := by
    filter_upwards [hk] with a ha
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    have h1 := amgm (k := k a) (x := ‖u a‖) (y := ‖g a‖) ha
    have hW0 : 0 ≤ (w a).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right h1 hW0]
  have hbdi : Integrable (fun a => (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2) μ :=
    (hF2i.add hF1i).div_const 2
  have hPi : Integrable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    Integrable.mono' hbdi hPm hPbd
  have hF1c : Integrable (fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ)) μ := hF1i.ofReal
  have hsplit : (fun a => ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ)) =
      fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ) - u a * conj (g a) * ((w a).toReal : ℂ) := by
    funext a
    rw [sub_mul, sub_mul, mul_assoc (k a : ℂ) (g a) (conj (g a)), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hsplit, integral_sub hF1c hPi, integral_complex_ofReal, sub_eq_zero] at h0
  have hn : 0 ≤ ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := integral_nonneg_of_ae hF1nn
  have hle : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ ≤
      ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
    calc ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ
        = ‖((∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hn]
      _ = ‖∫ a, u a * conj (g a) * ((w a).toReal : ℂ) ∂μ‖ := by rw [h0]
      _ ≤ ∫ a, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ a, (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 ∂μ :=
          integral_mono_ae hPi.norm hbdi hPbd
      _ = ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
          rw [integral_div, integral_add hF2i hF1i]
  have hJr : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ ≤ q * ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := by
    rw [hint1, hint2]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hJ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0] at this
  have hz : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq1.le) hn]
  rw [hint1] at hz
  exact ((ENNReal.toReal_eq_zero_iff _).1 hz).resolve_right hI.ne

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

noncomputable section

section Cone

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

def cone (a : ι → E) : MvPolynomial ι R →ₐ[R] Polynomial E :=
  aeval fun i => Polynomial.C (a i) * Polynomial.X

theorem cone_homog (a : ι → E) {f : MvPolynomial ι R} {d : ℕ} (hf : f.IsHomogeneous d) :
    cone a f = Polynomial.monomial d (aeval a f) := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have hp : (m.prod fun i k => (Polynomial.C (a i) * Polynomial.X) ^ k) =
      Polynomial.C (m.prod fun i k => a i ^ k) * Polynomial.X ^ d := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
      Finset.prod_pow_eq_pow_sum, hd]
  rw [cone, aeval_monomial, aeval_monomial, hp, Polynomial.algebraMap_apply, ← mul_assoc,
    ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_cone (a : ι → E) (f : MvPolynomial ι R) (n : ℕ) :
    (cone a f).coeff n = aeval a (homogeneousComponent n f) := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent f]

  rw [map_sum, Polynomial.finsetSum_coeff]
  simp_rw [cone_homog a (homogeneousComponent_isHomogeneous _ f), Polynomial.coeff_monomial_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp at h; omega), map_zero]

theorem aeval_mul_homog (q : ι → E) (t : E) {G : MvPolynomial ι R} {m : ℕ} (hG : G.IsHomogeneous m) :
    aeval (fun i => q i * t) G = t ^ m * aeval q G := by
  have h := congrArg ((Polynomial.aeval t : Polynomial E →ₐ[E] E).restrictScalars R)
    (cone_homog (R := R) q hG)
  rw [cone, MvPolynomial.comp_aeval_apply] at h
  simp only [AlgHom.restrictScalars_apply, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Polynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h, mul_comm]

theorem eval_mul_homog {K : Type*} [CommRing K] (q : ι → K) (t : K) {G : MvPolynomial ι K} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => q i * t) G = t ^ m * eval q G := by
  simpa using aeval_mul_homog (R := K) q t hG

end Cone

open MvPolynomial in
theorem exists_cons_one_ne {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    {G : MvPolynomial (Fin (n + 1)) K} (hG : G.IsHomogeneous m) (h0 : G ≠ 0) :
    ∃ c : Fin n → K, eval (Fin.cons 1 c) G ≠ 0 := by
  by_contra! h
  apply h0
  have hX : (X 0 * G : MvPolynomial (Fin (n + 1)) K) = 0 := by
    apply MvPolynomial.funext
    intro p
    rw [map_mul, eval_X, map_zero]
    by_cases hp : p 0 = 0
    · rw [hp, zero_mul]
    · have hq : p = fun i => (Fin.cons 1 (fun k => p k.succ / p 0) : Fin (n + 1) → K) i * p 0 := by
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp
        · simp [div_mul_cancel₀ _ hp]
      have : eval p G = 0 := by
        rw [hq]
        rw [eval_mul_homog _ _ hG, h, mul_zero]
      rw [this, mul_zero]
  exact (mul_eq_zero.mp hX).resolve_left (X_ne_zero _)

section Int

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

end Int

section Homog

open Polynomial

theorem prod_pow_natDegree_coeff' {B : Type*} [CommRing B] {ι : Type*} (s : Finset ι)
    (v : ι → B[X]) (d : ι → ℕ) (hv : ∀ i, (v i).natDegree ≤ 1) :
    (∏ i ∈ s, v i ^ d i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, v i ^ d i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (v i).coeff 1 ^ d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨hDegree, hCoeff⟩ := ih
    have haDegree : (v a ^ d a).natDegree ≤ d a := by
      simpa using natDegree_pow_le_of_le (d a) (hv a)
    have haCoeff : (v a ^ d a).coeff (d a) = (v a).coeff 1 ^ d a := by
      simpa using coeff_pow_of_natDegree_le (m := d a) (hv a)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨natDegree_mul_le.trans (add_le_add haDegree hDegree), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le haDegree hDegree, haCoeff, hCoeff]

end Homog

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd

theorem exists_val_of_prime {Kf : Type*} [Field Kf] (A : Subring Kf) (P : Ideal A) [P.IsPrime] :
    ∃ V : ValuationSubring Kf, (∀ a : A, (a : Kf) ∈ V) ∧ (∀ a : A, a ∉ P → (a : Kf)⁻¹ ∈ V) ∧
      ∀ a : A, a ∈ P → V.valuation (a : Kf) < 1 := by
  obtain ⟨B, hB⟩ := (LocalSubring.ofPrime A P).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hB
  let e := LocalSubring.ofPrimeEquiv A P
  let f : Localization.AtPrime P →+* B.toLocalSubring.toSubring :=
    (Subring.inclusion hle).comp (e : Localization.AtPrime P →+* (LocalSubring.ofPrime A P).toSubring)
  have hf : ∀ a : A, ((f (algebraMap A (Localization.AtPrime P) a) : B.toLocalSubring.toSubring) : Kf) = a := by
    intro a
    show ((e (algebraMap A (Localization.AtPrime P) a) : (LocalSubring.ofPrime A P).toSubring) : Kf) = a
    rw [AlgEquiv.commutes]
    rfl
  have hmem : ∀ a : A, (a : Kf) ∈ B := by
    intro a
    have h := (f (algebraMap A (Localization.AtPrime P) a)).2
    rw [hf] at h
    exact h
  refine ⟨B, hmem, fun a ha => ?_, fun a ha => ?_⟩
  · have hu : IsUnit (algebraMap A (Localization.AtPrime P) a) :=
      IsLocalization.map_units _ (⟨a, ha⟩ : P.primeCompl)
    obtain ⟨u, hu'⟩ := hu.map f
    have h1 : ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) * (u : _) = 1 :=
      u.inv_mul
    have h2 : (((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) : Kf) * (a : Kf) = 1 := by
      rw [← hf a, ← hu']
      exact congrArg Subtype.val h1
    rw [← eq_inv_of_mul_eq_one_left h2]
    exact ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring).2
  · have hnu : ¬ IsUnit (algebraMap A (Localization.AtPrime P) a) := fun h =>
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P a).1 h ha
    have hnu2 : ¬ IsUnit (f (algebraMap A (Localization.AtPrime P) a)) := by
      intro h
      apply hnu
      have h' : IsUnit (e (algebraMap A (Localization.AtPrime P) a)) := hloc.map_nonunit _ h
      have h'' := h'.map (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
      first
      | (convert h'' using 1
         exact (e.symm_apply_apply _).symm)
      | (rwa [show (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
            (e (algebraMap A (Localization.AtPrime P) a)) = algebraMap A (Localization.AtPrime P) a from
            e.symm_apply_apply _] at h'')
    by_contra hge
    push_neg at hge
    have hv1 : B.valuation (a : Kf) = 1 := le_antisymm ((B.valuation_le_one_iff _).2 (hmem a)) hge
    have hunit : IsUnit (⟨a, hmem a⟩ : B) := (B.valuation_eq_one_iff ⟨a, hmem a⟩).2 hv1
    apply hnu2
    have heq : f (algebraMap A (Localization.AtPrime P) a) = ⟨a, hmem a⟩ := Subtype.ext (hf a)
    rw [heq]
    exact hunit

end ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd
end
