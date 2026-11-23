module

public import ReciprocityTheory.SemistableReduction.Bundle008
public import Mathlib.Algebra.MvPolynomial.Funext
public import ReciprocityTheory.SemistableReduction.Bundle010
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle057
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tmLog (f : MvPolynomial ι ℂ) (θ : ι → ℝ) : ℝ := Real.log ‖MvPolynomial.eval (torusPoint θ) f‖

lemma measurable_tmLog (f : MvPolynomial ι ℂ) : Measurable (tmLog f) := measurable_logEval f

lemma tmLog_update (f : MvPolynomial ι ℂ) (θ : ι → ℝ) (i : ι) (t : ℝ) :
    tmLog f (update θ i t) = Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖ := by
  rw [tmLog, torusPoint_update, tm_eval_update]

lemma tmLog_le (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    tmLog f θ ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := by
  unfold tmLog
  rcases eq_or_ne ‖MvPolynomial.eval (torusPoint θ) f‖ 0 with h | h
  · rw [h, Real.log_zero]; exact posLog_nonneg
  · exact (Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
      (norm_eval_torus_le f θ)).trans (le_max_right _ _)

lemma coeffIn_eq_zero_of_lt (i : ι) (f : MvPolynomial ι ℂ) (k : ℕ)
    (hk : f.support.sup (fun s => s i) < k) : coeffIn i k f = 0 := by
  unfold coeffIn
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro s hs hsk
  have := Finset.le_sup (f := fun s : ι →₀ ℕ => s i) hs
  omega

lemma exists_coeffIn_ne_zero (i : ι) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∃ k, coeffIn i k f ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hf
  apply MvPolynomial.funext
  intro x
  have hs : tmSlice i x f = 0 := by
    ext k
    rw [tmSlice_coeff, h k]
    simp
  rw [← update_eq_self i x, tm_eval_update, hs]
  simp

lemma exists_top_coeffIn (i : ι) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∃ d, coeffIn i d f ≠ 0 ∧ ∀ k, d < k → coeffIn i k f = 0 := by
  classical
  set T := (Finset.range (f.support.sup (fun s => s i) + 1)).filter (fun k => coeffIn i k f ≠ 0)
  have hT : T.Nonempty := by
    obtain ⟨k, hk⟩ := exists_coeffIn_ne_zero i f hf
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hk⟩⟩
    by_contra hlt
    exact hk (coeffIn_eq_zero_of_lt i f k (by omega))
  refine ⟨T.max' hT, (Finset.mem_filter.mp (T.max'_mem hT)).2, fun k hk => ?_⟩
  by_contra hne
  by_cases hkN : k < f.support.sup (fun s => s i) + 1
  · have : k ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkN, hne⟩
    exact absurd (T.le_max' k this) (by omega)
  · exact hne (coeffIn_eq_zero_of_lt i f k (by omega))

lemma eval_const_of_vars_empty (f : MvPolynomial ι ℂ) (hf : f.vars ⊆ ∅) (x : ι → ℂ) :
    MvPolynomial.eval x f = MvPolynomial.constantCoeff f := by
  have := MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars (RingHom.id ℂ) (g := x) (p := f)
    (fun i hi => absurd (hf hi) (by simp))
  simpa using this

lemma measurableSet_zeroTorus (f : MvPolynomial ι ℂ) :
    MeasurableSet {θ : ι → ℝ | MvPolynomial.eval (torusPoint θ) f = 0} :=
  (continuous_eval_torus f).measurable (measurableSet_singleton 0)

lemma torus_zero_set_measure_zero (S : Finset ι) : ∀ f : MvPolynomial ι ℂ, f.vars ⊆ S → f ≠ 0 →
    torusProb ι {θ | MvPolynomial.eval (torusPoint θ) f = 0} = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hS hf
    have hc : MvPolynomial.constantCoeff f ≠ 0 := by
      intro h0
      apply hf
      apply MvPolynomial.funext
      intro x
      rw [eval_const_of_vars_empty f hS, h0]
      simp
    have : {θ : ι → ℝ | MvPolynomial.eval (torusPoint θ) f = 0} = ∅ := by
      ext θ
      simp [eval_const_of_vars_empty f hS, hc]
    rw [this, measure_empty]
  | insert i S' hi ih =>
    intro f hS hf
    obtain ⟨d, hd, htop⟩ := exists_top_coeffIn i f hf
    have hg : torusProb ι {θ | MvPolynomial.eval (torusPoint θ) (coeffIn i d f) = 0} = 0 := by
      apply ih _ _ hd
      intro j hj
      have h1 := vars_coeffIn_subset i d f hj
      rw [Finset.mem_erase] at h1
      have h2 := hS h1.2
      rw [Finset.mem_insert] at h2
      exact h2.resolve_left h1.1
    apply tm_measure_null i (measurableSet_zeroTorus f)
    have hae : ∀ᵐ θ ∂(torusProb ι), MvPolynomial.eval (torusPoint θ) (coeffIn i d f) ≠ 0 := by
      rw [ae_iff]; simpa using hg
    filter_upwards [hae] with θ hθ
    have hp : tmSlice i (torusPoint θ) f ≠ 0 := by
      intro h0
      apply hθ
      rw [← tmSlice_coeff, h0, Polynomial.coeff_zero]
    have := zero_set_circ_null _ hp
    convert this using 3 with t
    simp only [torusPoint_update, tm_eval_update]

lemma tm_null (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    torusProb ι {θ | MvPolynomial.eval (torusPoint θ) f = 0} = 0 :=
  torus_zero_set_measure_zero Finset.univ f (Finset.subset_univ _) hf

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def colMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a i => σ (b i a)

theorem gramC_eq_colMat {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (colMat σ b)ᴴ * H * colMat σ b := by
  ext i j
  simp only [gramC, colMat, embVec, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem colMat_comb {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (N : Matrix (Fin k) (Fin k) K) :
    colMat σ (fun j => ∑ i, N i j • b i) = colMat σ b * N.map σ := by
  ext a j

  simp only [colMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply,
  Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem gramC_comb {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (N : Matrix (Fin k) (Fin k) K) :
    gramC H σ (fun j => ∑ i, N i j • b i) = (N.map σ)ᴴ * gramC H σ b * N.map σ := by
  rw [gramC_eq_colMat, gramC_eq_colMat, colMat_comb, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem det_gramC_comb {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (N : Matrix (Fin k) (Fin k) K) :
    (gramC H σ (fun j => ∑ i, N i j • b i)).det =
      ((Complex.normSq (σ N.det) : ℝ) : ℂ) * (gramC H σ b).det := by
  rw [gramC_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have h : (N.map σ).det = σ N.det := (RingHom.map_det σ N).symm
  rw [h, ← Complex.mul_conj]
  simp only [starRingEnd_apply]
  ring

theorem colMat_mulVec_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) :
    Function.Injective (colMat σ b).mulVec := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin r) (Fin k) K, B = Matrix.of fun a i => b i a := ⟨_, rfl⟩
  have hker : LinearMap.ker B.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∑ i, g i • b i = 0 := by
      funext a
      have h1 := congrFun hg a
      simp only [hB, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Pi.zero_apply] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    funext i
    exact Fintype.linearIndependent_iff.mp hb g h0 i
  obtain ⟨L, hL⟩ := B.mulVecLin.exists_leftInverse_of_injective hker
  have hLB : LinearMap.toMatrix' L * B = 1 := by
    have h2 := congrArg LinearMap.toMatrix' hL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h2
    have h4 : LinearMap.toMatrix' B.mulVecLin = B := LinearMap.toMatrix'_toLin' B
    rwa [h4] at h2
  have hc : colMat σ b = B.map σ := by
    ext a i
    rw [hB]
    rfl
  intro v w hvw
  have h3 : ((LinearMap.toMatrix' L).map σ * colMat σ b).mulVec v =
      ((LinearMap.toMatrix' L).map σ * colMat σ b).mulVec w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvw]
  rwa [hc, ← Matrix.map_mul, hLB, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.one_mulVec,
    Matrix.one_mulVec] at h3

theorem gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hH : H.PosDef) (hb : LinearIndependent K b) : (gramC H σ b).PosDef := by
  rw [gramC_eq_colMat]
  exact hH.conjTranspose_mul_mul_same (colMat_mulVec_injective σ b hb)

theorem gramC_det_re_pos {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hH : H.PosDef) (hb : LinearIndependent K b) : 0 < (gramC H σ b).det.re := by
  classical
  exact (Complex.pos_iff.mp (gramC_posDef H σ b hH hb).det_pos).1

theorem sum_log_normSq {K : Type} [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) =
      2 * Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have hprod : (∏ σ : K →+* ℂ, σ x) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
    have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
    have h2 : algebraMap ℚ ℂ (Algebra.norm ℚ x) = ((Algebra.norm ℚ x : ℚ) : ℂ) := eq_ratCast _ _
    rw [h2] at h1
    rw [h1]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  have hne : ∀ σ : K →+* ℂ, Complex.normSq (σ x) ≠ 0 := fun σ => by
    rw [Ne, Complex.normSq_eq_zero]
    exact (map_ne_zero σ).mpr hx
  have hN : ((Algebra.norm ℚ x : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  rw [← Real.log_prod (s := Finset.univ) (f := fun σ : K →+* ℂ => Complex.normSq (σ x)) (fun σ _ => hne σ),
    ← map_prod Complex.normSq (fun σ : K →+* ℂ => σ x) Finset.univ, hprod,
    ← Complex.ofReal_ratCast, Complex.normSq_ofReal, Real.log_mul hN hN,
    ← Real.log_abs ((Algebra.norm ℚ x : ℚ) : ℝ)]
  ring

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DegAdd

open Matrix NumberField
open scoped ComplexOrder

def embMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (v : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a j => σ (v j a)

theorem gramC_eq_mul {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (v : Fin k → Fin r → K) :
    gramC H σ v = (embMat σ v)ᴴ * H * embMat σ v := by
  ext i j
  simp only [gramC, embMat, embVec, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

theorem embMat_mulVec_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    {v : Fin k → Fin r → K} (hv : LinearIndependent K v) :
    Function.Injective (embMat σ v).mulVec := by
  set B : Matrix (Fin r) (Fin k) K := Matrix.of fun a j => v j a
  have hcol : B.col = v := by
    funext j a
    rfl
  have hB : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hv
  have hker : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact hB (by simpa [Matrix.toLin'_apply] using h)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) hker
  have hNB : LinearMap.toMatrix' g * B = 1 := by
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hE : embMat σ v = B.map σ := rfl
  have h1 : (LinearMap.toMatrix' g).map σ * embMat σ v = 1 := by
    rw [hE, ← Matrix.map_mul, hNB, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have h := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, h1] using h

theorem gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) {v : Fin k → Fin r → K} (hH : H.PosDef)
    (hv : LinearIndependent K v) : (gramC H σ v).PosDef := by
  rw [gramC_eq_mul]
  exact hH.conjTranspose_mul_mul_same (embMat_mulVec_injective σ hv)

theorem gramC_append_blocks {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) :
    (gramC H σ (Fin.append b c)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (gramC H σ b) (gramX H σ b c) (gramX H σ c b) (gramC H σ c) := by
  ext (i | i) (j | j) <;> simp [gramC, gramX]

theorem log_det_gram_append {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) (hH : H.PosDef) (hb : LinearIndependent K b)
    (h : LinearIndependent K (Fin.append b c)) :
    Real.log (gramC H σ (Fin.append b c)).det.re =
      Real.log (gramC H σ b).det.re + Real.log (quotGramC H σ b c).det.re := by
  have hG := (gramC_posDef H σ hH h).det_pos
  have hGb := (gramC_posDef H σ hH hb).det_pos
  have : Invertible (gramC H σ b) := (gramC_posDef H σ hH hb).isUnit.invertible
  have hdet : (gramC H σ (Fin.append b c)).det =
      (gramC H σ b).det * (quotGramC H σ b c).det := by
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv (gramC H σ (Fin.append b c)),
      gramC_append_blocks, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    rfl
  rw [hdet] at hG ⊢
  rw [Complex.pos_iff] at hG hGb
  have hre : ((gramC H σ b).det * (quotGramC H σ b c).det).re =
      (gramC H σ b).det.re * (quotGramC H σ b c).det.re := by
    simp [Complex.mul_re, ← hGb.2]
  have hy : 0 < (quotGramC H σ b c).det.re := by
    rw [hre] at hG
    exact (pos_iff_pos_of_mul_pos hG.1).mp hGb.1
  rw [hre, Real.log_mul hGb.1.ne' hy.ne']

end DegAdd

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def wittMat {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j =>
    if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
    else if i = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0

def WittBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r), S.G.det ≠ 0 →
    ∃ (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K), P.det ≠ 0 ∧ 2 * m ≤ r ∧
      (P.map S.c)ᵀ * S.G * P = wittMat r m g ∧
      ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
        ∑ i, S.c (t i) * g i * t i = 0 → t = 0

def spanIdx {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℕ :=
  (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup

def hGram {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => S.h (b i) (b j)

def LatDegBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b b' : Fin k → Fin r → K),
    (∀ σ, (H σ).PosDef) → B.FG → IsKBasisIn B b → IsKBasisIn B b' →
    latDeg H B b = latDeg H B b'

def IntegralIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (S : HermForm K r)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K),
    B.FG → IsKBasisIn B b → IsIntegralOn S B → (hGram S b).det ≠ 0 →
    ((spanIdx B b : ℕ) : ℝ) ^ 2 ≤ |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)|

def SelfDualIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin r → Fin r → K),
    IsLattice L → IsSelfDual S L → IsKBasisIn L b →
    |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| ≤ ((spanIdx L b : ℕ) : ℝ) ^ 2

def cutSub (K : Type) [Field K] [NumberField K] (r e : ℕ) : Submodule (𝓞 K) (Fin r → K) := UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub K r e

def projGe (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if e ≤ (i : ℕ) then x i else 0
  map_add' x y := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]

def diagMet {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ) :
    (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ :=
  fun σ => Matrix.diagonal fun i => ((δ σ i : ℝ) : ℂ)

def GradedExtStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r e k k₀ k₁ : ℕ) (δ : (K →+* ℂ) → Fin r → ℝ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (b₀ : Fin k₀ → Fin r → K)
    (b₁ : Fin k₁ → Fin r → K),
    (∀ σ i, 0 < δ σ i) → B.FG → IsKBasisIn B b → IsKBasisIn (B ⊓ cutSub K r e) b₀ →
    IsKBasisIn (B.map (projGe K r e)) b₁ →
    latDeg (diagMet δ) B b ≤
      latDeg (diagMet δ) (B ⊓ cutSub K r e) b₀ + latDeg (diagMet δ) (B.map (projGe K r e)) b₁

def AbsDetStatement : Prop :=
  ∀ (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℂ), A.PosDef → C.IsHermitian →
    (∀ v : Fin n → ℂ, ‖star v ⬝ᵥ (C *ᵥ v)‖ ≤ (star v ⬝ᵥ (A *ᵥ v)).re) → ‖C.det‖ ≤ A.det.re

end ReciprocityTheory.MultiplicativeHeights
end
end
