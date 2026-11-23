module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

section Mat

variable {n : ℕ}

lemma uGu_lower (G : Matrix (Fin n) (Fin n) ℂ) (hdet : ∀ c : Fin n, (blk G c).det ≠ 0) {a c : Fin n}
    (hac : a < c) : ((uMat G)ᵀ * G * (uMat G).map (starRingEnd ℂ)) c a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge a k with h | h
  · rw [Matrix.map_apply, upper_lt (uMat_upper G) h, map_zero, mul_zero]
  · rw [uT_G_zero G c (hdet c) k (lt_of_le_of_lt h hac), zero_mul]

lemma prod_castLE_succ {k : ℕ} (h : k + 1 ≤ n) (f : Fin n → ℂ) :
    ∏ j : Fin (k + 1), f (Fin.castLE h j) = (∏ j : Fin k, f (Fin.castLE (Nat.le_of_succ_le h) j)) * f ⟨k, h⟩ := by
  rw [Fin.prod_univ_castSucc]
  rfl

lemma lminor_diagonal (D : Fin n → ℂ) (i : Fin (n + 1)) :
    lminor (Matrix.diagonal D) i = ∏ j : Fin i, D (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  rw [lminor, det_sub_upper _ (Matrix.blockTriangular_diagonal D)]
  simp

end Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def uOf (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := uMat (gram τ.1 X.Gm (mat x τ))

def dOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := gram τ.1 X.Gm (mat x τ * uOf X x τ) k k

lemma blk_det {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (c : Fin r) :
    (blk (gram τ.1 X.Gm (mat x τ)) c).det ≠ 0 := by
  intro h0
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 c.castSucc
  have h2 : dmin X.Gm x τ c.castSucc = 0 := h0
  rw [h2, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1

lemma gram_u_eq {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat x τ * uOf X x τ) = Matrix.diagonal (dOf X x τ) := by
  ext c a
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · rcases lt_or_gt_of_ne h with h' | h'
    · have hH := gram_isHermitian τ.1 X.Gm_herm (mat x τ * uOf X x τ)
      rw [← hH.apply c a, uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h', star_zero]
    · rw [uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h']

lemma dOf_real {x : Frame X.Ψ r} (_hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : (dOf X x τ k).im = 0 := by
  have hH := gram_isHermitian τ.1 X.Gm_herm (mat x τ * uOf X x τ)
  exact Complex.conj_eq_iff_im.mp (hH.apply k k)

lemma dmin_prod {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ∏ j : Fin i, dOf X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  have h1 := lminor_conj (N := uOf X x τ) (A := gram τ.1 X.Gm (mat x τ)) (uMat_upper _) i
  rw [← gram_mul, gram_u_eq X hx τ, lminor_diagonal] at h1
  simp only [uOf, uMat_diag, Finset.prod_const_one, map_one, one_mul, mul_one] at h1
  exact h1.symm

lemma dmin_succ {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    dmin X.Gm x τ k.succ = dmin X.Gm x τ k.castSucc * dOf X x τ k := by
  rw [dmin_prod X hx τ, dmin_prod X hx τ]
  exact prod_castLE_succ k.isLt (dOf X x τ)

lemma psgn_succ (p0 k : ℕ) : psgn p0 (k + 1) = psgn p0 k * sgn p0 k := by
  rw [psgn, psgn, Finset.prod_range_succ]

lemma sgn_dOf_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    0 < sgn X.p0 k * (dOf X x τ k).re := by
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 k.castSucc
  have h2 := ((X.mem_dom_iff x).1 hx τ).2 k.succ
  rw [dmin_succ X hx τ k, Complex.mul_re, dOf_real X hx τ k, mul_zero, sub_zero] at h2
  rw [Fin.val_succ, psgn_succ] at h2
  rw [Fin.coe_castSucc] at h1
  by_contra hneg
  push_neg at hneg
  nlinarith

def sOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := ((Real.sqrt |(dOf X x τ k).re|)⁻¹ : ℝ)

def bOf (x : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (uOf X x τ * Matrix.diagonal (sOf X x τ) : Matrix _ _ ℂ)

lemma sgn_sq (p0 k : ℕ) : sgn p0 k = 1 ∨ sgn p0 k = -1 := by
  unfold sgn
  split_ifs <;> simp

lemma abs_re_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : 0 < |(dOf X x τ k).re| := by
  have h := sgn_dOf_pos X hx τ k
  refine abs_pos.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact lt_irrefl _ h

lemma sOf_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : sOf X x τ k ≠ 0 := by
  unfold sOf
  rw [Ne, Complex.ofReal_eq_zero, inv_eq_zero, Real.sqrt_eq_zero']
  exact not_le.mpr (abs_re_pos X hx τ k)

lemma bOf_mem {x : Frame X.Ψ r} (hx : x ∈ X.dom) : bOf X x ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)).det ≠ 0
    unfold uOf
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_of_upperTriangular (uMat_upper _)]
    simp only [uMat_diag, Finset.prod_const_one, one_mul]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => sOf_ne X hx τ k
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)) a c = 0
    unfold uOf
    rw [Matrix.mul_diagonal, upper_lt (uMat_upper _) hca, zero_mul]

lemma ortho_bOf {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.IsOrtho (rmul x (bOf X x)) := by
  intro τ
  change gram τ.1 X.Gm (mat x τ * (uOf X x τ * Matrix.diagonal (sOf X x τ))) = _
  rw [← Matrix.mul_assoc, gram_mul, gram_u_eq X hx τ, Matrix.diagonal_transpose,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  have hd : dOf X x τ a = ((dOf X x τ a).re : ℂ) :=
    Complex.ext (by simp) (by simp [dOf_real X hx τ a])
  have hpos := sgn_dOf_pos X hx τ a
  have habs := abs_re_pos X hx τ a
  rw [hd]
  simp only [sOf, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  set d := (dOf X x τ a).re
  have hs : (Real.sqrt |d|)⁻¹ * d * (Real.sqrt |d|)⁻¹ = d / |d| := by
    rw [mul_comm _ d, mul_assoc, ← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_mul_inv]
  rw [hs]
  rcases sgn_sq X.p0 a with h1 | h1 <;> rw [h1] at hpos ⊢
  · rw [abs_of_pos (by linarith), div_self (by linarith)]
  · have hn : d < 0 := by linarith
    rw [abs_of_neg hn, div_neg, div_self hn.ne]

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quad2 (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) (a : Fin 2 → ℂ) :
    M.det.re * Complex.normSq (a 1) ≤ (M 0 0).re * (∑ i, ∑ k, M i k * a i * conj (a k)).re := by
  have h00 : (M 0 0).im = 0 := by
    have := hM.apply 0 0
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h11 : (M 1 1).im = 0 := by
    have := hM.apply 1 1
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h10 : M 1 0 = conj (M 0 1) := by
    have := hM.apply 1 0
    rw [Complex.star_def] at this
    exact this.symm
  simp only [Matrix.det_fin_two, Fin.sum_univ_two, h10, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, h00, h11]
  nlinarith [sq_nonneg ((M 0 0).re * (a 0).re + (M 0 1).re * (a 1).re + (M 0 1).im * (a 1).im),
    sq_nonneg ((M 0 0).re * (a 0).im + (M 0 1).re * (a 1).im - (M 0 1).im * (a 1).re)]

theorem coef_zero {r : ℕ} {ξ x : Fin r → E} (hξ0 : ξ ≠ 0) (hne : ∀ e : E, x ≠ e • ξ)
    (τ : E →+* ℂ) (p q : ℂ) (h : p • Data.emb τ ξ + q • Data.emb τ x = 0) : q = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hξ0 (funext h0)
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ (x a / ξ a) * ξ b := by
    by_contra h0
    push_neg at h0
    exact hne (x a / ξ a) (funext fun b => by rw [Pi.smul_apply, smul_eq_mul, h0 b])
  have hm : ξ a * x b - ξ b * x a ≠ 0 := by
    intro h0
    apply hb
    rw [div_mul_eq_mul_div, eq_div_iff ha]
    linear_combination h0
  have h1 := congrFun h a
  have h2 := congrFun h b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Data.emb] at h1 h2
  have hτ : τ (ξ a * x b - ξ b * x a) ≠ 0 := (map_ne_zero τ).2 hm
  rw [map_sub, map_mul, map_mul] at hτ
  have h3 : q * (τ (ξ a) * τ (x b) - τ (ξ b) * τ (x a)) = 0 := by
    linear_combination τ (ξ a) * h2 - τ (ξ b) * h1
  exact (mul_eq_zero.1 h3).resolve_right hτ

variable {r : ℕ} (X : Data E r)

def toCP (τ : X.Ψ) : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩

theorem toCP_bij : Function.Bijective (toCP X) := by
  constructor
  · rintro ⟨τ, hτ⟩ ⟨τ', hτ'⟩ h
    have h' : InfinitePlace.mk τ = InfinitePlace.mk τ' := congrArg Subtype.val h
    rcases InfinitePlace.mk_eq_iff.1 h' with e | e
    · exact Subtype.ext e
    · exfalso
      rw [← e] at hτ'
      exact (X.cmType τ).1 hτ hτ'
  · rintro ⟨w, hw⟩
    by_cases hφ : w.embedding ∈ X.Ψ
    · exact ⟨⟨_, hφ⟩, Subtype.ext (InfinitePlace.mk_embedding w)⟩
    · have hc : ComplexEmbedding.conjugate w.embedding ∈ X.Ψ := by
        by_contra hc
        exact hφ ((X.cmType _).2 hc)
      exact ⟨⟨_, hc⟩, Subtype.ext ((InfinitePlace.mk_conjugate_eq _).trans (InfinitePlace.mk_embedding w))⟩

theorem card_Psi : Fintype.card X.Ψ = fdeg E := by
  rw [Fintype.card_of_bijective (toCP_bij X)]
  unfold fdeg
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
  have h0 : NumberField.InfinitePlace.nrRealPlaces E = 0 := by
    first
    | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero
    | exact NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance
    | simp
  rw [h0, zero_add] at h
  rw [← h]
  unfold NumberField.InfinitePlace.nrComplexPlaces
  have h3 : Fintype.card (TraceIntegralBasis.CP E) = Fintype.card {w : InfinitePlace E // w.IsComplex} :=
    Fintype.card_congr (Equiv.refl _)
  omega

theorem card_Psi_pos : 0 < Fintype.card X.Ψ := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(Classical.arbitrary (InfinitePlace E)).embedding⟩
  rw [Fintype.card_pos_iff]
  by_cases h : φ ∈ X.Ψ
  · exact ⟨⟨φ, h⟩⟩
  · exact ⟨⟨ComplexEmbedding.conjugate φ, by
      by_contra hc
      exact h ((X.cmType φ).2 hc)⟩⟩

theorem one_le_prod_norm (γ : E) (hint : IsIntegral ℤ γ) (hγ : γ ≠ 0) :
    1 ≤ ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 := by
  have hall : ∀ w : InfinitePlace E, w.IsComplex := fun w => IsTotallyComplex.isComplex w
  have h1 : ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 = ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 :=
    Fintype.prod_bijective (toCP X) (toCP_bij X) _ _ fun τ => by
      show _ = (InfinitePlace.mk τ.1 γ) ^ 2
      rw [InfinitePlace.apply]
  have h2 : ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 = ∏ w : InfinitePlace E, w γ ^ w.mult := by
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv hall) _ _ fun w => ?_
    show w.1 γ ^ 2 = w.1 γ ^ InfinitePlace.mult w.1
    rw [InfinitePlace.mult_isComplex w]
  rw [h1, h2, InfinitePlace.prod_eq_abs_norm]
  have hI : IsIntegral ℤ (Algebra.norm ℚ γ) := by
    first
    | exact Algebra.isIntegral_norm ℚ hint
    | exact Algebra.isIntegral_norm hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have hN : Algebra.norm ℚ γ ≠ 0 := Algebra.norm_ne_zero_iff.2 hγ
  rw [← hn] at hN ⊢
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hN (map_zero _)
  have h3 := Int.one_le_abs hn0
  simp only [algebraMap_int_eq, eq_intCast]
  push_cast
  exact_mod_cast h3

end

end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

def nsq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ j, ‖v j‖ ^ 2

lemma nsq_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ nsq v := by
  unfold nsq
  positivity

lemma nsq_mulVec_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (A.mulVec v) ≤ (∑ i, ∑ j, ‖A i j‖ ^ 2) * nsq v := by
  unfold nsq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h1 : ‖A.mulVec v i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => norm_mul _ _
  calc ‖A.mulVec v i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma opN_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    BddAbove {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
      t = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
  refine ⟨Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2), ?_⟩
  rintro t ⟨v, -, rfl⟩
  have hF : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by positivity
  have key := nsq_mulVec_le A v
  have hb : 0 ≤ nsq v := nsq_nonneg v
  unfold nsq at key hb
  rcases hb.eq_or_lt with h | h
  · rw [← h]
    simp
  · rw [div_le_iff₀ (Real.sqrt_pos.2 h), ← Real.sqrt_mul hF]
    exact Real.sqrt_le_sqrt key

lemma opN_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ Data.opN A := by
  unfold Data.opN
  apply Real.sSup_nonneg
  rintro t ⟨v, -, rfl⟩
  positivity

lemma nsq_mulVec_le_opN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (A.mulVec v) ≤ Data.opN A ^ 2 * nsq v := by
  by_cases hv : v = 0
  · subst hv
    simp [nsq, Matrix.mulVec_zero]
  have hmem : Real.sqrt (nsq (A.mulVec v)) / Real.sqrt (nsq v) ≤ Data.opN A :=
    le_csSup (opN_bdd A) ⟨v, hv, rfl⟩
  have hpos : 0 < nsq v := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    unfold nsq
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hj) 2)
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖) (Finset.mem_univ j))
  rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)] at hmem
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hmem 2
  rwa [mul_pow, Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt hpos.le] at h2

lemma opN_le_zN {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (Z : X.Coord) (τ : X.Ψ) : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
  unfold Data.zN
  exact le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open Metric Set

lemma exp_nine_quarters_lt : Real.exp (9 / 4) < 9.5 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : |Real.exp (1 / 4) - ∑ m ∈ Finset.range 4, (1 / 4 : ℝ) ^ m / m.factorial| ≤
      |(1 / 4 : ℝ)| ^ 4 * ((Nat.succ 4 : ℕ) / ((Nat.factorial 4 : ℕ) * 4)) :=
    Real.exp_bound (by norm_num [abs_of_pos]) (by norm_num)
  have h3 : Real.exp (1 / 4) < 1.2841 := by
    have := (abs_le.mp h2).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have h4 : Real.exp (9 / 4) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he4 : 0 < Real.exp (1 / 4) := Real.exp_pos _
  rw [h4]
  calc Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) ≤ 2.7182818286 * 2.7182818286 * 1.2841 := by
        gcongr
    _ < 9.5 := by norm_num

theorem schwarzLemmaBall_holds : SchwarzLemmaBall := by
  intro V _ _ γ ρ S hρ hd hb h1 h2 Z hZ
  have hS : 0 < S := by linarith [norm_nonneg (γ 0)]
  have hmaps : MapsTo γ (ball 0 ρ) (closedBall (γ 0) ((Real.exp (9 / 4) + 1) * S)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖γ z - γ 0‖ ≤ ‖γ z‖ + ‖γ 0‖ := norm_sub_le _ _
      _ ≤ Real.exp (9 / 4) * S + S := add_le_add (hb z (ball_subset_closedBall hz)) h2
      _ = (Real.exp (9 / 4) + 1) * S := by ring
  have hZρ : Z ∈ ball (0 : V) ρ := ball_subset_ball (by linarith) hZ
  have key := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hd.mono ball_subset_closedBall) hmaps hZρ
  have hZn : ‖Z‖ < ρ / 21 := by simpa using hZ
  rw [dist_zero_right] at key
  intro h0
  rw [h0, dist_comm, dist_zero_right] at key
  have hexp := exp_nine_quarters_lt
  have : (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ < S / 2 := by
    calc (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ ≤ (Real.exp (9 / 4) + 1) * S / ρ * (ρ / 21) := by
          gcongr
      _ = (Real.exp (9 / 4) + 1) * S / 21 := by field_simp
      _ < S / 2 := by nlinarith
  linarith

end ReciprocityTheory.ChartRestriction.G.FD
end
