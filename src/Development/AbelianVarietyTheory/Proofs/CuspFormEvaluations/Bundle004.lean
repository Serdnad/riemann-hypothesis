module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory.SmulMemOfSpan

open NumberField

theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin r → E)) (v : Fin r → E)
    (hv : v ∈ Submodule.span E (L : Set (Fin r → E))) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ (c : E) • v ∈ L := by
  have hL : ∀ (n : RingOfIntegers E) (w : Fin r → E), w ∈ L → (n : E) • w ∈ L := by
    intro n w hw
    rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    exact L.smul_mem n hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [RingOfIntegers.coe_eq_algebraMap, map_one, one_smul]
    exact hx
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have e : ((c * d : RingOfIntegers E) : E) • (x + y) =
        (d : E) • ((c : E) • x) + (c : E) • ((d : E) • y) := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      ring
    rw [e]
    exact L.add_mem (hL d _ hcx) (hL c _ hdy)
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨n, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) a
    have hy0 : algebraMap (RingOfIntegers E) E y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    refine ⟨y * c, mul_ne_zero (nonZeroDivisors.ne_zero hy) hc, ?_⟩
    have e : ((y * c : RingOfIntegers E) : E) •
        ((algebraMap (RingOfIntegers E) E n / algebraMap (RingOfIntegers E) E y) • x) =
        (n : E) • ((c : E) • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      field_simp
    rw [e]
    exact hL n _ hcx

theorem exists_smul_mem_lattice : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E), ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ (↑c : E) • v ∈ ReciprocityTheory.ChartRestriction.G.FD.Data.Λ X := by
  intro E _ _ _ r X v
  refine exists_smul_mem_of_span X.Λ v ?_
  rw [X.Λ_span]
  exact Submodule.mem_top

end GlobalTheory.SmulMemOfSpan
end

section

namespace GlobalTheory

open Complex ReciprocityTheory.ChartRestriction.G.I2

namespace FockTranslation

variable {ι : Type} [Fintype ι]

theorem herm_add_left (u v w : EuclideanSpace ℂ ι) : Hf (u + v) w = Hf u w + Hf v w := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (u v w : EuclideanSpace ℂ ι) : Hf u (v + w) = Hf u v + Hf u w := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

theorem herm_sub_left (u v w : EuclideanSpace ℂ ι) : Hf (u - v) w = Hf u w - Hf v w := by
  simp [Hf, sub_mul, Finset.sum_sub_distrib]

theorem herm_sub_right (u v w : EuclideanSpace ℂ ι) : Hf u (v - w) = Hf u v - Hf u w := by
  simp [Hf, mul_sub, Finset.sum_sub_distrib]

theorem herm_neg_left (u w : EuclideanSpace ℂ ι) : Hf (-u) w = -Hf u w := by
  simp [Hf]

theorem herm_neg_right (u w : EuclideanSpace ℂ ι) : Hf u (-w) = -Hf u w := by
  simp [Hf]

theorem herm_zero_right (u : EuclideanSpace ℂ ι) : Hf u 0 = 0 := by
  simp [Hf]

theorem herm_smul_right (c : ℂ) (u w : EuclideanSpace ℂ ι) :
    Hf u (c • w) = (starRingEnd ℂ) c * Hf u w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem herm_conj (u w : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf u w) = Hf w u := by

  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem herm_sub_swap (u w : EuclideanSpace ℂ ι) :
    Hf w u = Hf u w - 2 * I * ((Hf u w).im : ℂ) := by
  have h := Complex.sub_conj (Hf u w)
  rw [herm_conj] at h
  push_cast at h
  linear_combination -h

theorem herm_self (x : EuclideanSpace ℂ ι) : Hf x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Hf, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem herm_self_re (x : EuclideanSpace ℂ ι) : (Hf x x).re = ‖x‖ ^ 2 := by
  rw [herm_self, Complex.ofReal_re]

theorem herm_self_im (x : EuclideanSpace ℂ ι) : (Hf x x).im = 0 := by
  rw [herm_self, Complex.ofReal_im]

theorem herm_re_swap (u w : EuclideanSpace ℂ ι) : (Hf w u).re = (Hf u w).re := by
  rw [← herm_conj u w, Complex.conj_re]

theorem herm_im_swap (u w : EuclideanSpace ℂ ι) : (Hf w u).im = -(Hf u w).im := by
  rw [← herm_conj u w, Complex.conj_im]

theorem herm_differentiable (a : EuclideanSpace ℂ ι) :
    Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v a := by
  unfold Hf
  fun_prop

end FockTranslation


open FockTranslation in
theorem fock_translation_laws {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)) (q : ℕ) :
    (∀ a b F, U q a (U q b F) = cexp (-(q * Real.pi * I * (Hf a b).im)) • U q (a + b) F) ∧ (∀ F, U q 0 F = F) ∧
    (∀ a F, (fun v => U q a F (-v)) = U q (-a) (fun v => F (-v))) ∧
    (∀ a F (M : ℕ), (U q a)^[M] F = U q ((M : ℂ) • a) F) ∧
    (∀ a F v, ‖U q a F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) = ‖F (v - a)‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v - a‖ ^ 2)) ∧
    (∀ (Y : GT ι) F, F ∈ Y.Sec q ↔ Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, Y.ka γ • U q γ F = F) ∧
    (∀ (Y : GT ι) a, (∀ γ ∈ lat Y.b, ∃ k : ℤ, q * (Hf a γ).im = k) → ∀ F ∈ Y.Sec q, U q a F ∈ Y.Sec q) ∧
    (∀ (φ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (N : ℕ), (∀ v w, Hf (φ v) (φ w) = N * Hf v w) →
      ∀ a F, U (q * N) a (F ∘ φ) = U q (φ a) F ∘ φ) := by
  have h1 : ∀ a b F, U q a (U q b F) =
      cexp (-(q * Real.pi * I * (Hf a b).im)) • U q (a + b) F := by
    intro a b F
    funext v
    simp only [hU, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, sub_sub]
    congr 2
    simp only [FockTranslation.herm_add_left, FockTranslation.herm_add_right,
      FockTranslation.herm_sub_left]
    rw [FockTranslation.herm_sub_swap a b]
    ring
  have h2 : ∀ F, U q 0 F = F := by
    intro F
    funext v
    simp [hU, FockTranslation.herm_zero_right]
  have h6 : ∀ (Y : GT ι) F, F ∈ Y.Sec q ↔
      Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, Y.ka γ • U q γ F = F := by
    intro Y F
    have key : ∀ γ v, (Y.ka γ • U q γ F) (v + γ) =
        Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * F v := by
      intro γ v
      simp only [hU, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right,
        FockTranslation.herm_add_left]
      rw [← mul_assoc]
      congr 3
      ring
    refine and_congr_right fun _ => forall₂_congr fun γ _ => ⟨fun h => ?_, fun h v => ?_⟩
    · funext w
      have := key γ (w - γ)
      rw [← h, sub_add_cancel] at this
      exact this
    · rw [← key, h]
  refine ⟨h1, h2, ?_, ?_, ?_, h6, ?_, ?_⟩
  · intro a F
    funext v
    simp only [hU, FockTranslation.herm_neg_left, FockTranslation.herm_neg_right, neg_neg]
    congr 2
    abel
  · intro a F M
    induction M with
    | zero => simp [h2]
    | succ M ih =>
      rw [Function.iterate_succ_apply', ih, h1]
      have : (Hf a ((M : ℂ) • a)).im = 0 := by
        rw [FockTranslation.herm_smul_right]
        simp [FockTranslation.herm_self_im]
      rw [this]
      have e : a + (M : ℂ) • a = ((M + 1 : ℕ) : ℂ) • a := by
        push_cast
        rw [add_smul, one_smul, add_comm]
      simp [e]
  · intro a F v
    rw [hU, norm_mul, mul_pow, Complex.norm_exp, mul_comm (_ ^ 2) (‖F (v - a)‖ ^ 2), mul_assoc,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    rw [← FockTranslation.herm_self_re v, ← FockTranslation.herm_self_re (v - a)]
    have e : (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 : ℂ) =
        ((q * Real.pi : ℝ) : ℂ) * Hf v a - ((q * Real.pi / 2 : ℝ) : ℂ) * Hf a a := by
      push_cast
      ring
    rw [e]
    simp only [FockTranslation.herm_sub_left, FockTranslation.herm_sub_right, Complex.sub_re,
      Complex.re_ofReal_mul, FockTranslation.herm_re_swap v a]
    push_cast
    ring
  · intro Y a ha F hF
    rw [h6] at hF ⊢
    obtain ⟨hd, hF⟩ := hF
    refine ⟨?_, fun γ hγ => ?_⟩
    · have e : U q a F = fun v =>
          cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a) :=
        funext fun v => hU q a F v
      rw [e]
      have := FockTranslation.herm_differentiable a
      fun_prop
    · obtain ⟨k, hk⟩ := ha γ hγ
      have hk' : (q : ℂ) * ((Hf a γ).im : ℂ) = k := by exact_mod_cast hk
      have hc : U q γ (U q a F) = U q a (U q γ F) := by
        rw [h1, h1, add_comm γ a]
        congr 1
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨k, ?_⟩
        rw [FockTranslation.herm_im_swap a γ, ← hk']
        push_cast
        ring
      rw [hc]
      conv_rhs => rw [← hF γ hγ]
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, hU q a]
      ring
  · intro φ N hφ a F
    funext v
    simp only [hU, Function.comp_apply, hφ, map_sub]
    congr 2
    push_cast
    ring

end GlobalTheory
end

section

open scoped BigOperators
open NumberField

namespace GlobalTheory.GridSize

open GlobalTheory.Harm GlobalTheory.MvPoly

section Minor

variable {T : Type*} {p q n : ℕ}

theorem l1Norm_rowBlockLinearForm_le (t : T) (r : Fin p ⊕ Fin q) (v : Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∑ k, ‖v k‖ ^ 2 ≤ R ^ 2) : l1Norm (rowForm t r v) ≤ √(n : ℝ) * R := by
  rw [rowForm_apply]
  refine (l1Norm_linearForm_le (fun k => (t, r, k)) v).trans ?_
  rw [Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hR, hv⟩) (Real.sqrt_nonneg _)

theorem l1Norm_det_le_of_entry_bound {σ : Type*} {i N : ℕ} (hi : i ≤ N)
    (M : Matrix (Fin i) (Fin i) (MvPolynomial σ ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a b, l1Norm (M a b) ≤ B) : l1Norm M.det ≤ (N * B) ^ i := by
  refine (l1Norm_det_le_pow M h).trans ?_
  rw [Fintype.card_fin]
  have : (i : ℝ) ≤ N := by exact_mod_cast hi
  gcongr

theorem l1Norm_rowBlockLeadingMinorProduct_le [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → Fin n → ℂ) (φ : T → Fin q → Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hε : ∀ t a, ∑ k, ‖ε t a k‖ ^ 2 ≤ R ^ 2) (hφ : ∀ t b, ∑ k, ‖φ t b k‖ ^ 2 ≤ R ^ 2)
    {N : ℕ} (hp : p ≤ N) (hq : q ≤ N) :
    l1Norm (minorProd c c' ε φ) ≤ (N * √(n : ℝ) * R) ^ typeDegree c c' := by
  have hB : 0 ≤ √(n : ℝ) * R := by positivity
  rw [minorProd, typeDegree, ← Finset.prod_pow_eq_pow_sum, mul_assoc]
  refine (l1Norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => l1Norm_nonneg _) fun t _ => ?_)
  rw [pow_add]
  refine (l1Norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (l1Norm_nonneg _) (by positivity))
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hε _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hφ _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]

end Minor

section Length

variable {E : Type*} [CommRing E] {κ : Type*} [Fintype κ]

noncomputable def embSeminorm (τ : E →+* ℂ) : RingSeminorm E where
  toFun x := ‖τ x‖
  map_zero' := by simp
  add_le' x y := by rw [map_add (f := _)]; exact norm_add_le _ _
  neg' x := by simp
  mul_le' x y := by simp

noncomputable def embVec (τ : E →+* ℂ) : (κ → E) →+ EuclideanSpace ℂ κ where
  toFun v := WithLp.toLp 2 fun k => τ (v k)
  map_zero' := by ext k; simp
  map_add' v w := by ext k; simp



omit [Fintype κ] in
theorem embVec_smul (τ : E →+* ℂ) (x : E) (v : κ → E) : embVec τ (x • v) = τ x • embVec τ v := by
  ext k; simp [embVec, Pi.smul_apply]

noncomputable def embLength (τ : E →+* ℂ) : AddGroupSeminorm (κ → E) where
  toFun v := ‖embVec τ v‖
  map_zero' := by simp
  add_le' x y := by rw [map_add (f := _)]; exact norm_add_le _ _
  neg' x := by simp

theorem embLength_apply (τ : E →+* ℂ) (v : κ → E) : embLength τ v = ‖embVec τ v‖ := rfl

theorem embLength_sq (τ : E →+* ℂ) (v : κ → E) : embLength τ v ^ 2 = ∑ k, ‖τ (v k)‖ ^ 2 := by
  rw [embLength_apply, EuclideanSpace.norm_sq_eq]; rfl

theorem embLength_smul (τ : E →+* ℂ) (x : E) (v : κ → E) :
    embLength τ (x • v) = ‖τ x‖ * embLength τ v := by
  rw [embLength_apply, embVec_smul, norm_smul, embLength_apply]

theorem embLength_le_abs (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2) :
    embLength τ v ≤ |R| :=
  (le_abs_self _).trans (sq_le_sq.mp (by rwa [embLength_sq]))

theorem sum_sq_le_of_embLength_le (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : embLength τ v ≤ |R|) :
    ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2 := by
  rw [← embLength_sq, ← sq_abs R]
  exact pow_le_pow_left₀ (apply_nonneg _ _) h 2

theorem norm_emb_sum_mul_le (τ : E →+* ℂ) (s : E → E) (hs : ∀ x, ‖τ (s x)‖ = ‖τ x‖)
    (x y : κ → E) : ‖τ (∑ k, x k * s (y k))‖ ≤ embLength τ x * embLength τ y := by

  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  simp only [map_mul, norm_mul, hs]
  refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  rw [mul_pow, embLength_sq, embLength_sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem sum_sq_combination_le (τ : E →+* ℂ) {ι : Type*} [Fintype ι] (v : ι → κ → E) {ρ : ℝ}
    (hv : ∀ i, ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2) (A : ι → ℕ) {d : ℕ} (hA : ∀ i, A i ≤ d) :
    ∑ k, ‖τ ((∑ i, (A i : E) • v i) k)‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * d * ρ) ^ 2 := by
  apply sum_sq_le_of_embLength_le

  rw [embLength_apply, map_sum, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast, mul_assoc,
  ← nsmul_eq_mul, ← Finset.card_univ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_)
  rw [← embLength_apply, embLength_smul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul (by exact_mod_cast hA i) (embLength_le_abs τ (hv i)) (apply_nonneg _ _)
    (Nat.cast_nonneg _)

end Length

section Perp

open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.FD

theorem perpVec_eq_perpVector {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {p : ℕ}
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) :
    perpVec h e e' g = perpVector (fun a => (LinearMap.proj (e a)).comp h) e' g := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p n : ℕ}

theorem sum_sq_perpVec_le (τ : E →+* ℂ) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (e e' : Fin p → Fin n → E) (g : Fin n → E) {R : ℝ}
    (he : ∀ a, ∑ k, ‖τ (e a k)‖ ^ 2 ≤ R ^ 2) (he' : ∀ a, ∑ k, ‖τ (e' a k)‖ ^ 2 ≤ R ^ 2)
    (hg : ∑ k, ‖τ (g k)‖ ^ 2 ≤ R ^ 2) :
    ∑ k, ‖τ (perpVec h e e' g k)‖ ^ 2 ≤ (((p + 1).factorial : ℝ) * R ^ (2 * p + 1)) ^ 2 := by
  have hs : ∀ x, ‖τ (cc x)‖ = ‖τ x‖ := fun x => by
    rw [cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have key : ∀ u v, embLength τ u ≤ |R| → embLength τ v ≤ |R| → ‖τ (h u v)‖ ≤ |R| ^ 2 :=
    fun u v hu hv => by
      rw [hh, sq]
      exact (norm_emb_sum_mul_le τ cc hs u v).trans
        (mul_le_mul hu hv (apply_nonneg _ _) (abs_nonneg _))
  apply sum_sq_le_of_embLength_le
  rw [perpVec_eq_perpVector, abs_mul, Nat.abs_cast, abs_pow, pow_succ, pow_mul, ← mul_assoc]
  exact seminorm_perpVector_le (embSeminorm τ) (by change ‖τ 1‖ ≤ 1; simp) (embLength τ)
    (fun x v => (embLength_smul τ x v).le) _ e' g
    (fun a a' => key _ _ (embLength_le_abs τ (he' a')) (embLength_le_abs τ (he a)))
    (fun a => key _ _ (embLength_le_abs τ hg) (embLength_le_abs τ (he a)))
    (fun a => embLength_le_abs τ (he' a)) (embLength_le_abs τ hg)

end Perp

end GlobalTheory.GridSize
end
