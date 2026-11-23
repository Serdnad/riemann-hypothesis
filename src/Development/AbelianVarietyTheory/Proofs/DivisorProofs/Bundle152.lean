module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
public import Mathlib.RingTheory.Derivation.Lie
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
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open scoped nonZeroDivisors
open Metric Complex

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem eisTerm_at_zero_eq {F : Type} [Field F] [NumberField F] (k : ℕ) (z : Emb F → ℂ) (p : F × F) :
    eisTerm k 0 z p = (∏ τ, latPt z p τ)⁻¹ ^ k := by
  simp [eisTerm]

theorem norm_latPt_le_two_mul_of_near {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (p : F × F) (τ : Emb F) :
    ‖latPt z₀ p τ‖ ≤ 2 * ‖latPt z p τ‖ := by
  have h1 : ‖z τ - z₀ τ‖ < r := lt_of_le_of_lt (norm_le_pi_norm (z - z₀) τ) hz
  have h2 : r ≤ (z τ).im := by
    have h3 := abs_im_le_norm (z τ - z₀ τ)
    rw [sub_im] at h3
    have h4 := (abs_le.1 (h3.trans h1.le)).1
    linarith [hr τ]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have e : latPt z₀ p τ = latPt z p τ + 2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ) := by
    simp only [latPt]; ring
  have hn : ∀ w : ℂ, ‖2 * (Real.pi : ℂ) * I * w‖ = 2 * Real.pi * ‖w‖ := by
    intro w
    rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    norm_num
  have hlow : 2 * Real.pi * (|τ p.2| * r) ≤ ‖latPt z p τ‖ := by
    rw [latPt, hn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ (abs_im_le_norm _)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add]
    rw [abs_mul, abs_of_pos (lt_of_lt_of_le (lt_of_le_of_lt (norm_nonneg _) hz) h2)]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hup : ‖2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ)‖ ≤ 2 * Real.pi * (|τ p.2| * r) := by
    rw [show 2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ) = 2 * (Real.pi : ℂ) * I * (((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ)) by ring, hn, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)) (by positivity)
  rw [e]
  linarith [norm_add_le (latPt z p τ) (2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ))]

theorem norm_eisTerm_zero_le_of_near {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hz₀ : z₀ ∈ upperHalf F) (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (k : ℕ) {p : F × F} (hp : p ≠ 0) :
    ‖eisTerm k 0 z p‖ ≤ (2 ^ Fintype.card (Emb F)) ^ k * ‖eisTerm k 0 z₀ p‖ := by
  rw [eisTerm_at_zero_eq, eisTerm_at_zero_eq, norm_pow, norm_pow, norm_inv, norm_inv, norm_prod, norm_prod, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have hA : 0 < ∏ τ, ‖latPt z₀ p τ‖ :=
    Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz₀ hp τ)
  have hAB : ∏ τ, ‖latPt z₀ p τ‖ ≤ 2 ^ Fintype.card (Emb F) * ∏ τ, ‖latPt z p τ‖ := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) fun τ _ => norm_latPt_le_two_mul_of_near hr hz p τ
  have h2 : (0 : ℝ) < 2 ^ Fintype.card (Emb F) := by positivity
  have hB : 0 < ∏ τ, ‖latPt z p τ‖ := by
    by_contra h
    push_neg at h
    nlinarith
  rw [inv_le_comm₀ hB (by positivity), mul_inv, inv_inv]
  calc (2 ^ Fintype.card (Emb F))⁻¹ * ∏ τ, ‖latPt z₀ p τ‖ ≤ (2 ^ Fintype.card (Emb F))⁻¹ * (2 ^ Fintype.card (Emb F) * ∏ τ, ‖latPt z p τ‖) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
    _ = ∏ τ, ‖latPt z p τ‖ := by field_simp

theorem eisSum_zero_differentiableOn :
    ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F) (k : ℕ),
      (∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 k 0 z)) →
      DifferentiableOn ℂ (eisSum 𝔞 𝔟 k 0) (upperHalf F) := by
  intro F _ _ _ 𝔞 𝔟 k hs z₀ hz₀
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ τ, 2 * r ≤ (z₀ τ).im := by
    rcases isEmpty_or_nonempty (Emb F) with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · refine ⟨(Finset.univ.inf' Finset.univ_nonempty fun τ => (z₀ τ).im) / 2, ?_, fun τ => ?_⟩
      · exact half_pos ((Finset.lt_inf'_iff _).2 fun τ _ => hz₀ τ)
      · have := Finset.inf'_le (fun τ => (z₀ τ).im) (Finset.mem_univ τ)
        linarith
  have hsub : ball z₀ r ⊆ upperHalf F := by
    intro z hz τ
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : ‖z τ - z₀ τ‖ < r := lt_of_le_of_lt (norm_le_pi_norm (z - z₀) τ) hz
    have h3 := abs_im_le_norm (z τ - z₀ τ)
    rw [sub_im] at h3
    have h4 := (abs_le.1 (h3.trans h1.le)).1
    linarith [hr τ]
  have hdiff : ∀ c : Quotient (latRel 𝔞 𝔟), DifferentiableOn ℂ (fun z => eisClass 𝔞 𝔟 k 0 z c) (ball z₀ r) := by
    intro c z hz
    have hp : c.out.1 ≠ 0 := c.out.2.2.2
    have e : (fun z => eisClass 𝔞 𝔟 k 0 z c) = fun z => (∏ τ, latPt z c.out.1 τ)⁻¹ ^ k := by
      funext z; exact eisTerm_at_zero_eq k z c.out.1
    rw [e]
    have hP : Differentiable ℂ (fun z : Emb F → ℂ => ∏ τ, latPt z c.out.1 τ) := by
      unfold latPt; fun_prop
    have hne : ∏ τ, latPt z c.out.1 τ ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => latPt_ne_zero (hsub hz) hp τ
    exact ((hP z).inv hne).pow k |>.differentiableWithinAt
  have hbd : ∀ c : Quotient (latRel 𝔞 𝔟), ∀ z ∈ ball z₀ r,
      ‖eisClass 𝔞 𝔟 k 0 z c‖ ≤ (2 ^ Fintype.card (Emb F)) ^ k * ‖eisClass 𝔞 𝔟 k 0 z₀ c‖ := by
    intro c z hz
    rw [mem_ball, dist_eq_norm] at hz
    exact norm_eisTerm_zero_le_of_near hz₀ hr hz k c.out.2.2.2
  have hsum : Summable fun c => (2 ^ Fintype.card (Emb F) : ℝ) ^ k * ‖eisClass 𝔞 𝔟 k 0 z₀ c‖ :=
    (summable_norm_iff.2 (hs z₀ hz₀)).mul_left _
  have h := GlobalTheory.differentiableOn_tsum_of_norm_le (Emb F → ℂ) (Quotient (latRel 𝔞 𝔟)) (ball z₀ r)
    (fun c z => eisClass 𝔞 𝔟 k 0 z c) _ isOpen_ball hdiff hsum hbd
  exact (h.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr0))).differentiableWithinAt

end GlobalTheory
end

section

namespace GlobalTheory.TotalDegreeBounds

open MvPolynomial

theorem totalDegree_aeval_le {σ τ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (f : σ → MvPolynomial τ A) (hf : ∀ i, (f i).totalDegree ≤ 1) (P : MvPolynomial σ R) :
    (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap R (MvPolynomial τ A) (AddMonoidAlgebra.coeff P d)).totalDegree = 0 := by
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.totalDegree_C]
  rw [h0, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hf i)

theorem totalDegree_sum_X_mul_C_le {ι τ A : Type*} [Fintype ι] [CommSemiring A]
    (g : ι → τ) (a : ι → A) :
    (∑ l : ι, (X (g l) * C (a l) : MvPolynomial τ A)).totalDegree ≤ 1 := by
  classical
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, add_zero]
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  simp

theorem main : (let d1 : (n : ℕ) → Fin n × Fin n ⊕ Fin n × Fin n → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n) := @(fun (n : ℕ) (x : Fin n × Fin n ⊕ Fin n × Fin n) ↦ match x with | Sum.inl x => ∑ l : Fin n, MvPolynomial.X (Sum.inr (l, Prod.fst x)) * (MvPolynomial.C : MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ)) (MvPolynomial.X (Sum.inl (l, Prod.snd x))) | Sum.inr x => ∑ l : Fin n, MvPolynomial.X (Sum.inl (l, Prod.fst x)) * (MvPolynomial.C : MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ)) (MvPolynomial.X (Sum.inr (l, Prod.snd x)))); let d2 : (n : ℕ) → GlobalTheory.PsCo.Pc1.Poly n →ₐ[ℂ] MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n) := @(fun (n : ℕ) ↦ MvPolynomial.aeval (d1 n)); ∀ {n : ℕ} (P : GlobalTheory.PsCo.Pc1.Poly n), MvPolynomial.totalDegree ((d2 n : GlobalTheory.PsCo.Pc1.Poly n → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n)) P) ≤ MvPolynomial.totalDegree P) := by
  intro d1 d2 n P
  refine totalDegree_aeval_le (d1 n) ?_ P
  rintro (x | x)
  · exact totalDegree_sum_X_mul_C_le _ _
  · exact totalDegree_sum_X_mul_C_le _ _

end GlobalTheory.TotalDegreeBounds
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Pc1

private theorem sg_sq' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg; split_ifs <;> simp

private theorem conj_sg' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (starRingEnd ℂ) (sg ε a) = sg ε a := by
  unfold sg; split_ifs <;> simp

private theorem lieU_decomposition {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) :
    ∃ A B : Mat n, LieU ε A ∧ LieU ε B ∧ Z = A + Complex.I • B := by
  refine ⟨Matrix.of fun a b => (Z a b + (starRingEnd ℂ) (barM ε Z a b)) / 2,
    Matrix.of fun a b => -Complex.I * (Z a b - (starRingEnd ℂ) (barM ε Z a b)) / 2, ?_, ?_, ?_⟩
  · intro a b
    have ha := sg_sq' ε a
    have hb := sg_sq' ε b
    simp only [barM, Matrix.of_apply, map_div₀, map_add (f := _), map_neg, map_mul, conj_sg',
      Complex.conj_conj, map_ofNat]
    linear_combination (-(starRingEnd ℂ) (Z a b) / 2 * (sg ε b * sg ε b)) * ha
      + (-(starRingEnd ℂ) (Z a b) / 2) * hb
  · intro a b
    have ha := sg_sq' ε a
    have hb := sg_sq' ε b
    simp only [barM, Matrix.of_apply, map_div₀, map_sub, map_neg, map_mul, conj_sg',
      Complex.conj_conj, map_ofNat, Complex.conj_I]
    linear_combination (-Complex.I * (starRingEnd ℂ) (Z a b) / 2 * (sg ε b * sg ε b)) * ha
      + (-Complex.I * (starRingEnd ℂ) (Z a b) / 2) * hb
  · ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination ((Z a b - (starRingEnd ℂ) (barM ε Z a b)) / 2) * Complex.I_mul_I

theorem dZ_add_smul {n : ℕ} (ε : Fin n → Bool) (A B : Mat n) (c : ℂ) :
    dZ ε (A + c • B) = dZ ε A + c • dZ ε B := by
  apply MvPolynomial.derivation_ext
  rintro (x | x)
  · simp only [dZ, Derivation.add_apply, Derivation.smul_apply, mkDerivation_X, Sum.elim_inl,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, smul_eq_C_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [dZ, Derivation.add_apply, Derivation.smul_apply, mkDerivation_X, Sum.elim_inr, barM,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_neg, smul_eq_C_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem adBas_add_smul {n : ℕ} (ε : Fin n → Bool) (A B : Mat n) (c : ℂ) (H : ℝ → ℝ)
    (P : GlobalTheory.PsCo.Pc1.Poly n) :
    adBas ε (A + c • B) H P = adBas ε A H P + c • adBas ε B H P := by
  funext g
  have hC : ev g (C c) = c := by simp [ev]
  simp only [adBas, bas, dZ_add_smul, Derivation.add_apply, Derivation.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_C_mul, map_add, map_mul, hC]
  ring

theorem adBas_mem_adSpanM  : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ)
    (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H →
    GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  intro n ε Z H P hH
  obtain ⟨A, B, hA, hB, rfl⟩ := lieU_decomposition ε Z
  rw [adBas_add_smul]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨A, H, P, hA, hH, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨B, H, P, hB, hH, rfl⟩))

end GlobalTheory.PsCo.Pc1
end

section

noncomputable section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open scoped ContDiff Topology

namespace GlobalTheory.PsCo.Pc1

theorem iteratedDeriv_scale_eq_zero {G : ℝ → ℝ} (hG : ∀ x, 1 ≤ x → G x = 0) {t : ℝ} (ht : 0 < t) (k : ℕ)
    {x : ℝ} (hx : 1 < t * x) : iteratedDeriv k (fun y => G (t * y)) x = 0 := by
  have hev : (fun y => G (t * y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    have hopen : IsOpen {y : ℝ | 1 < t * y} := isOpen_lt continuous_const (continuous_const.mul continuous_id)
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hG _ (le_of_lt hy)
  rw [hev.iteratedDeriv_eq k]
  simp [iteratedDeriv_const]

theorem isCutFn_iteratedDeriv_scale {G : ℝ → ℝ} (hGs : ContDiff ℝ ∞ G) (hG : ∀ x, 1 ≤ x → G x = 0) {t : ℝ}
    (ht : 0 < t) (k : ℕ) : IsCutFn (iteratedDeriv k (fun y => G (t * y))) := by
  refine ⟨?_, 2 / t, fun x hx => iteratedDeriv_scale_eq_zero hG ht k ?_⟩
  · rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv k (hGs.comp (contDiff_const.mul contDiff_id))
  · have : 2 ≤ t * x := by rwa [div_le_iff₀ ht, mul_comm] at hx
    linarith

theorem stFam : StFam := by
  intro n ε G p hG
  refine ⟨(Finset.range (nMode ε + 1)).sup fun k => (p k).totalDegree, fun k hk =>
    Finset.le_sup (f := fun k => (p k).totalDegree) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)), fun t ht => ⟨?_, ?_⟩⟩
  · have : famF ε G p t = ∑ k ∈ Finset.range (nMode ε + 1), bas ε (iteratedDeriv k fun x => G (t * x)) (p k) := by
      funext g; simp [famF, Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun k hk => Submodule.subset_span ⟨_, p k, isCutFn_iteratedDeriv_scale hG.1 hG.2.1 ht k,
      Finset.le_sup (f := fun k => (p k).totalDegree) hk, rfl⟩
  · intro g hg
    simp only [famF, bas]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [iteratedDeriv_scale_eq_zero hG.2.1 ht k hg]
    simp

end GlobalTheory.PsCo.Pc1
end
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.DMComm

variable {n : ℕ}

theorem barM_single (ε : Fin n → Bool) (x : Mode ε) :
    barM ε (Matrix.single x.1.2 x.1.1 1) = Matrix.single x.1.1 x.1.2 1 := by
  obtain ⟨⟨a, b⟩, ha, hb⟩ := x
  ext i j
  simp only [barM, Matrix.single_apply]
  by_cases h : b = j ∧ a = i
  · obtain ⟨rfl, rfl⟩ := h
    simp only at ha hb
    simp [sg, ha, hb]
  · have h' : ¬ (a = i ∧ b = j) := fun h2 => h ⟨h2.2, h2.1⟩
    simp [h, h']

theorem dM_inl (ε : Fin n → Bool) (x : Mode ε) (i j : Fin n) :
    dM ε x (X (Sum.inl (i, j))) = (if j = x.1.1 then X (Sum.inl (i, x.1.2)) else 0)
      - (if i = x.1.2 then X (Sum.inl (x.1.1, j)) else 0) := by
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inl, Finset.sum_sub_distrib]
  congr 1
  · by_cases h : j = x.1.1
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]
  · by_cases h : i = x.1.2
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]

theorem dM_inr (ε : Fin n → Bool) (x : Mode ε) (i j : Fin n) :
    dM ε x (X (Sum.inr (i, j))) = (if j = x.1.2 then X (Sum.inr (i, x.1.1)) else 0)
      - (if i = x.1.1 then X (Sum.inr (x.1.2, j)) else 0) := by
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inr, Finset.sum_sub_distrib, barM_single]
  congr 1
  · by_cases h : j = x.1.2
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]
  · by_cases h : i = x.1.1
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]

theorem mode_ne (ε : Fin n → Bool) (w x : Mode ε) : x.1.2 ≠ w.1.1 := by
  intro h
  have h1 := x.2.2
  rw [h, w.2.1] at h1
  exact absurd h1 (by simp)

theorem dM_comm_X (ε : Fin n → Bool) (w x : Mode ε) (v : (Fin n × Fin n) ⊕ (Fin n × Fin n)) :
    dM ε w (dM ε x (X v)) = dM ε x (dM ε w (X v)) := by
  have h1 := mode_ne ε w x
  have h2 := mode_ne ε x w
  have h3 := h1.symm
  have h4 := h2.symm
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [dM_inl, map_sub, apply_ite (dM ε w), apply_ite (dM ε x), map_zero, h1, h2, h3, h4, if_false]
    split_ifs <;> simp_all
  · simp only [dM_inr, map_sub, apply_ite (dM ε w), apply_ite (dM ε x), map_zero, h1, h2, h3, h4, if_false]
    split_ifs <;> simp_all

theorem dM_comm : GlobalTheory.PsCo.Cw2a.T_dM_comm := by
  intro n ε w x P
  have h : ⁅dM ε w, dM ε x⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, dM_comm_X, sub_self]
    rfl
  have h2 := congrArg (fun D : Derivation ℂ (Poly n) (Poly n) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using h2

end GlobalTheory.PsCo.DMComm
end

section

noncomputable section

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1

theorem stProfile_holds : StProfile := by
  intro N
  induction N with
  | zero =>
    refine ⟨fun x => expNegInvGlue (1 - x), ?_, ?_, ?_, ?_⟩
    · exact expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
    · intro x hx
      exact expNegInvGlue.zero_of_nonpos (by linarith)
    · intro x
      simpa using expNegInvGlue.nonneg _
    · simpa using expNegInvGlue.pos_of_pos (x := 1) one_pos
  | succ N ih =>
    obtain ⟨G, h1, h2, h3, h4⟩ := ih
    have hc : Continuous G := h1.continuous
    have hd : deriv (fun x => ∫ s in (1:ℝ)..x, G s) = G := by
      funext x
      exact (hc.deriv_integral G 1 x)
    refine ⟨fun x => ∫ s in (1:ℝ)..x, G s, ?_, ?_, ?_, ?_⟩
    · rw [contDiff_infty_iff_deriv, hd]
      exact ⟨fun x => (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).differentiableAt, h1⟩
    · intro x hx
      have : ∫ s in (1:ℝ)..x, G s = ∫ s in (1:ℝ)..x, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hx] at hs
        exact h2 s hs.1
      simpa using this
    · intro x
      rw [iteratedDeriv_succ', hd]
      exact h3 x
    · rw [iteratedDeriv_succ', hd]
      exact h4

end GlobalTheory.PsCo.Pc1
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

theorem HasQ.add {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ + g τ) (fun n => a n + b n) := by
  intro τ
  simpa only [add_mul] using (hf τ).add (hg τ)

theorem HasQ.sub {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ - g τ) (fun n => a n - b n) := by
  intro τ
  simpa only [sub_mul] using (hf τ).sub (hg τ)

theorem HasQ.const_mul {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (c : ℂ) (hf : HasQ N f a) :
    HasQ N (fun τ => c * f τ) (fun n => c * a n) := by
  intro τ
  simpa only [mul_assoc] using (hf τ).mul_left c

theorem HasQ.const (N : ℕ) (c : ℂ) :
    HasQ N (fun _ => c) (fun n => if n = 0 then c else 0) := by
  intro τ
  have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) 0
    (fun m hm => by simp [hm])
  simpa using h

theorem HasQ.sum {N : ℕ} {κ : Type*} (s : Finset κ) {f : κ → ℍ → ℂ} {a : κ → ℕ → ℂ}
    (h : ∀ k ∈ s, HasQ N (f k) (a k)) :
    HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n) := by
  intro τ
  simpa only [Finset.sum_mul] using hasSum_sum fun k hk => h k hk τ

theorem hasQ_linear : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by
  intro N
  exact ⟨fun f g a b hf hg => hf.add hg, fun f g a b hf hg => hf.sub hg,
    fun c f a hf => hf.const_mul c, fun c => HasQ.const N c, fun κ s f a h => HasQ.sum s h⟩

end GlobalTheory.QFam
end
