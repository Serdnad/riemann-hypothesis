module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle149
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

section

noncomputable section

open Complex MeasureTheory Set
open scoped FourierTransform

namespace GlobalTheory.HeckeTwo

lemma lipschitzOneVariableKernel_two_eq_indicator {y : ℝ} (hy : 0 < y) :
    GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ 1 * Complex.exp (-(((2 * Real.pi * y : ℝ) : ℂ) * t))) := by
  funext t
  have him : ((y : ℂ) * I).im = y := by simp
  simp only [GlobalTheory.LipschitzTR.phi1, Set.indicator, Set.mem_Ioi, him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases ht : 0 < t
  · rw [if_pos ht, if_pos ht, abs_of_pos ht]
    push_cast
    congr 2
    ring_nf
    rw [I_sq]
    ring
  · rw [if_neg ht, if_neg ht]

lemma norm_inv_ofReal_add_mul_I_sq (x y : ℝ) : ‖((x : ℂ) + (y : ℂ) * I)⁻¹ ^ 2‖ = (x ^ 2 + y ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma ofReal_add_ofReal_mul_I_ne_zero (x : ℝ) {y : ℝ} (hy : 0 < y) : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy.ne' this

theorem hTrans_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y =
    if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  intro ν y hy
  set g := GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) with hg
  have hw : ((y : ℂ) * I).im ≠ 0 := by simp [hy.ne']
  have hgc : Continuous g := GlobalTheory.LipschitzTR.continuous_lipschitzOneVariableKernel le_rfl hw
  have hgi : Integrable g := by
    rw [hg, lipschitzOneVariableKernel_two_eq_indicator hy, integrable_indicator_iff measurableSet_Ioi]
    exact GlobalTheory.LipschitzTR.integrableOn_pow_mul_cexp_neg 1 (by simp; positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hF : ∀ x : ℝ, 𝓕 g x = -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 := by
    intro x
    rw [hg, GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow 2 le_rfl even_two _ hw x]
    have hne := ofReal_add_ofReal_mul_I_ne_zero (-x) hy
    rw [zpow_neg, zpow_natCast]
    push_cast at hne ⊢
    have : (y : ℂ) * I - x = -(x : ℂ) + y * I := by ring
    rw [this]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hFi : Integrable (𝓕 g) := by
    have hb : Integrable (fun x : ℝ => ((4 * Real.pi ^ 2 * y ^ 2)⁻¹ : ℝ) * (1 + (x / y) ^ 2)⁻¹) :=
      (integrable_inv_one_add_sq.comp_div hy.ne').const_mul _
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    · rw [show (𝓕 g) = fun x : ℝ => -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 from funext hF]
      exact Continuous.aestronglyMeasurable
        (continuous_const.mul ((((continuous_ofReal.comp continuous_neg).add continuous_const).inv₀
          (fun x => ofReal_add_ofReal_mul_I_ne_zero (-x) hy)).pow 2))
    · rw [hF, norm_mul, norm_neg, norm_inv, norm_mul, norm_pow, norm_inv_ofReal_add_mul_I_sq]
      simp only [RCLike.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, neg_sq]
      have : y ≠ 0 := hy.ne'
      field_simp <;> ring
  have hinv : 𝓕 (𝓕⁻ g) = g := hgc.fourier_fourierInv_eq hgi hFi
  have hphi : ∀ t : ℝ, phi 0 ((t : ℂ) + (y : ℂ) * I) = -4 * (Real.pi : ℂ) ^ 2 * 𝓕⁻ g t := by
    intro t
    rw [Real.fourierInv_eq_fourier_neg, hF, neg_neg]
    unfold phi
    rw [mul_zero, Complex.cpow_zero, mul_one]
    field_simp
  have hT : hTrans 0 ν y = -4 * (Real.pi : ℂ) ^ 2 * 𝓕 (𝓕⁻ g) ν := by
    unfold hTrans
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1
    funext t
    rw [hphi t, smul_eq_mul]
    push_cast
    ring_nf
  rw [hT, hinv, hg]
  simp only [GlobalTheory.LipschitzTR.phi1]
  have him : ((y : ℂ) * I).im = y := by simp
  rw [him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases hν : 0 < ν
  · rw [if_pos hν, if_pos hν, abs_of_pos hν]
    push_cast
    ring_nf
    rw [I_sq]
    ring_nf
  · rw [if_neg hν, if_neg hν, mul_zero]

end GlobalTheory.HeckeTwo
end
end

section

open NumberField Complex
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeTwo

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem norm_phi_le (σ w : ℂ) (hσ : 0 < σ.re) (c : ℝ) (hc : 0 < c) (hcw : c ≤ |w.im|) :
    ‖phi σ w‖ ≤ ‖w⁻¹ ^ 2‖ * c ^ (-2 * σ.re) := by
  have hw : 0 < ‖w‖ := lt_of_lt_of_le hc (hcw.trans (Complex.abs_im_le_norm w))
  unfold phi
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : (-2 * σ).re = -2 * σ.re := by simp
  rw [hre]
  exact Real.rpow_le_rpow_of_nonpos hc (hcw.trans (Complex.abs_im_le_norm w)) (by linarith)

theorem summable_latSum (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : Frac F) (σ : ℂ)
    (hσ : 0 < σ.re) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) (b : F) (hb : b ≠ 0) :
    Summable (fun a : {a : F // a ∈ latM 𝔞} =>
      ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by
  classical
  have hM : latM 𝔞 ≠ 0 := by
    rw [latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero 𝔞)
  set z' : Emb F → ℂ := fun τ => ((τ b : ℝ) : ℂ) * z τ with hz'
  have hc : ∀ τ : Emb F, 0 < |τ b * (z τ).im| := fun τ =>
    abs_pos.2 (mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne')
  have him : ∀ τ : Emb F, (z' τ).im ≠ 0 := fun τ => by
    have := hc τ
    simp only [hz', Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact abs_pos.1 this
  have hs := GlobalTheory.LipschitzTR.summable_lhsTerm_ideal F (latM 𝔞) hM 2 le_rfl z' him
  have hs' : Summable (fun a : {a : F // a ∈ latM 𝔞} => GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1) := hs
  set C : ℝ := ∏ τ : Emb F, |τ b * (z τ).im| ^ (-2 * σ.re) with hC
  refine Summable.of_norm_bounded ((summable_norm_iff.2 hs').mul_left C) fun a => ?_
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1 =
      ∏ τ : Emb F, (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)⁻¹ ^ 2 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm
    rw [zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hz', inv_pow, add_comm]
  rw [hl, norm_prod, norm_prod, hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [mul_comm (|τ b * (z τ).im| ^ (-2 * σ.re))]
  refine norm_phi_le σ _ hσ _ (hc τ) (le_of_eq ?_)
  simp

end GlobalTheory.HeckeTwo
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoConst

variable {F : Type} [Field F] [NumberField F]

theorem exists_ideal (M : FractionalIdeal (𝓞 F)⁰ F) (N : Frac F) (hM : M * (N : FractionalIdeal (𝓞 F)⁰ F) = 1)
    (a : NZ M) : ∃ J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = ClassGroup.mk F N},
      ((J.1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * N := by
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * (N : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by
    rw [← hM]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 a.2.1) _
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hs : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 a.2.2
  have hI0 : I ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hs N.ne_zero (by rw [← hI]; simp)
  refine ⟨⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, ?_⟩, hI⟩
  have e : FractionalIdeal.mk0 F ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩ = Units.mk0 _ hs * N := by
    ext1
    rw [FractionalIdeal.coe_mk0]
    exact hI
  rw [← ClassGroup.mk_mk0 F, e, map_mul, ClassGroup.mk_eq_one_iff.2, one_mul]
  rw [FractionalIdeal.isPrincipal_iff]
  exact ⟨a.1, rfl⟩

theorem exists_equiv (M : FractionalIdeal (𝓞 F)⁰ F) (N : Frac F) (hM : M * (N : FractionalIdeal (𝓞 F)⁰ F) = 1) :
    ∃ e : Quotient (unitRel M) ≃ {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = ClassGroup.mk F N}, ∀ c,
      (((e c).1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ c.out.1 * N := by
  choose f hf using exists_ideal M N hM
  have key : ∀ a b : NZ M, (unitRel M).r a b ↔
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 := by
    intro a b
    rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
    refine exists_congr fun ε => ?_
    rw [Units.smul_def, Algebra.smul_def]
    exact eq_comm
  refine ⟨Equiv.ofBijective (fun c => f c.out) ⟨?_, ?_⟩, fun c => hf _⟩
  · intro c c' h
    have h1 := hf c.out
    simp only at h
    rw [h, hf] at h1
    have h2 := (key _ _).2 (mul_right_cancel₀ N.ne_zero h1).symm
    rw [← c.out_eq, ← c'.out_eq]
    exact Quotient.sound h2
  · rintro ⟨J, hJ⟩
    have h1 : ClassGroup.mk F (FractionalIdeal.mk0 F J * N⁻¹) = 1 := by
      rw [map_mul, map_inv, ClassGroup.mk_mk0, hJ, mul_inv_cancel]
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at h1
    obtain ⟨a, ha⟩ := h1
    have ha0 : a ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.1 (ha ▸ Units.ne_zero _)
    have hMN : M = ((N⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left hM
    rw [Units.val_mul, FractionalIdeal.coe_mk0, ← hMN] at ha
    have haM : a ∈ M := by
      rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← ha]
      conv_rhs => rw [← one_mul M]
      exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
    refine ⟨Quotient.mk _ ⟨a, haM, ha0⟩, ?_⟩
    have h2 : (unitRel M).r (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out ⟨a, haM, ha0⟩ :=
      Quotient.exact (Quotient.out_eq _)
    have h3 := hf (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out
    rw [(key _ _).1 h2] at h3
    simp only at h3
    rw [← ha, mul_assoc, hM, mul_one] at h3
    exact Subtype.ext (Subtype.ext (FractionalIdeal.coeIdeal_injective h3))

theorem card_emb [IsTotallyReal F] : Fintype.card (Emb F) = Module.finrank ℚ F := by
  have h := prod_emb (F := F) (algebraMap ℚ F 2)
  rw [Algebra.norm_algebraMap] at h
  simp only [map_ofNat, Finset.prod_const, Finset.card_univ] at h
  have h' : (2 : ℕ) ^ Fintype.card (Emb F) = 2 ^ Module.finrank ℚ F := by exact_mod_cast h
  exact Nat.pow_right_injective le_rfl h'

theorem eisTerm_zero [IsTotallyReal F] (a : F) :
    eisTerm 2 0 0 (a, 0) = ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F *
      (((|Algebra.norm ℚ a| : ℚ) : ℂ))⁻¹ ^ 2 := by
  have h1 : ∏ τ, latPt (0 : Emb F → ℂ) (a, 0) τ =
      (2 * (Real.pi : ℂ) * I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [← prod_emb, ← card_emb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [latPt]
  have h2 : (((|Algebra.norm ℚ a| : ℚ) : ℂ))⁻¹ ^ 2 = ((Algebra.norm ℚ a : ℚ) : ℂ)⁻¹ ^ 2 := by
    rw [inv_pow, inv_pow, ← Rat.cast_pow, sq_abs, Rat.cast_pow]
  unfold eisTerm
  rw [h1, h2, mul_zero, cpow_zero, mul_one, mul_inv, mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm 2 (Module.finrank ℚ F)]

theorem aPart_zero [IsTotallyReal F] (𝔞 : Frac F) (C : ClassGroup (𝓞 F)) (D : (Ideal (𝓞 F))⁰) (Za : ℂ → ℂ)
    (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F)) (hC : C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D)
    (hZ : IsPartialZeta C Za) :
    aPart 𝔞 0 = ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F * ((dF F : ℂ) * (nrm 𝔞 : ℂ)) ^ 2 * Za 2 := by
  set N : Frac F := FractionalIdeal.mk0 F D * 𝔞 with hN
  have hCN : C = ClassGroup.mk F N := by
    rw [hN, map_mul, ClassGroup.mk_mk0, ← hC, inv_mul_cancel_right]
  have hM : latM 𝔞 * (N : FractionalIdeal (𝓞 F)⁰ F) = 1 := by
    have := (FractionalIdeal.mk0 F D).ne_zero
    rw [FractionalIdeal.coe_mk0] at this
    rw [latM, hN, ← hD, Units.val_mul, FractionalIdeal.coe_mk0, Units.val_inv_eq_inv_val, ← mul_inv,
      inv_mul_cancel₀ (mul_ne_zero this 𝔞.ne_zero)]
  have hnN : ((FractionalIdeal.absNorm (N : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℂ) = (dF F : ℂ) * (nrm 𝔞 : ℂ) := by
    rw [hN, Units.val_mul, FractionalIdeal.coe_mk0, map_mul, FractionalIdeal.coeIdeal_absNorm, hD,
      absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, dF, nrm, ← Int.cast_abs,
      Rat.cast_mul, Rat.cast_intCast, ofReal_intCast, ofReal_ratCast]
  have hn0 : (dF F : ℂ) * (nrm 𝔞 : ℂ) ≠ 0 := by
    rw [← hnN]
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 N.ne_zero)
  subst hCN
  obtain ⟨e, he⟩ := exists_equiv _ N hM
  have hs := (e.hasSum_iff.2 (hZ.2 2 (by norm_num))).mul_left
    (((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F * ((dF F : ℂ) * (nrm 𝔞 : ℂ)) ^ 2)
  rw [← hs.tsum_eq, aPart]
  refine tsum_congr fun c => ?_
  have h1 := congrArg (fun I => ((FractionalIdeal.absNorm I : ℚ) : ℂ)) (he c)
  simp only [map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, hnN,
    Rat.cast_natCast] at h1
  rw [eisTerm_zero, Function.comp_apply, h1, cpow_neg, cpow_two]
  generalize (dF F : ℂ) * (nrm 𝔞 : ℂ) = x at hn0 ⊢
  generalize ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F = y
  rw [mul_pow, mul_inv, inv_pow, mul_assoc, mul_left_comm (x ^ 2), mul_inv_cancel₀ (pow_ne_zero 2 hn0), mul_one]

theorem gammaR_two : Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
  rw [Gammaℝ_def, show (2 : ℂ) / 2 = 1 by norm_num, show -(2 : ℂ) / 2 = -1 by norm_num, Complex.Gamma_one, cpow_neg_one,
    mul_one]

theorem gammaR_neg_one : Gammaℝ (-1) = -2 * (Real.pi : ℂ) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := Gammaℝ_add_two (s := -1) (by norm_num)
  rw [show (-1 : ℂ) + 2 = 1 by norm_num, Gammaℝ_one] at h
  field_simp at h
  linear_combination h

theorem constant_term : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (C : ClassGroup (NumberField.RingOfIntegers F)) (D : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F))) (Za Za' : ℂ → ℂ), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) → C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Za → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Za' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Za s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Za' (1 - s)) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * GlobalTheory.HeckeTwo.aPart 𝔞 0 / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Za' (1 - ((2 : ℕ) : ℂ)) := by
  intro F _ _ _ 𝔞 C D Za Za' hD hC hZ _ hfe
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfe2 := hfe 2 (fun n h => by
      have h' : (2 : ℤ) = -2 * n := by exact_mod_cast h
      omega) (fun n h => by
      have h' : (1 - 2 : ℤ) = -2 * n := by exact_mod_cast h
      omega)
  have hd : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hn : (nrm 𝔞 : ℂ) ≠ 0 := by
    rw [nrm]
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 𝔞.ne_zero)
  set r : ℝ := dF F ^ ((1 : ℝ) / 2) with hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hd _).ne'
  have hrr : (dF F : ℂ) = (r : ℂ) ^ 2 := by
    have : dF F = r ^ 2 := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]; norm_num
    exact_mod_cast this
  have hc : cK F 2 = r := by
    rw [cK, hr]; norm_num
  have hneg : (dF F : ℂ) ^ ((-1 : ℂ) / 2) = (r : ℂ)⁻¹ := by
    rw [hr, ofReal_cpow hd.le, ← cpow_neg]
    congr 1
    push_cast; ring
  rw [show (1 : ℂ) - 2 = -1 by norm_num, show (2 : ℂ) / 2 = 1 by norm_num, cpow_one, hneg, gammaR_two,
    gammaR_neg_one] at hfe2
  rw [show (1 : ℂ) - ((2 : ℕ) : ℂ) = -1 by norm_num, aPart_zero 𝔞 C D Za hD hC hZ, hc, omegaFactor, ← hr]
  have hI : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 = 2⁻¹ * (Real.pi : ℂ)⁻¹ * (-2 * (Real.pi : ℂ))⁻¹ := by
    rw [inv_pow, mul_pow, I_sq]; field_simp
  have hg : (-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hπ)
  rw [hI, mul_pow, mul_pow, inv_pow (-2 * (Real.pi : ℂ)), hrr]
  rw [hrr] at hfe2
  generalize (-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F = g at hg hfe2
  generalize ((Real.pi : ℂ)⁻¹) ^ Module.finrank ℚ F = p at hfe2
  generalize ((2 : ℂ)⁻¹) ^ Module.finrank ℚ F = t
  push_cast
  field_simp at hfe2 ⊢
  linear_combination t * hfe2

end GlobalTheory.HeckeTwoConst
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

lemma ofReal_add_I_ne_zero (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma norm_inv_ofReal_add_I_sq (t : ℝ) : ‖((t : ℂ) + I)⁻¹ ^ 2‖ = (1 + t ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma tendsto_inv_ofReal_add_I_atTop :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)⁻¹) Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)) Filter.atTop (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_abs_atTop_atTop
    have := Complex.abs_re_le_norm ((t : ℂ) + I)
    simpa using this
  exact Filter.Tendsto.comp Filter.tendsto_inv₀_cobounded hb

lemma tendsto_inv_ofReal_add_I_atBot :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)⁻¹) Filter.atBot (nhds 0) := by
  have hb : Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)) Filter.atBot (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_abs_atBot_atTop
    have := Complex.abs_re_le_norm ((t : ℂ) + I)
    simpa using this
  exact Filter.Tendsto.comp Filter.tendsto_inv₀_cobounded hb

lemma hasDerivAt_neg_inv_ofReal_add_I (t : ℝ) :
    HasDerivAt (fun s : ℝ => -((s : ℂ) + I)⁻¹) (((t : ℂ) + I)⁻¹ ^ 2) t := by
  have h1 : HasDerivAt (fun w : ℂ => w + I) 1 (t : ℂ) := (hasDerivAt_id _).add_const I
  have h2 := (h1.inv (ofReal_add_I_ne_zero t)).neg
  have h3 := h2.comp_ofReal
  convert (preTransparency := .reducible) h3 using 1
  · funext s
    simp
  · rw [inv_pow]
    field_simp

lemma integral_inv_ofReal_add_I_sq : ∫ t : ℝ, ((t : ℂ) + I)⁻¹ ^ 2 = 0 := by
  have hint : MeasureTheory.Integrable (fun t : ℝ => ((t : ℂ) + I)⁻¹ ^ 2) := by
    refine integrable_inv_one_add_sq.mono' ?_ ?_
    · exact (((continuous_ofReal.add continuous_const).inv₀ ofReal_add_I_ne_zero).pow 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => (norm_inv_ofReal_add_I_sq t).le)
  rw [MeasureTheory.integral_of_hasDerivAt_of_tendsto hasDerivAt_neg_inv_ofReal_add_I hint
    (by simpa using tendsto_inv_ofReal_add_I_atBot.neg)
    (by simpa using tendsto_inv_ofReal_add_I_atTop.neg)]
  simp

theorem cConst_zero : cConst 0 = 0 := by
  unfold cConst hTrans phi
  simp only [mul_zero, neg_zero, Complex.cpow_zero, mul_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, one_mul]
  exact integral_inv_ofReal_add_I_sq

end GlobalTheory.HeckeTwo
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem sec_finite_flat (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) :
    Module.Finite Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) ∧ Module.Flat Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) := by
  obtain ⟨h1, h2, -⟩ := y.2.2
  haveI : IsFinite (subStr A B y) := h1
  haveI : Flat (subStr A B y) := h2
  constructor
  · exact IsFinite.finite_app (subStr A B y) W W.2
  · have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage (subStr A B y)
    have h := Scheme.Hom.flat_appLE (subStr A B y) W.2 hV le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at h
    exact h

end GlobalTheory.HilbAff
end
