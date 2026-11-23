module

import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvaluesOfNewton
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle054
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem hahnSeries_order_eq_neg_one_of_coeff {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (h0 : ∀ r : ℚ, r < -1 → h.coeff r = 0) : h.order = -1 := by
  have h1' : h.coeff (-1) ≠ 0 := by rw [h1]; exact one_ne_zero
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1'
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1') ?_
  exact le_of_not_gt fun hlt => hne (HahnSeries.coeff_order_eq_zero.mp (h0 _ hlt))

theorem hahnSeries_pow_order_of_order_neg_one {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (ho : h.order = -1) (n : ℕ) :
    (h ^ n).order = -(n : ℚ) ∧ (h ^ n).coeff (-(n : ℚ)) = 1 := by
  have hord : ∀ k : ℕ, (h ^ k).order = -(k : ℚ) := fun k => by
    rw [HahnSeries.order_pow, ho]
    simp
  refine ⟨hord n, ?_⟩
  induction n with
  | zero => simp
  | succ k ih =>

    have hm := HahnSeries.coeff_mul_order_add_order (h ^ k) h
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord k, ho, ih, h1, mul_one] at hm
    have e : -((k + 1 : ℕ) : ℚ) = -(k : ℚ) + -1 := by push_cast; ring
    rw [pow_succ, e, hm]

private theorem hahnSeries_coeff_algebra_smul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (r : Ω) (y : HahnSeries ℚ Ω) (a : ℚ) :
    (@HSMul.hSMul Ω (HahnSeries ℚ Ω) (HahnSeries ℚ Ω) (@instHSMul _ _ Algebra.toSMul) r y).coeff a =
      r * y.coeff a := by
  rw [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

theorem Tower.jK_transcendental {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  apply GlobalTheory.K4.jK_transcendental <;> assumption

end GlobalTheory.KZ
end

section

namespace GlobalTheory.IwahoriEigenObj

theorem iwahoriEigenvalues : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues :=
  GlobalTheory.IwahoriEigen.iwahoriEigenvalues

end GlobalTheory.IwahoriEigenObj
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral : ∀ (c M a : ℕ), 0 < M → a < M → ∃ k : ℤ, ∀ b : ℕ, admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ A : ℕ → ℂ, HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A ∧ A 0 ≠ 0 ∧ (∀ n, A n ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) ∧ (Nat.Coprime c M → ∀ n, A n ∈ Subring.closure {ee (1 / (M : ℂ))}) ∧ (b = 0 → ∀ n, ∃ z : ℤ, A n = z) := by
  first | exact @GlobalTheory.SiegQ.sg_expansion_int | exact GlobalTheory.SiegQ.sg_expansion_int | (intros; apply GlobalTheory.SiegQ.sg_expansion_int <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq : ∀ (N : ℕ) (d : ℤ) (u : (ZMod N)ˣ), (u : ZMod N) = d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' ↔ dg u * redGL N γ' = redGL N γ * dg u := by
  first | exact @GlobalTheory.FNCong.cong_iff_dg | exact GlobalTheory.FNCong.cong_iff_dg | (intros; apply GlobalTheory.FNCong.cong_iff_dg <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HkInv
open GlobalTheory.HeckeFamilyMatrices

theorem reps (N l q : ℕ) (σ γ : SL(2, ℤ)) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ)
    (hγ : γ ∈ GlobalTheory.Hk.lev N l) (i : Fin (q + 1)) :
    ∃ i' : Fin (q + 1), ∃ γ' ∈ GlobalTheory.Hk.lev N l, tqFam q σ i * mat γ = mat γ' * tqFam q σ i' := by
  by_cases hi : (i : ℕ) < q
  · have e : tqFam q σ i = !![(1 : ℤ), ((i : ℕ) : ℤ); 0, (q : ℤ)] := by rw [tqFam, if_pos hi]
    rw [e]
    by_cases hd : (q : ℤ) ∣ mat γ 0 0 + ((i : ℕ) : ℤ) * mat γ 1 0
    · obtain ⟨γ', h1, h2⟩ := GlobalTheory.T.upper_mul_eq_mul_diamond_diag_gamma1InterGamma0 N l q i σ γ hq hqN hσ hi hγ hd
      refine ⟨Fin.last q, γ', h1, ?_⟩
      rw [h2, tqFam, if_neg (by simp)]
    · obtain ⟨j', hj', γ', h1, h2⟩ := GlobalTheory.T.upperTriangular_mul_eq_mul_upperTriangular_gamma1InterGamma0 N l q i γ hq hqN hi hγ hd
      refine ⟨⟨j', by omega⟩, γ', h1, ?_⟩
      rw [h2, tqFam, if_pos (by simpa using hj')]
  · have e : tqFam q σ i = mat σ * dg q 1 := by rw [tqFam, if_neg hi]
    rw [e]
    by_cases hd : (q : ℤ) ∣ mat γ 1 0
    · obtain ⟨γ', h1, h2⟩ := GlobalTheory.T.diamond_diag_mul_eq_mul_of_dvd_lowerLeft_gamma1InterGamma0 N l q σ γ hq hqN hσ hγ hd
      refine ⟨Fin.last q, γ', h1, ?_⟩
      rw [h2, tqFam, if_neg (by simp)]
    · obtain ⟨j', hj', γ', h1, h2⟩ := GlobalTheory.T.diamond_diag_mul_eq_mul_upperTriangular_of_not_dvd_lowerLeft N l q σ γ hq hqN hσ hγ hd
      refine ⟨⟨j', by omega⟩, γ', h1, ?_⟩
      rw [h2, tqFam, if_pos (by simpa using hj')]

theorem perm (N l q : ℕ) (σ γ : SL(2, ℤ)) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ)
    (hγ : γ ∈ GlobalTheory.Hk.lev N l) :
    ∃ π : Equiv.Perm (Fin (q + 1)), ∀ i, ∃ γ' ∈ GlobalTheory.Hk.lev N l,
      tqFam q σ i * mat γ = mat γ' * tqFam q σ (π i) := by
  choose π g hg he using reps N l q σ γ hq hqN hσ hγ
  have hinj : Function.Injective π := by
    intro i₁ i₂ h
    have e1 := he i₁
    have e2 := he i₂
    rw [h] at e1
    apply GlobalTheory.T.heckeTqRepresentatives_cosets_distinct q σ (g i₁ * (g i₂)⁻¹) i₁ i₂ hq
    have hγi : mat γ * mat γ⁻¹ = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgi : mat (g i₂)⁻¹ * mat (g i₂) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc tqFam q σ i₁ = tqFam q σ i₁ * mat γ * mat γ⁻¹ := by rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
      _ = mat (g i₁) * (mat (g i₂)⁻¹ * (mat (g i₂) * tqFam q σ (π i₂))) * mat γ⁻¹ := by
          rw [e1, ← Matrix.mul_assoc (mat (g i₂)⁻¹), hgi, Matrix.one_mul]
      _ = mat (g i₁ * (g i₂)⁻¹) * (tqFam q σ i₂ * mat γ * mat γ⁻¹) := by
          rw [← e2, show mat (g i₁ * (g i₂)⁻¹) = mat (g i₁) * mat (g i₂)⁻¹ from Matrix.SpecialLinearGroup.coe_mul _ _]
          simp only [Matrix.mul_assoc]
      _ = mat (g i₁ * (g i₂)⁻¹) * tqFam q σ i₂ := by rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
  exact ⟨Equiv.ofBijective π hinj.bijective_of_finite, fun i => ⟨g i, hg i, he i⟩⟩

theorem det_tqFam (q : ℕ) (hq : 0 < q) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : (tqFam q σ i).det ≠ 0 := by
  unfold tqFam
  split_ifs
  · simp [Matrix.det_fin_two_of, hq.ne']
  · rw [Matrix.det_mul]; simp [dg, Matrix.det_fin_two_of, hq.ne']

theorem heckeT_slash_invariant : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → (∀ γ ∈ GlobalTheory.Hk.lev N l, f ∣[k] γ = f) →
    ∀ γ ∈ GlobalTheory.Hk.lev N l, GlobalTheory.Hk.heckeT k q σ f ∣[k] γ = GlobalTheory.Hk.heckeT k q σ f := by
  intro N l q k σ f _ hq hqN hσ hf γ hγ
  obtain ⟨π, hπ⟩ := perm N l q σ γ hq hqN hσ hγ
  have hq0 := hq.pos
  have hmat : (mat γ).det ≠ 0 := by simp [mat]
  rw [← GlobalTheory.SlashUpperTriangularMatrices.tq_eq k q σ f hq0, TqF, hkF]
  have key : ∀ i, (f ∣[k] toGL (tqFam q σ i)) ∣[k] γ = f ∣[k] toGL (tqFam q σ (π i)) := by
    intro i
    obtain ⟨γ', hγ', he⟩ := hπ i
    have hmat' : (mat γ').det ≠ 0 := by simp [mat]
    rw [ModularForm.SL_slash, ← SlashAction.slash_mul, ← GlobalTheory.SlashUpperTriangularMatrices.toGL_SL,
      ← GlobalTheory.SlashUpperTriangularMatrices.toGL_mul _ _ (det_tqFam q hq0 σ i) hmat, he,
      GlobalTheory.SlashUpperTriangularMatrices.toGL_mul _ _ hmat' (det_tqFam q hq0 σ _), SlashAction.slash_mul,
      GlobalTheory.SlashUpperTriangularMatrices.toGL_SL, ← ModularForm.SL_slash, hf γ' hγ']
  have hsum : ∀ (s : Finset (Fin (q + 1))) (F : Fin (q + 1) → ℍ → ℂ),
      (∑ i ∈ s, F i) ∣[k] γ = ∑ i ∈ s, F i ∣[k] γ := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simp [SlashAction.zero_slash]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  rw [hsum, Finset.sum_congr rfl (fun i _ => key i)]
  exact Equiv.sum_comp π (fun i => f ∣[k] toGL (tqFam q σ i))

end GlobalTheory.HkInv
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.dia k σ ⇑f := by
  first | exact @GlobalTheory.Hk.dia_cuspForm | exact GlobalTheory.Hk.dia_cuspForm | (intros; apply GlobalTheory.Hk.dia_cuspForm <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem sum_range_mul_eq (h : ℕ → ℂ) (q r : ℕ) :
    ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range q, h (j + q * i) = ∑ m ∈ Finset.range (q * r), h m := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.add_comm]

theorem im_div_pos (τ : ℍ) (j q : ℕ) (hq : 0 < q) : 0 < (((τ : ℂ) + j) / q).im := by
  rw [Complex.div_natCast_im]
  simp only [Complex.add_im, Complex.natCast_im, add_zero]
  exact div_pos τ.im_pos (by exact_mod_cast hq)

theorem uOp_uOp_eq (f : ℍ → ℂ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (τ : ℍ) :
    uOp a (uOp b f) τ =
      ((a : ℂ) * b)⁻¹ * ∑ m ∈ Finset.range (a * b), f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b))) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [uOp]
  rw [← sum_range_mul_eq (fun m : ℕ => f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b)))) a b]
  conv_rhs => rw [Finset.sum_comm]
  rw [mul_inv, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofComplex_apply_of_im_pos (im_div_pos τ j a ha)]
  congr 2
  push_cast
  field_simp
  ring

theorem uOp_comm (f : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    uOp q (uOp r f) = uOp r (uOp q f) := by
  funext τ
  rw [uOp_uOp_eq f q r hq hr, uOp_uOp_eq f r q hr hq, mul_comm (r : ℂ), Nat.mul_comm r q]

theorem sum_mul_mod (G : ℕ → ℂ) (q r : ℕ) (hq : 0 < q) (hc : Nat.Coprime q r) :
    ∑ j ∈ Finset.range q, G (r * j % q) = ∑ j ∈ Finset.range q, G j := by
  have hinj : Set.InjOn (fun j => r * j % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h1 : a ≡ b [MOD q] := Nat.ModEq.cancel_left_of_coprime hc hab
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  have himg : (Finset.range q).image (fun j => r * j % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨a, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image hinj, himg]

theorem per_ofComplex (g : ℍ → ℂ) (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) (z : ℂ) (hz : 0 < z.im) :
    g (ofComplex (z + 1)) = g (ofComplex z) := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  have h1 : ofComplex (z + 1) = (1 : ℝ) +ᵥ ofComplex z := by
    apply UpperHalfPlane.ext
    rw [coe_vadd, ofComplex_apply_of_im_pos hz1, ofComplex_apply_of_im_pos hz]
    push_cast
    ring
  rw [h1, hper]

theorem uOp_vOp (g : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hc : Nat.Coprime q r)
    (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) :
    uOp q (vOp r g) = vOp r (uOp q g) := by
  funext τ
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hw : 0 < ((r : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hr) τ.im_pos
  simp only [uOp, vOp]
  rw [ofComplex_apply_of_im_pos hw]
  congr 1
  set w : ℂ := (r : ℂ) * τ with hwdef
  set G : ℕ → ℂ := fun m => g (ofComplex ((w + m) / q)) with hG
  have hGq : ∀ m n : ℕ, G (m + q * n) = G m := by
    intro m n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih]
      simp only [hG]
      have hpos : 0 < ((w + ((m + q * n : ℕ) : ℂ)) / q).im := by
        rw [Complex.div_natCast_im]
        simp only [Complex.add_im, Complex.natCast_im, add_zero]
        exact div_pos hw (by exact_mod_cast hq)
      rw [← per_ofComplex g hper _ hpos]
      congr 2
      push_cast
      field_simp
      ring
  have hmod : ∀ m, G m = G (m % q) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m q]
    exact hGq _ _
  calc ∑ j ∈ Finset.range q, g (ofComplex ((r : ℂ) * ↑(ofComplex (((τ : ℂ) + j) / q))))
      = ∑ j ∈ Finset.range q, G (r * j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hG]
        rw [ofComplex_apply_of_im_pos (im_div_pos τ j q hq)]
        congr 2
        rw [hwdef]
        push_cast
        field_simp
    _ = ∑ j ∈ Finset.range q, G (r * j % q) := Finset.sum_congr rfl fun j _ => hmod _
    _ = ∑ j ∈ Finset.range q, G j := sum_mul_mod G q r hq hc
    _ = _ := rfl

theorem uOp_add (q : ℕ) (f g : ℍ → ℂ) : uOp q (f + g) = uOp q f + uOp q g := by
  funext τ
  simp [uOp, Finset.sum_add_distrib, mul_add]

theorem uOp_smul (q : ℕ) (c : ℂ) (f : ℍ → ℂ) : uOp q (c • f) = c • uOp q f := by
  funext τ
  simp [uOp, Finset.mul_sum, mul_left_comm]

theorem T_mem_lev (N l : ℕ) : ModularGroup.T ∈ lev N l := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp [ModularGroup.T]
  · rw [Gamma0_mem]
    simp [ModularGroup.T]

theorem uOp_heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    r.Prime → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l r σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.uOp q (GlobalTheory.Hk.heckeT k r σ ⇑f) = GlobalTheory.Hk.heckeT k r σ (GlobalTheory.Hk.uOp q ⇑f) := by
  intro N l q r k σ hN hl hq hqd hr hrd hσ f
  have hq0 : 0 < q := hq.pos
  have hr0 : 0 < r := hr.pos
  have hne : q ≠ r := fun h => hrd (h ▸ hqd)
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hne
  have hinv : ∀ γ ∈ lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ => by
    rw [SL_slash]; exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  have hper : ∀ τ : ℍ, ((⇑f) ∣[k] σ) ((1 : ℝ) +ᵥ τ) = ((⇑f) ∣[k] σ) τ := by
    intro τ
    have h1 : ((⇑f) ∣[k] σ) ∣[k] ModularGroup.T = (⇑f) ∣[k] σ := by
      have e : σ * ModularGroup.T = (σ * ModularGroup.T * σ⁻¹) * σ := by group
      rw [← SlashAction.slash_mul, e, SlashAction.slash_mul,
        hinv _ (isDia_conj_mem_lev N l r σ _ hσ (T_mem_lev N l))]
    have h2 := congr_fun h1 τ
    have hden : denom (ModularGroup.T : GL (Fin 2) ℝ) τ = 1 := by
      rw [denom]; simp [ModularGroup.coe_T]
    rw [SL_slash_apply, modular_T_smul] at h2
    simpa [hden] using h2
  have hd := GlobalTheory.T.heckeUOperatorExplicit_comm_diamondOperatorOfMatrix N l q k r σ hN hl hq hqd hσ f
  unfold GlobalTheory.Hk.dia at hd
  simp only [GlobalTheory.Hk.heckeT]
  rw [uOp_add, uOp_smul, uOp_comm _ q r hq0 hr0, uOp_vOp _ q r hq0 hr0 hcop hper, hd]

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma petersson_smul_of_mem {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f g : CuspForm Γ k) {h : SL(2, ℤ)}
    (hh : h ∈ Γ) (τ : ℍ) : petersson k ⇑f ⇑g (h • τ) = petersson k ⇑f ⇑g τ := by
  have hf : (⇑f ∣[k] h) = ⇑f := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn f _ ⟨h, hh, rfl⟩
  have hg : (⇑g ∣[k] h) = ⇑g := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn g _ ⟨h, hh, rfl⟩
  rw [← petersson_slash_SL, hf, hg]

def cosetShift (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ))
    (h₁ : ∀ γ ∈ Γ, σ * γ * σ⁻¹ ∈ Γ) (h₂ : ∀ γ ∈ Γ, σ⁻¹ * γ * σ ∈ Γ) :
    SL(2, ℤ) ⧸ Γ ≃ SL(2, ℤ) ⧸ Γ where
  toFun := Quotient.map' (· * σ⁻¹) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₁ _ hab
  invFun := Quotient.map' (· * σ) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₂ _ hab
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

theorem pet_dia_dia : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → GlobalTheory.Hk.IsDia N l d σ →
    ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.dia k σ ⇑f) (GlobalTheory.Hk.dia k σ ⇑g) =
        GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g := by
  intro N l k d σ _ _ hσ f g
  have h₁ : ∀ γ ∈ lev N l, σ * γ * σ⁻¹ ∈ lev N l := fun γ hγ => GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level N l d σ γ hσ hγ
  have hσ' : IsDia N l (σ 0 0) σ⁻¹ := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl, hσ.1]
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  have h₂ : ∀ γ ∈ lev N l, σ⁻¹ * γ * σ ∈ lev N l := fun γ hγ => by
    simpa using GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level N l _ σ⁻¹ γ hσ' hγ
  set e := cosetShift (lev N l) σ h₁ h₂
  unfold pet
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun γ => ?_
  congr 1
  funext z
  have he : e γ = QuotientGroup.mk (γ.out * σ⁻¹) := by
    conv_lhs => rw [← QuotientGroup.out_eq' γ]
    rfl
  have hx : (QuotientGroup.mk (e γ).out : SL(2, ℤ) ⧸ lev N l) = QuotientGroup.mk (γ.out * σ⁻¹) := by
    rw [QuotientGroup.out_eq', he]
  have hmem := QuotientGroup.eq.mp hx.symm
  have hinv : (e γ).out⁻¹ = ((γ.out * σ⁻¹)⁻¹ * (e γ).out)⁻¹ * (σ * γ.out⁻¹) := by group
  rw [hinv, mul_smul, petersson_smul_of_mem f g (inv_mem hmem), dia, dia, petersson_slash_SL,
    mul_smul]

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem dia_congr : ∀ (N l : ℕ) (k d : ℤ) (σ τ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    GlobalTheory.Hk.IsDia N l d τ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.dia k σ ⇑f = GlobalTheory.Hk.dia k τ ⇑f := by
  intro N l k d σ τ hN hσ hτ f
  have h := GlobalTheory.T.diamond_mul_inv_mem_gamma1InterGamma0Level N l d σ τ hN hσ hτ
  have hτ' : τ = (τ * σ⁻¹) * σ := by group
  have hinv : ⇑f ∣[k] (τ * σ⁻¹) = ⇑f :=
    SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ h)
  unfold GlobalTheory.Hk.dia
  rw [hτ', SlashAction.slash_mul, hinv]

end GlobalTheory.Hk
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.kroneckerHeckeProduct_invariant_principal_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M q : ℕ) (σ : SL(2, ℤ)) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  first | exact @GlobalTheory.kronecker_product_level | exact GlobalTheory.kronecker_product_level | (intros; apply GlobalTheory.kronecker_product_level <;> assumption)
end
