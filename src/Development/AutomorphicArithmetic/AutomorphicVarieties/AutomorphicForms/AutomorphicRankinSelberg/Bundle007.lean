module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace UpperTheory.V.Af.Rs

private theorem cls_rep (hR : RowRep) (L : ℕ) [NeZero L] (v : Fin 2 → ZMod L) :
    ∃ (n : ℕ) (γ : SL(2, ℤ)), v = cls L ((n : ℤ) • row γ) := by
  obtain ⟨n, γ, h⟩ := hR (fun i => ((v i).val : ℤ))
  refine ⟨n, γ, ?_⟩
  rw [← h]
  funext i
  simp [cls]

private theorem cls_smul (L : ℕ) (m n : ℕ) (x : Fin 2 → ℤ) :
    (m : ZMod L) • cls L ((n : ℤ) • x) = cls L (((m * n : ℕ) : ℤ) • x) := by
  funext i
  simp only [cls, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem norm_char_le {L : ℕ} [NeZero L] (ψ : DirichletCharacter ℂ L) (a : ZMod L) : ‖ψ a‖ ≤ 1 :=
  ψ.norm_le_one a

end UpperTheory.V.Af.Rs

theorem UpperTheory.V.Af.Rs.clsProp :
    UpperTheory.V.Af.Rs.RowRep → UpperTheory.V.Af.Rs.ClsProp := by
  intro hR L _ ψ F G hG
  have hscale : ∀ (a : ZMod L) (v : Fin 2 → ZMod L) (z : ℍ), G (a • v) z = ψ a * G v z := by
    intro a v z
    obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
    rw [← ZMod.natCast_zmod_val a, cls_smul, hG, hG]
    push_cast
    rw [map_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hFc, C, hC⟩
    refine ⟨?_, C, ?_⟩
    · intro v
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      have hγ : Continuous (fun z : ℍ => γ • z) :=
        continuous_const_smul (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
      have : (fun z => G (cls L ((n : ℤ) • row γ)) z) = fun z => ψ n * F (γ • z) := by
        funext z; exact hG n γ z
      change Continuous (fun z => G (cls L ((n : ℤ) • row γ)) z)
      rw [this]
      exact continuous_const.mul (hFc.comp hγ)
    · intro v z hz
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      rw [hG, norm_mul, mul_assoc]
      have h1 := hC γ z hz
      have h0 : 0 ≤ ‖F (γ • z)‖ * z.im ^ 3 := by
        have : 0 < z.im := z.im_pos
        positivity
      exact (mul_le_of_le_one_left h0 (norm_char_le ψ _)).trans h1
  · intro hψ z
    obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hψ
    let e : (Fin 2 → ZMod L) ≃ (Fin 2 → ZMod L) :=
      { toFun := fun v => (u : ZMod L) • v
        invFun := fun v => ((u⁻¹ : (ZMod L)ˣ) : ZMod L) • v
        left_inv := fun v => by simp [smul_smul]
        right_inv := fun v => by simp [smul_smul] }
    have hs : ∑ v, G v z = ∑ v, G ((u : ZMod L) • v) z :=
      Fintype.sum_equiv e.symm _ _ (fun v => by simp [e, smul_smul])
    have hs2 : ∑ v, G v z = ψ u * ∑ v, G v z := by
      rw [Finset.mul_sum]
      conv_lhs => rw [hs]
      exact Finset.sum_congr rfl (fun v _ => hscale _ v z)
    have hne : (1 : ℂ) - ψ u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have : ((1 : ℂ) - ψ u) * ∑ v, G v z = 0 := by rw [sub_mul, one_mul, ← hs2, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  · intro hψ hF0 hFpos
    have hval : ∀ n : ℕ, ψ n = 0 ∨ ψ n = 1 := by
      intro n
      subst hψ
      by_cases h : IsUnit (n : ZMod L)
      · exact Or.inr (MulChar.one_apply h)
      · exact Or.inl (MulChar.map_nonunit _ h)
    refine ⟨?_, ?_⟩
    · intro v z
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      rw [hG]
      rcases hval n with h | h <;> simp [h, hF0]
    · obtain ⟨z0, hz0⟩ := hFpos
      obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z0
      refine ⟨cls L (((1 : ℕ) : ℤ) • row g⁻¹), g • z0, hg, ?_⟩
      rw [hG, inv_smul_smul]
      subst hψ
      simpa using hz0
end

section

open Set UpperTheory.V.Af UpperTheory.V.Sd
open scoped ComplexConjugate

theorem UpperTheory.V.Af.Rs.cmp :
    UpperTheory.V.Af.Rs.RankSum → UpperTheory.V.Af.Rs.Rankin → UpperTheory.V.Af.Rs.ArFact → UpperTheory.V.Af.Rs.ArSum → UpperTheory.V.Af.Rs.Cmp := by
  intro hRS hR hAF hAS k L _ hk χ ψ g h hap hχ s hs
  have hrec1 : Rs.Rec (fun p => χ (p : ZMod L) * (p:ℂ)^(k-1)) (coef g.f) :=
    ⟨g.one, fun p hp n hn => g.eig p hp n hn⟩
  have hrec2 : Rs.Rec (fun p => ψ (p : ZMod L) * (p:ℂ)^(k-1)) (coef h.f) :=
    ⟨h.one, fun p hp n hn => h.eig p hp n hn⟩
  have hba : ∀ p, Nat.Prime p → coef h.f p = coef g.f p := fun p hp => hap p hp
  have hz : ∀ p, Nat.Prime p → χ (p : ZMod L) * (p:ℂ)^(k-1) ≠ ψ (p : ZMod L) * (p:ℂ)^(k-1) →
      coef g.f p = 0 := by
    intro p hp hne
    apply hχ p hp
    intro heq
    apply hne
    rw [heq]
  have hbd : ∀ p, Nat.Prime p → ‖χ (p : ZMod L) * (p:ℂ)^(k-1)‖ ≤ (p:ℝ)^(k-1) ∧
      ‖ψ (p : ZMod L) * (p:ℂ)^(k-1)‖ ≤ (p:ℝ)^(k-1) := by
    intro p hp
    constructor <;>
    · rw [norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one _ _)
  obtain ⟨P, hPb, hP⟩ := hAF (k-1) _ _ (coef g.f) (coef h.f) hrec1 hrec2 hba hz hbd
  have hkt : ((k-1 : ℕ) : ℝ) + 1 ≤ (k:ℝ) + s - 1 := by
    rw [Nat.cast_sub hk]
    push_cast
    linarith [hs.1]
  have key := hAS (k-1) ((k:ℝ) + s - 1) (coef g.f) (coef h.f) P hkt hPb hP (hRS k L g.f s hs)
  rw [hR k L g.f g.f s hs, hR k L g.f h.f s hs, norm_mul, norm_mul]
  have hconv : (∑' n : ℕ, (starRingEnd ℂ) (coef g.f n) * coef g.f n / (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ))
      = ((∑' n : ℕ, ‖coef g.f n‖ ^ 2 / (n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    rw [Complex.conj_mul']
    push_cast
    ring
  have hnn : 0 ≤ ∑' n : ℕ, ‖coef g.f n‖ ^ 2 / (n:ℝ) ^ ((k:ℝ) + s - 1) :=
    tsum_nonneg fun n => div_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [hconv, Complex.norm_of_nonneg hnn]
  have hre := Complex.re_le_norm (∑' n : ℕ, (starRingEnd ℂ) (coef h.f n) * coef g.f n /
    (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ))
  have hg := norm_nonneg ((Rs.gam ((k:ℝ) + s - 1) : ℝ) : ℂ)
  calc _ ≤ ‖((Rs.gam ((k:ℝ) + s - 1) : ℝ) : ℂ)‖ * (7 * ‖∑' n : ℕ, (starRingEnd ℂ) (coef h.f n) * coef g.f n /
        (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ)‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hg
    _ = _ := by ring
end

section

open Filter Asymptotics CongruenceSubgroup Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Pointwise

private theorem bounded_petersson_weight (H : ℍ → ℂ) (B a : ℝ) (ha : 0 < a) (hB : ∀ z, ‖H z‖ ≤ B)
    (hd : H =O[atImInfty] fun τ => Real.exp (-a * τ.im)) : ∃ C : ℝ, ∀ z : ℍ, ‖H z‖ * z.im ^ 3 ≤ C := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hd
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hc
  set M := max A 0 with hM
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB UpperHalfPlane.I)
  have hM0 : 0 ≤ M := le_max_right _ _
  refine ⟨B * M ^ 3 + |c| * (6 / a ^ 3), fun z => ?_⟩
  have ht := z.im_pos
  have h1 : 0 ≤ B * M ^ 3 := by positivity
  have h2 : 0 ≤ |c| * (6 / a ^ 3) := by positivity
  rcases le_total z.im M with h | h
  · have : ‖H z‖ * z.im ^ 3 ≤ B * M ^ 3 :=
      mul_le_mul (hB z) (pow_le_pow_left₀ ht.le h 3) (by positivity) hB0
    linarith
  · have hz := hA z ((le_max_left _ _).trans h)
    simp only [Set.mem_setOf_eq] at hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hz
    have hexp : (a * z.im) ^ 3 / 6 ≤ Real.exp (a * z.im) := by
      have := Real.pow_div_factorial_le_exp (a * z.im) (by positivity) 3
      simpa [Nat.factorial] using this
    have he := Real.exp_pos (a * z.im)
    have hkey : Real.exp (-a * z.im) * z.im ^ 3 ≤ 6 / a ^ 3 := by
      rw [le_div_iff₀ (by positivity), neg_mul, Real.exp_neg, inv_mul_eq_div, div_mul_eq_mul_div,
        div_le_iff₀ he]
      rw [mul_pow] at hexp
      nlinarith
    have : ‖H z‖ * z.im ^ 3 ≤ |c| * (6 / a ^ 3) :=
      calc ‖H z‖ * z.im ^ 3 ≤ c * Real.exp (-a * z.im) * z.im ^ 3 :=
            mul_le_mul_of_nonneg_right hz (by positivity)
        _ ≤ |c| * (Real.exp (-a * z.im) * z.im ^ 3) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
        _ ≤ |c| * (6 / a ^ 3) := mul_le_mul_of_nonneg_left hkey (abs_nonneg c)
    linarith

theorem UpperTheory.V.Af.Rs.nicePet :
    UpperTheory.V.Af.Rs.NicePet := by
  intro k L _ f g
  refine ⟨by fun_prop, ?_⟩
  obtain ⟨B, hB⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Subgroup.map (mapGL ℝ) (Gamma1 L)) g f
  have hdec : ∀ h : SL(2, ℤ), ∃ a > 0,
      (fun τ => UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • τ)) =O[atImInfty]
        fun τ => Real.exp (-a * τ.im) := by
    intro h
    have : ((ConjAct.toConjAct (h : GL (Fin 2) ℝ)⁻¹) •
        (Subgroup.map (mapGL ℝ) (Gamma1 L))).IsArithmetic := by
      simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
        using! Subgroup.IsArithmetic.conj (Subgroup.map (mapGL ℝ) (Gamma1 L)) (mapGL ℚ h)⁻¹
    simp_rw [← UpperHalfPlane.petersson_slash_SL]
    exact (CuspFormClass.zero_at_infty (CuspForm.translate g h)).petersson_exp_decay_left
      (k : ℤ) _ (ModularForm.translate f h)
  have key : ∀ h : SL(2, ℤ), ∃ C : ℝ, ∀ z : ℍ,
      ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • z)‖ * z.im ^ 3 ≤ C := by
    intro h
    obtain ⟨a, ha, hd⟩ := hdec h
    exact bounded_petersson_weight (fun τ => UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • τ)) B a ha
      (fun z => hB _) hd
  choose Cf hCf using key
  let Γ' : Subgroup SL(2, ℤ) :=
    (Subgroup.map (mapGL ℝ) (Gamma1 L)).comap (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
  have : Fintype (SL(2, ℤ) ⧸ Γ') := Subgroup.fintypeQuotientOfFiniteIndex
  have hinv : ∀ j ∈ Γ', ∀ w : ℍ,
      ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (j • w)‖ = ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f w‖ :=
    fun j hj w => SlashInvariantFormClass.norm_petersson_smul (g := mapGL ℝ j) hj
  refine ⟨∑ q : SL(2, ℤ) ⧸ Γ', |Cf (Quotient.out q)⁻¹|, fun γ z _ => ?_⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul Γ' γ⁻¹
  have hγ : γ = (j : SL(2, ℤ)) * (Quotient.out (QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ Γ'))⁻¹ := by
    rw [hj]; group
  rw [hγ, mul_smul, hinv _ j.2]
  refine (hCf _ z).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun q : SL(2, ℤ) ⧸ Γ' => |Cf (Quotient.out q)⁻¹|)
    (fun q _ => abs_nonneg _) (Finset.mem_univ _)
end
