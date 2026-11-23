module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle175
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerUnitsFiniteModPowersAtLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle172
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_exp_converges : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (f : T.K), Den (T.exp f) ∧ ∃ (φ : ℂ → ℂ) (C : ℝ), T.an f = (φ : Mero) ∧ HS ε C φ (T.exp f) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb0, hfab⟩ := T.io_surj f
  have hiob : T.io b ≠ 0 := by
    intro h
    exact hb0 (T.io_inj (by rw [h, map_zero]))
  have hexb : T.exp (T.io b) ≠ 0 := by
    intro h
    exact hiob (T.exp.toRingHom.injective (by simpa using h))
  have hexpf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹ := by
    rw [← hfab, map_mul, mul_assoc, mul_inv_cancel₀ hexb, mul_one]
  obtain ⟨hops, -, -, -, hinv⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  have hEa := T.exp_io a
  have hEb := T.exp_io b
  have hEbi := hinv _ _ hexb hEb
  have hE : IsExp ε ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹) (T.exp f) := by
    rw [hexpf]; exact (hops _ _ _ _ hEa hEbi).2.2
  obtain ⟨hden, C, hC⟩ := hE
  refine ⟨hden, up ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹), C, ?_, hC⟩

  obtain ⟨⟨A, hA⟩, hmd, -, -, hHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units
  have hbR : InR ε.range (b : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 b.2
  have hbhol : DifferentiableOn ℂ (up (b : ℍ → ℂ)) Hs := (hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ hbR)
  have hgb0 : ((up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) ≠ 0 := by
    intro h
    apply hb0
    have h0 : ((up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h
    have := hid _ _ hbhol (differentiableOn_const 0) h0
    apply Subtype.ext
    funext τ
    have h1 := this τ (hHs τ)
    simpa [up, UpperHalfPlane.ofComplex_apply] using h1
  have hev := (hunit _ hbhol hgb0).1
  have hgi : germ ((b : ℍ → ℂ)⁻¹) * germ (b : ℍ → ℂ) = 1 := by
    unfold germ
    rw [← Filter.Germ.coe_mul]
    show ((up ((b : ℍ → ℂ)⁻¹) * up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((fun _ => (1 : ℂ) : ℂ → ℂ) : Mero)
    rw [Filter.Germ.coe_eq]
    filter_upwards [hev] with z hz
    simp only [Pi.mul_apply, up, Pi.inv_apply] at hz ⊢
    exact inv_mul_cancel₀ hz
  have hanf : T.an f * germ (b : ℍ → ℂ) = germ (a : ℍ → ℂ) := by
    rw [← T.an_io, ← T.an_io, ← map_mul, hfab]
  show T.an f = germ ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹)
  rw [← hA, map_mul, hA, hA, ← hanf, mul_assoc, mul_comm (germ (b : ℍ → ℂ)), hgi, mul_one]

end GlobalTheory.FN
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

def scaleH (l : ℕ) (hl : 0 < l) (τ : ℍ) : ℍ :=
  UpperHalfPlane.mk ((l : ℂ) * τ) (by simp; positivity)

lemma coe_sl_apply (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ)) / (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp

lemma denom_sl_ne (g : SL(2, ℤ)) (z : ℍ) : ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
  have h2 := UpperHalfPlane.denom_ne_zero g z
  simpa [UpperHalfPlane.denom] using h2

theorem Vo_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 0 < l →
    (MF k L χ a → MF k (L * l) χ (Vo l a)) ∧ (CF k L χ a → CF k (L * l) χ (Vo l a)) := by
  intro k L l χ a hl
  have key : MF k L χ a → MF k (L * l) χ (Vo l a) := by
    rintro ⟨hP, hI⟩
    obtain ⟨hP', hq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl hP
    refine ⟨hP', ?_⟩
    intro γ hγ τ
    obtain ⟨m, hm⟩ := hγ
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this; exact this
    let γ' : SL(2, ℤ) := ⟨!![γ 0 0, (l : ℤ) * γ 0 1; (L : ℤ) * m, γ 1 1], by
      rw [Matrix.det_fin_two_of]; rw [hm] at hdet; push_cast at hdet; linear_combination hdet⟩
    have h1 : ((L : ℕ) : ℤ) ∣ γ' 1 0 := ⟨m, by simp [γ']⟩
    have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    have hc : ((γ 1 0 : ℤ) : ℂ) = (L : ℂ) * l * m := by rw [hm]; push_cast; ring
    have e1 : γ' • scaleH l hl τ = scaleH l hl (γ • τ) := by
      apply UpperHalfPlane.ext
      rw [coe_sl_apply]
      simp only [scaleH, UpperHalfPlane.coe_mk, coe_sl_apply]
      have hd := denom_sl_ne γ τ
      rw [hc] at hd ⊢
      simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      push_cast
      have hd2 : (L : ℂ) * m * (l * (τ : ℂ)) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
        convert hd using 1; ring
      field_simp
    rw [hq (γ • τ) (scaleH l hl (γ • τ)) rfl, hq τ (scaleH l hl τ) rfl, ← e1, hI γ' h1]
    simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, scaleH, UpperHalfPlane.coe_mk]
    rw [hc]; push_cast; ring_nf
  refine ⟨key, ?_⟩
  rintro ⟨hM, C, hC⟩
  refine ⟨key hM, C, fun τ => ?_⟩
  obtain ⟨_, hq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl hM.1
  rw [hq τ (scaleH l hl τ) rfl]
  have him : (scaleH l hl τ).im = l * τ.im := by
    change ((l:ℂ) * (τ:ℂ)).im = (l:ℝ) * (τ:ℂ).im
    simp
  have hle : τ.im ≤ (scaleH l hl τ).im := by
    rw [him]; have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith [τ.im_pos]
  calc ‖qs a (scaleH l hl τ)‖ ^ 2 * τ.im ^ k ≤ ‖qs a (scaleH l hl τ)‖ ^ 2 * (scaleH l hl τ).im ^ k := by
        gcongr
    _ ≤ C := hC _

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.LipOne

theorem block (L : ℕ) (f : ℤ → ℂ) (N : ℕ) :
    ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), f d =
      ∑ r ∈ Finset.range L, ∑ n ∈ Finset.Icc (-(N:ℤ)) N, f (r + n * L) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rw [← Finset.sum_product']
  have hL' : (0:ℤ) < L := by exact_mod_cast hL
  refine Finset.sum_nbij' (fun d => ((d % L).toNat, d / L)) (fun p => (p.1 : ℤ) + p.2 * L) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_Ico] at hd
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    have h1 := Int.emod_nonneg d hL'.ne'
    have h2 := Int.emod_lt_of_pos d hL'
    have h3 := Int.emod_add_mul_ediv d L
    refine ⟨by omega, ?_, ?_⟩
    · by_contra h
      push_neg at h
      have : (L:ℤ) * (d / L) ≤ L * (-(N:ℤ) - 1) := by
        apply mul_le_mul_of_nonneg_left (by omega) hL'.le
      nlinarith
    · by_contra h
      push_neg at h
      have : (L:ℤ) * (N + 1) ≤ L * (d / L) := by
        apply mul_le_mul_of_nonneg_left (by omega) hL'.le
      nlinarith
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp
    simp only [Finset.mem_coe, Finset.mem_Ico]
    obtain ⟨h1, h2, h3⟩ := hp
    have h1' : (p.1 : ℤ) < L := by exact_mod_cast h1
    have h0 : (0:ℤ) ≤ p.1 := by positivity
    constructor <;> nlinarith
  · intro d hd
    simp only
    have h1 := Int.emod_nonneg d hL'.ne'
    rw [Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv d L
    linarith
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp
    have h1' : (p.1 : ℤ) < L := by exact_mod_cast hp.1
    ext
    · simp only
      rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) h1']
      simp
    · simp only
      rw [Int.add_mul_ediv_right _ _ hL'.ne', Int.ediv_eq_zero_of_lt (by positivity) h1']
      simp
  · intro d hd
    simp only
    congr 1
    have h1 := Int.emod_nonneg d hL'.ne'
    rw [Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv d L
    linarith

theorem lipschitz_one : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm 1 0 (z + d)) atTop (𝓝 (-2 * π * Complex.I / L * ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  intro L φ z hL hz h0
  have hLz : (L:ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have htrm : ∀ w : ℂ, trm 1 0 w = w⁻¹ := by
    intro w
    simp [trm]
  simp only [htrm]
  have hsum0 : ∑ r ∈ Finset.range L, φ r = 0 := by simpa [hat] using h0
  set g : ℤ → ℂ := fun d => φ d * ((z + d)⁻¹ - (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) with hg
  have hs : Summable g := T.summable_periodic_mul_inv_sub_inv_floor' L φ z hL hz
  have hsplit : ∀ s : Finset ℤ, ∑ d ∈ s, φ d * (z + d)⁻¹ =
      ∑ d ∈ s, g d + ∑ d ∈ s, φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹ := by
    intro s
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg]
    ring
  have hmonoF : Monotone (fun R : ℕ => Finset.Icc (-(R:ℤ)) R) := by
    intro a b hab
    have : (a:ℤ) ≤ b := by exact_mod_cast hab
    exact Finset.Icc_subset_Icc (by omega) (by omega)
  have hcovF : ∀ d : ℤ, ∃ R : ℕ, d ∈ Finset.Icc (-(R:ℤ)) R := by
    intro d
    exact ⟨d.natAbs, by simp only [Finset.mem_Icc]; omega⟩
  have hmonoG : Monotone (fun N : ℕ => Finset.Ico (-(N * L : ℤ)) ((N + 1) * L)) := by
    intro a b hab
    have : (a:ℤ) ≤ b := by exact_mod_cast hab
    have hL0 : (0:ℤ) ≤ L := by positivity
    exact Finset.Ico_subset_Ico (by nlinarith) (by nlinarith)
  have hcovG : ∀ d : ℤ, ∃ N : ℕ, d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L) := by
    intro d
    refine ⟨d.natAbs, ?_⟩
    have h1 : (1:ℤ) ≤ L := by exact_mod_cast hL
    have h3 : (d.natAbs : ℤ) = |d| := Int.natCast_natAbs d
    have h4 : (0:ℤ) ≤ |d| := abs_nonneg d
    simp only [Finset.mem_Ico]
    rw [h3]
    constructor
    · nlinarith [neg_abs_le d]
    · nlinarith [le_abs_self d]
  have hF := Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoF hcovF)
  have hG := Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoG hcovG)
  have hzero : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L),
      φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹ = 0 := by
    intro N
    rw [block L (fun d : ℤ => φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) N]
    calc _ = ∑ r ∈ Finset.range L, φ r * ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + ((L:ℤ) * n : ℤ))⁻¹ := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          have hr' : (r:ℤ) < L := by exact_mod_cast Finset.mem_range.mp hr
          rw [Int.add_mul_ediv_right _ _ hLz, Int.ediv_eq_zero_of_lt (by positivity) hr', zero_add]
          congr 1
          push_cast
          simp [ZMod.natCast_self]
      _ = 0 := by rw [← Finset.sum_mul, hsum0, zero_mul]
  have hb : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), φ d * (z + d)⁻¹ =
      ∑ r ∈ Finset.range L, φ r * ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹ := by
    intro N
    rw [block L (fun d : ℤ => φ d * (z + d)⁻¹) N]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    simp only [ZMod.natCast_self, mul_zero, add_zero]
    ring_nf
  have hmain := tendsto_finsetSum (Finset.range L)
    fun r (_ : r ∈ Finset.range L) => (T.tendsto_sum_Icc_inv_add_mul_eq_pi_div_mul_cot L z r hL hz).const_mul (φ r)
  rw [T.sum_periodic_cot_eq_qExpansion_fourier L φ z hL hz h0] at hmain
  have hT : ∑' d, g d = -2 * ↑π * Complex.I / ↑L * ∑' (m : ℕ), hat φ ↑(m + 1) *
      cexp (2 * ↑π * Complex.I * ↑(m + 1) * z / ↑L) := by
    refine tendsto_nhds_unique ?_ hmain
    refine hG.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [← hb N, hsplit, hzero N, add_zero]
  have hlim := hF.add (T.tendsto_sum_Icc_periodic_mul_inv_floor_div L φ z hL hz h0)
  rw [add_zero, hT] at hlim
  refine hlim.congr fun R => ?_
  simp only [Function.comp_apply]
  rw [hsplit]

end GlobalTheory.EisM.LipOne
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

lemma wt_countable : Countable SL(2, ℤ) := by
  have : Function.Injective (fun g : SL(2, ℤ) => fun i j => (g : Matrix (Fin 2) (Fin 2) ℤ) i j) := by
    intro g h e; ext i j; exact congrFun (congrFun e i) j
  exact this.countable

lemma wt_cont (g : SL(2, ℤ)) : Continuous (fun τ : ℍ => g • τ) :=
  continuous_const_smul (g : GL (Fin 2) ℝ)

lemma wt_fd_closed : IsClosed ModularGroup.fd := by
  have h1 : IsClosed {z : ℍ | 1 ≤ normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ 1 / 2} :=
    isClosed_le (continuous_abs.comp (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)) continuous_const
  exact h1.inter h2

theorem wt_exists : ∀ L : ℕ, 0 < L → ∃ ρ, Wt L ρ := by
  intro L hL
  haveI : NeZero L := ⟨hL.ne'⟩
  haveI := wt_countable
  haveI hfin : Finite (SL(2, ℤ) ⧸ Gamma0 L) := Subgroup.finite_quotient_of_finiteIndex
  set S : Finset SL(2, ℤ) := (Set.finite_range (fun q : SL(2, ℤ) ⧸ Gamma0 L => q.out)).toFinset with hS
  have hcov : ∀ g : SL(2, ℤ), ∃ s ∈ S, ∃ γ ∈ Gamma0 L, g = s * γ := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gamma0 L) g
    refine ⟨(QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma0 L).out, by simp [hS], ((h⁻¹ : Gamma0 L) : SL(2, ℤ)), (h⁻¹).2, ?_⟩
    rw [hh]; simp
  set K : Set ℍ := {τ | ∃ s ∈ S, s • τ ∈ ModularGroup.fd} with hK
  have hKm : MeasurableSet K := by
    have : K = ⋃ s ∈ S, (fun τ : ℍ => s • τ) ⁻¹' ModularGroup.fd := by
      ext τ; simp [hK]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun s _ => (wt_fd_closed.preimage (wt_cont s)).measurableSet
  have hKfin : ∀ τ : ℍ, {γ : Gamma0 L | (γ : SL(2, ℤ)) • τ ∈ K}.Finite := by
    intro τ
    have h1 : {g : SL(2, ℤ) | g • τ ∈ K}.Finite := by
      have : {g : SL(2, ℤ) | g • τ ∈ K} = ⋃ s ∈ S, (fun g => s * g) ⁻¹' {g | g • τ ∈ ModularGroup.fd} := by
        ext g; simp [hK, mul_smul]
      rw [this]
      exact Set.Finite.biUnion S.finite_toSet fun s _ =>
        (GlobalTheory.T.finite_slTwo_smul_mem_fundamentalDomain τ).preimage (mul_right_injective s).injOn
    exact Set.Finite.preimage (f := (Subtype.val : Gamma0 L → SL(2, ℤ))) Subtype.val_injective.injOn h1
  have hKne : ∀ τ : ℍ, ∃ γ : Gamma0 L, (γ : SL(2, ℤ)) • τ ∈ K := by
    intro τ
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    obtain ⟨s, hs, γ, hγ, rfl⟩ := hcov g
    exact ⟨⟨γ, hγ⟩, s, hs, by rwa [mul_smul] at hg⟩
  let N : ℍ → ENNReal := fun τ => ∑' γ : Gamma0 L, K.indicator (1 : ℍ → ENNReal) ((γ : SL(2, ℤ)) • τ)
  have hNm : Measurable N := by
    refine Measurable.tsum fun γ => ?_
    exact (measurable_one.indicator hKm).comp (wt_cont (γ : SL(2, ℤ))).measurable
  have hNcard : ∀ τ, N τ = ((hKfin τ).toFinset.card : ENNReal) := by
    intro τ
    simp only [N]
    rw [tsum_eq_sum (s := (hKfin τ).toFinset)]
    · rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      rw [Set.indicator_of_mem hγ]; simp
    · intro γ hγ
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      rw [Set.indicator_of_notMem hγ]
  have hNinv : ∀ (γ : Gamma0 L) τ, N ((γ : SL(2, ℤ)) • τ) = N τ := by
    intro γ τ
    simp only [N]
    rw [← (Equiv.mulRight γ).tsum_eq (fun δ : Gamma0 L => K.indicator (1 : ℍ → ENNReal) ((δ : SL(2, ℤ)) • τ))]
    simp [mul_smul]
  let ρ : ℍ → ℝ := fun τ => K.indicator (fun τ => ((N τ).toReal)⁻¹) τ
  refine ⟨ρ, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (ENNReal.measurable_toReal.comp hNm).inv.indicator hKm
  · intro τ; simp only [ρ]; apply Set.indicator_nonneg; intro τ _; positivity
  · intro τ
    have hz : ∀ γ ∉ (hKfin τ).toFinset, ρ ((γ : SL(2, ℤ)) • τ) = 0 := by
      intro γ hγ
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      simp only [ρ]; rw [Set.indicator_of_notMem hγ]
    have hpos : 0 < (hKfin τ).toFinset.card := by
      obtain ⟨γ, hγ⟩ := hKne τ
      exact Finset.card_pos.mpr ⟨γ, by simpa using hγ⟩
    have heq : ∑ γ ∈ (hKfin τ).toFinset, ρ ((γ : SL(2, ℤ)) • τ) = 1 := by
      rw [Finset.sum_congr rfl (g := fun _ => (((hKfin τ).toFinset.card : ℝ))⁻¹)]
      · rw [Finset.sum_const, nsmul_eq_mul]
        have : ((hKfin τ).toFinset.card : ℝ) ≠ 0 := by positivity
        field_simp
      · intro γ hγ
        have hγ' : (γ : SL(2, ℤ)) • τ ∈ K := by
          simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ; exact hγ
        simp only [ρ]
        rw [Set.indicator_of_mem hγ', hNinv, hNcard]
        simp
    exact heq ▸ hasSum_sum_of_ne_finset_zero hz
  · refine ⟨S, fun τ hτ => ?_⟩
    have : τ ∈ K := by
      by_contra h; exact hτ (by simp only [ρ]; rw [Set.indicator_of_notMem h])
    exact this

end GlobalTheory
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.overAffineJLine_comap_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ W : ValuationSubring X.K, X.OverY W → (∀ g : GQ, X.OverY (W.comap (X.sl g).toRingEquiv.toRingHom)) ∧ ∀ s : Ω ≃ₐ[ℚ] Ω, X.OverY (W.comap (X.gal s).toRingHom) := by
  first | exact @GlobalTheory.KZ.Tower.overY_comap_sl_gal | exact GlobalTheory.KZ.Tower.overY_comap_sl_gal | (intros; apply GlobalTheory.KZ.Tower.overY_comap_sl_gal <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.modularTower_units_finite_mod_powers_at_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M m : ℕ), 0 < M → 0 < m → ∃ R : Finset X.Kˣ, ∀ f : X.Kˣ, f ∈ X.Un m → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ r ∈ R, ∃ g : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (g : X.K) = g) ∧ ∃ c : Ω, c ≠ 0 ∧ (f : X.K) = r * (g : X.K) ^ m * algebraMap Ω X.K c := by
  first | exact @GlobalTheory.KZ.FinLev.finite_mod_powers | exact GlobalTheory.KZ.FinLev.finite_mod_powers | (intros; apply GlobalTheory.KZ.FinLev.finite_mod_powers <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), IsDl X A l n s f φ → IsDl X A l n s f φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  first | exact @GlobalTheory.Glue.isDl_unique | exact GlobalTheory.Glue.isDl_unique | (intros; apply GlobalTheory.Glue.isDl_unique <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.mass_not_rootsAvoid_le' : ∀ (g : ℕ) [Fact g.Prime], ∀ (N q d : ℕ) (c : (ZMod g)ˣ), (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → (mass g N fun f => ¬ RootsAvoid g c f) ≤ 1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by
  first | exact @GlobalTheory.BadShare.mass_not_rootsAvoid_le | exact GlobalTheory.BadShare.mass_not_rootsAvoid_le | (intros; apply GlobalTheory.BadShare.mass_not_rootsAvoid_le <;> assumption)
end
