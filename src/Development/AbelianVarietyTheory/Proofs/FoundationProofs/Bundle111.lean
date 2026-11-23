module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle084
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle101
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.ZetaExp

theorem pow_mod_eq {M : Type*} [Monoid M] {w : M} {N : ℕ} (h : w ^ N = 1) (a : ℕ) : w ^ (a % N) = w ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, h, one_pow, mul_one]

theorem ch_eq_pow (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / N : ℚ) : ℂ)) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) (N : ℕ), 0 < N → (∃ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d) ∧ ∀ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∃ u : (ZMod N)ˣ, (u : ZMod N) = d ∧ ∀ g : ℂ ≃+* ℂ, (∀ x, g (ε x) = ε (s x)) → ZetaAct g N u := by
  intro Ω _ _ _ ε s N hN
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨_, hval, _, _, hprim, _⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  set ζ := eOm ε (1 / N) with hζ
  have hp : IsPrimitiveRoot ζ N := hprim N hN
  have hsp : IsPrimitiveRoot (s ζ) N := hp.map_of_injective s.injective
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one hsp.pow_eq_one
    exact ⟨i, by rw [← hi, zpow_natCast]⟩
  · intro d hd
    set i : ℕ := (d % (N : ℤ)).toNat with hi
    have hnn : 0 ≤ d % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have hic : (i : ℤ) = d % (N : ℤ) := Int.toNat_of_nonneg hnn
    have hζi : ζ ^ d = ζ ^ i := by
      rw [← zpow_natCast, hic]
      have hz : ζ ≠ 0 := hp.ne_zero hN.ne'
      conv_lhs => rw [← Int.mul_ediv_add_emod d N, zpow_add₀ hz, zpow_mul, zpow_natCast, hp.pow_eq_one, one_zpow, one_mul]
    have hsi : s ζ = ζ ^ i := hd.trans hζi
    have hcop : i.Coprime N := (hp.pow_iff_coprime hN i).1 (hsi ▸ hsp)
    have hdi : ((d : ZMod N)) = (i : ZMod N) := by
      rw [← Int.cast_natCast, hic, ZMod.intCast_mod]
    have hu : IsUnit (i : ZMod N) := (ZMod.isUnit_iff_coprime i N).2 hcop
    refine ⟨hu.unit, by rw [IsUnit.unit_spec, hdi], ?_⟩
    intro g hg j
    have hεζ : ε ζ = Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / N : ℚ) : ℂ)) := hval _
    have hηN : (ε ζ) ^ N = 1 := by rw [← map_pow, hp.pow_eq_one, map_one]
    have hl : g ((ε ζ) ^ j.val) = (ε ζ) ^ (i * j.val) := by
      rw [map_pow, hg, hsi, map_pow, ← pow_mul]
    have hr : ((i : ZMod N) * j).val = (i * j.val) % N := by
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
    rw [ch_eq_pow, ch_eq_pow, ← hεζ, hl, IsUnit.unit_spec, hr, pow_mod_eq hηN]

end GlobalTheory.ZetaExp
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.MobLaws

theorem det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h0
  have hy : 0 < z.im := hz
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  have hd := det_pos g
  rcases him with hc | hc
  · rw [hc] at hre hd; simp at hre; rw [hre] at hd; simp at hd
  · linarith

theorem im_mob (g : GQ) (z : ℂ) : (mob g z).im =
    (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) * z.im /
      Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := by
  rw [mob, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ratCast_re, Complex.ratCast_im]
  push_cast
  rw [div_sub_div_same]
  congr 1
  ring

theorem mob_mem (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  show 0 < (mob g z).im
  rw [im_mob]
  have hy : 0 < z.im := hz
  have hd : (0:ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) := by exact_mod_cast det_pos g
  exact div_pos (mul_pos hd hy) (Complex.normSq_pos.2 (den_ne g hz))

theorem complex_mobius_fraction_clear_denom (a b c d N D : ℂ) (hD : D ≠ 0) :
    (a * (N / D) + b) / (c * (N / D) + d) = (a * N + b * D) / (c * N + d * D) := by
  have e1 : a * (N / D) + b = (a * N + b * D) / D := by field_simp
  have e2 : c * (N / D) + d = (c * N + d * D) / D := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hD]

theorem mob_mul (g h : GQ) {z : ℂ} (hz : z ∈ Hs) : mob (g * h) z = mob g (mob h z) := by
  have h1 := den_ne h hz
  unfold mob
  rw [complex_mobius_fraction_clear_denom _ _ _ _ _ _ h1]
  simp only [ent_mul]
  push_cast
  congr 1 <;> ring

theorem mob_one (z : ℂ) : mob 1 z = z := by
  simp [mob, ent]

theorem mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold mob
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

theorem toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.2]; norm_num
  apply Subtype.ext; apply Units.ext; ext i j
  simp [toGQ, h, ofSL]

theorem toGQ_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (hm : 0 < m.det) (hm' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have h : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos hm hm'
  apply Subtype.ext; apply Units.ext
  simp only [toGQ, h, hm, hm', dif_pos]
  ext i j
  simp [Matrix.mul_apply]

end GlobalTheory.KZ.MobLaws

namespace GlobalTheory.KZ

theorem mob_laws : (∀ (g : GQ), ∀ z ∈ Hs, mob g z ∈ Hs) ∧ (∀ (g h : GQ), ∀ z ∈ Hs, mob (g * h) z = mob g (mob h z)) ∧ (∀ z, mob 1 z = z) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ (∀ γ : SL(2, ℤ), toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ) ∧ (∀ m m' : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det → 0 < m'.det → toGQ (m * m') = toGQ m * toGQ m') :=
  ⟨fun g _ hz => MobLaws.mob_mem g hz, fun g h _ hz => MobLaws.mob_mul g h hz, MobLaws.mob_one,
    MobLaws.mob_diff, MobLaws.toGQ_SL, MobLaws.toGQ_mul⟩

end GlobalTheory.KZ
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.towerJInvariant_transcendental : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε), Transcendental Ω X.jK := by
  first | exact @GlobalTheory.KZ.Tower.jK_transcendental | exact GlobalTheory.KZ.Tower.jK_transcendental | (intros; apply GlobalTheory.KZ.Tower.jK_transcendental <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.diamondOperatorOfMatrix_congr : ∀ (N l : ℕ) (k d : ℤ) (σ τ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.dia k σ ⇑f = GlobalTheory.Hk.dia k τ ⇑f := by
  first | exact @GlobalTheory.Hk.dia_congr | exact GlobalTheory.Hk.dia_congr | (intros; apply GlobalTheory.Hk.dia_congr <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeT_slash_eq_of_slash_eq : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → (∀ γ ∈ GlobalTheory.Hk.lev N l, f ∣[k] γ = f) → ∀ γ ∈ GlobalTheory.Hk.lev N l, GlobalTheory.Hk.heckeT k q σ f ∣[k] γ = GlobalTheory.Hk.heckeT k q σ f := by
  first | exact @GlobalTheory.HkInv.heckeT_slash_invariant | exact GlobalTheory.HkInv.heckeT_slash_invariant | (intros; apply GlobalTheory.HkInv.heckeT_slash_invariant <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → GlobalTheory.Hk.IsDia N l d σ → ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.dia k σ ⇑f) (GlobalTheory.Hk.dia k σ ⇑g) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g := by
  first | exact @GlobalTheory.Hk.pet_dia_dia | exact GlobalTheory.Hk.pet_dia_dia | (intros; apply GlobalTheory.Hk.pet_dia_dia <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ

theorem _root_.GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane : ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs → (∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) → (∃ M t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z‖ ≤ M) → ∃ c : ℂ, ∀ z ∈ Hs, φ z = c := by
  first | exact @GlobalTheory.KZ.LevelOne.const_of_invariant_bounded | exact GlobalTheory.KZ.LevelOne.const_of_invariant_bounded | (intros; apply GlobalTheory.KZ.LevelOne.const_of_invariant_bounded <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ

theorem _root_.GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n) → ∃ B t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z - ε ((X.exp h).coeff 0)‖ ≤ B * Real.exp (-(2 * Real.pi * (z.im - t))) := by
  first | exact @GlobalTheory.KZ.ExpBound.bound_at_infinity | exact GlobalTheory.KZ.ExpBound.bound_at_infinity | (intros; apply GlobalTheory.KZ.ExpBound.bound_at_infinity <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeUOperator_preserves_modularForm_gamma1InterGamma0 : ∀ (N l q : ℕ) (k : ℤ), 0 < N → 0 < l → q.Prime → q ∣ N * l → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.uOp q ⇑f := by
  first | exact @GlobalTheory.Hk.uOp_modularForm | exact GlobalTheory.Hk.uOp_modularForm | (intros; apply GlobalTheory.Hk.uOp_modularForm <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerLimit

theorem trunc_mem (w : ℕ) (R : ℂ[X]) :
    (∑ j ∈ Finset.range (w + 1), C (R.coeff j) * X ^ j) ∈ degreeLT ℂ (w + 1) := by
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Finset.mem_range.1 hj

theorem trunc_coeff (w : ℕ) (R : ℂ[X]) {j : ℕ} (hj : j ≤ w) :
    (∑ i ∈ Finset.range (w + 1), C (R.coeff i) * X ^ i).coeff j = R.coeff j := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_of_le hj]

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  unfold eichler
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Finset.mem_range.1 hj

theorem bound_rate {F : ℍ → ℂ} {C c c' : ℝ} (hc : c' ≤ c)
    (hF : ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) :
    ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ max C 0 * Real.exp (-c' * τ.im) := by
  intro τ hτ
  refine (hF τ hτ).trans ?_
  have h1 : Real.exp (-c * τ.im) ≤ Real.exp (-c' * τ.im) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg (sub_nonneg.2 hc) (τ.im_pos.le)])
  calc C * Real.exp (-c * τ.im) ≤ max C 0 * Real.exp (-c * τ.im) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (-c' * τ.im) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

theorem polySlash_eichler_limit : ∀ (k : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]) (σ : SL(2, ℤ)) (Cf cf Ch ch : ℝ), 2 ≤ k → 0 < cf → 0 < ch → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[(k : ℤ)] σ) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h ∣[(k : ℤ)] σ) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(f ∣[(k : ℤ)] σ) τ‖ ≤ Cf * Real.exp (-cf * τ.im)) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(h ∣[(k : ℤ)] σ) τ‖ ≤ Ch * Real.exp (-ch * τ.im)) → p ∈ degreeLT ℂ (k - 1) → ∃ (Q : ℂ[X]) (C' c : ℝ), Q ∈ degreeLT ℂ (k - 2 + 1) ∧ 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ k - 2, ‖(slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p) - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (k - 2) := by
  intro k f h p σ Cf cf Ch ch hk hcf hch hf hh hfs hhs bf bh _hp
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk f hf σ
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk h hh σ
  have hc : 0 < min cf ch := lt_min hcf hch
  obtain ⟨Lf, Kf, hLf⟩ := GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay (k - 2) (f ∣[(k : ℤ)] σ) (max Cf 0) (min cf ch) hfs hc
    (bound_rate (min_le_left _ _) bf)
  obtain ⟨Lh, Kh, hLh⟩ := GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay (k - 2) (h ∣[(k : ℤ)] σ) (max Ch 0) (min cf ch) hhs hc
    (bound_rate (min_le_right _ _) bh)
  set R : ℂ[X] := Lf + C1 - (Lh + C2).map (starRingEnd ℂ) - slP (k - 2) (mat σ) p with hR
  refine ⟨∑ j ∈ Finset.range (k - 2 + 1), C (R.coeff j) * X ^ j, Kf + Kh, min cf ch,
    trunc_mem _ _, hc, ?_⟩
  intro τ hτ j hj
  have key : slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p)
      = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C1
        - (eichler (k - 2) (h ∣[(k : ℤ)] σ) τ + C2).map (starRingEnd ℂ) - slP (k - 2) (mat σ) p := by
    rw [map_sub, map_sub, hC1, ← (GlobalTheory.T.polyDegreeSlashAction_right_action_properties (k - 2) (mat σ) 1 _ (eichler_mem _ _ _)).2.2.2, hC2]
  have e1 := hLf τ hτ j hj
  have e2 := hLh τ hτ j hj
  rw [coeff_sub] at e1 e2
  rw [coeff_sub, key, trunc_coeff _ _ hj, hR]
  simp only [coeff_sub, coeff_add, coeff_map, map_add (f := _)]
  calc _ = ‖((eichler (k - 2) (f ∣[(k : ℤ)] σ) τ).coeff j - Lf.coeff j)
        - (starRingEnd ℂ) ((eichler (k - 2) (h ∣[(k : ℤ)] σ) τ).coeff j - Lh.coeff j)‖ := by
          congr 1; rw [map_sub]; ring
    _ ≤ _ := norm_sub_le _ _
    _ = ‖(eichler (k - 2) (f ∣[(k : ℤ)] σ) τ).coeff j - Lf.coeff j‖
        + ‖(eichler (k - 2) (h ∣[(k : ℤ)] σ) τ).coeff j - Lh.coeff j‖ := by rw [Complex.norm_conj]
    _ ≤ _ := by rw [add_mul, add_mul]; exact add_le_add e1 e2

end GlobalTheory.EichlerLimit
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem GlobalTheory.HeckeFamilyMatrices.ulSq_old : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Lev N l) (k : ℤ)),
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) ∧
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) ∧
    UlF (k : ℤ) l (UlF (k : ℤ) l ⇑f) - (χ l * (l : ℂ) ^ (k - 2)) • ⇑f = ⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1) := by
  intro N l k hN hl hlN hk χ f hf
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨u, v, huv⟩ : IsCoprime (l : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)
  have h : (l : ℤ) * u - N * (-v) = 1 := by linear_combination huv
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : NeZero l := ⟨hl0.ne'⟩
  haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance
  set W := wOld N l (-v) u with hW
  set D := dg (l : ℤ) 1 with hD
  have hWdet : 0 < W.det := by
    rw [hW, wOld, Matrix.det_fin_two_of]; nlinarith
  have hDdet : 0 < D.det := by
    rw [hD, dg, Matrix.det_fin_two_of]; simpa using hl0
  set F : ℍ → ℂ := ⇑f with hFdef
  have hF : ChiInv (k : ℤ) N (N * l) χ F := hf
  have cF : CuspAll (k : ℤ) F := GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 (Lev N l) k f
  set G := F ∣[(k : ℤ)] toGL W with hGdef
  have hG : ChiInv (k : ℤ) N (N * l) χ G := GlobalTheory.T.nebentypus_slash_oldformLevelRaisingMatrix N l k (-v) u h χ F hl0 hF
  have cG : CuspAll (k : ℤ) G := GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k W F hWdet cF
  have cTr : ∀ H, CuspAll (k : ℤ) H → CuspAll (k : ℤ) (trOld k N l (-v) u h H) := by
    intro H hH
    unfold trOld
    refine cuspAll_add hH ?_
    induction (Finset.range l) using Finset.induction_on with
    | empty => simpa using cuspAll_smul 0 hH
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      refine cuspAll_add ?_ ih
      rw [slash_SL_eq]
      exact GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k _ H (by simp [mat]) hH
  set A := trOld k N l (-v) u h F with hAdef
  set B := trOld k N l (-v) u h G with hBdef
  have hA : ChiInv (k : ℤ) N N χ A := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ F hN0 hl hF
  have hB : ChiInv (k : ℤ) N N χ B := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ G hN0 hl hG
  have cA : CuspAll (k : ℤ) A := cTr F cF
  have cB : CuspAll (k : ℤ) B := cTr G cG
  set C := B ∣[(k : ℤ)] toGL D with hCdef
  have hC : ChiInv (k : ℤ) N (N * l) χ C := GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise N l k χ B hl0 hB
  have cC : CuspAll (k : ℤ) C := GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k D B hDdet cB
  have hTC : ChiInv (k : ℤ) N N χ (trOld k N l (-v) u h C) := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ C hN0 hl hC
  have cTC : CuspAll (k : ℤ) (trOld k N l (-v) u h C) := cTr C cC
  set c₁ : ℂ := χ (l : ZMod N) with hc₁
  set p : ℂ := (l : ℂ) ^ ((k : ℤ) - 2) with hp
  have h₁ : ChiInv (k : ℤ) N N χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) :=
    chiInv_add (chiInv_smul _ hTC) (chiInv_smul _ hA)
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) hN0
    (cuspAll_add (cuspAll_smul _ cTC) (cuspAll_smul _ cA)) h₁
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (-(c₁ ^ 2) • B) hN0 (cuspAll_smul _ cB) (chiInv_smul _ hB)
  refine ⟨f₁, f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
  · rw [hf₁]; exact h₁ γ hγ
  · rw [hf₂]; exact chiInv_smul _ hB γ hγ
  rw [hf₁, hf₂]
  have e1 := GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h F hl0
  have e2 := GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h G hl0
  have e3 := GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus N l k (-v) u h χ F hl0 hF
  have e4 := GlobalTheory.T.heckeUl_eq_nebentypus_oldformTrace_sub_diag N l k (-v) u h χ B hl0 hB
  rw [← hAdef, ← hGdef] at e1
  rw [← hBdef, e3] at e2
  rw [← hCdef] at e4
  have cb : c₁ * χ (u : ZMod N) = 1 := by
    rw [hc₁, ← map_mul]
    have h2 := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at h2
    rw [ZMod.natCast_self] at h2
    rw [show ((l : ZMod N) * (u : ZMod N)) = 1 by linear_combination h2, map_one]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  have pp : p * (l : ℂ) ^ (2 - (k : ℤ)) = 1 := by
    rw [hp, ← zpow_add₀ hl']; simp
  have hUG : UlF k l G = p • (A - F) := by
    rw [e1, add_sub_cancel_left, smul_smul, pp, one_smul]
  have hUF : UlF k l F = c₁ • (B - G) := by
    have key : c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * ((l : ℂ) ^ ((k : ℤ) - 2) * χ (u : ZMod N)) = 1 := by
      rw [← hp]
      calc c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * (p * χ (u : ZMod N))
          = (p * (l : ℂ) ^ (2 - (k : ℤ))) * (c₁ * χ (u : ZMod N)) := by ring
        _ = 1 := by rw [pp, cb, one_mul]
    rw [e2, add_sub_cancel_left, ulF_smul k l hl0, smul_smul, smul_smul, key, one_smul]
  have hpk : (l : ℂ) ^ (k - 2) = p := by
    rw [hp, show ((k : ℤ) - 2) = ((k - 2 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [hpk, hUF, ulF_smul k l hl0, ulF_sub k l hl0, e4, hUG, smul_slash_toGL k D hDdet, ← hCdef]
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 2 ≤ k → ∀ f : ModularForm Γ (k : ℤ), per Γ (k - 2) ⇑f ∈ Z1 Γ (k - 2) ∧ ∀ (γ : Γ) (τ : ℍ), per Γ (k - 2) ⇑f γ = slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub | exact GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub | (intros; apply GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub <;> assumption)
end
