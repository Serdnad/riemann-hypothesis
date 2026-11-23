module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProductInvariant
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem GlobalTheory.kronecker_product_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M q : ℕ) (σ : SL(2, ℤ)) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  intro Ω _ _ ε X M q σ f hM hq hqM hf hσ γ hγ
  exact GlobalTheory.hecke_product_invariant ε X M q f hM hq hqM hf σ hσ γ hγ
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (τ : ℍ), HasSum (fun m => GlobalTheory.Hk.coef ⇑f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  first | exact @GlobalTheory.Hk.lev_hasSum_coef | exact GlobalTheory.Hk.lev_hasSum_coef | (intros; apply GlobalTheory.Hk.lev_hasSum_coef <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.hasSum_heckeUOperatorExplicit : ∀ (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < q → (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ τ : ℍ, HasSum (fun m => a (q * m) • Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.uOp q f τ) := by
  first | exact @GlobalTheory.Hk.hasSum_uOp | exact GlobalTheory.Hk.hasSum_uOp | (intros; apply GlobalTheory.Hk.hasSum_uOp <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.hasSum_heckeVOperatorExplicit : ∀ (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < q → (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ τ : ℍ, HasSum (fun m => (if q ∣ m then a (m / q) else 0) • Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.vOp q f τ) := by
  first | exact @GlobalTheory.Hk.vOp_hasSum | exact GlobalTheory.Hk.vOp_hasSum | (intros; apply GlobalTheory.Hk.vOp_hasSum <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.qExpansionCoeffPeriodOne_eq_of_hasSum : ∀ (f : ℍ → ℂ) (a : ℕ → ℂ), (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ n, GlobalTheory.Hk.coef f n = a n := by
  first | exact @GlobalTheory.Hk.coef_of_hasSum | exact GlobalTheory.Hk.coef_of_hasSum | (intros; apply GlobalTheory.Hk.coef_of_hasSum <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit : ∀ (q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → MDiff f → MDiff (GlobalTheory.Hk.uOp q f) ∧ MDiff (GlobalTheory.Hk.vOp q f) ∧ MDiff (GlobalTheory.Hk.heckeT k q σ f) := by
  first | exact @GlobalTheory.Hk.hecke_mdiff | exact GlobalTheory.Hk.hecke_mdiff | (intros; apply GlobalTheory.Hk.hecke_mdiff <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HermFN

lemma lin_ne_zero (c e : ℤ) (z : ℂ) (hz : 0 < z.im) (h : c ≠ 0 ∨ e ≠ 0) : (c : ℂ) * z + e ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hc
  · subst hc; simp at hre; rcases h with h | h <;> simp_all
  · linarith

lemma common_den (g : GQ) : ∃ N : ℕ, 0 < N ∧ ∀ i j, ∃ z : ℤ, (N : ℚ) * ent g i j = z := by
  refine ⟨∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den, ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => (ent g i j).den_pos))
  · intro i j
    have hdv : (ent g i j).den ∣ ∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den :=
      (Finset.dvd_prod_of_mem (fun j => (ent g i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j : Fin 2, (ent g i j).den) (Finset.mem_univ i))
    obtain ⟨k, hk⟩ := hdv
    refine ⟨k * (ent g i j).num, ?_⟩
    rw [hk]
    have := Rat.mul_den_eq_num (ent g i j)
    push_cast
    rw [← this]; ring

lemma upper_step (p p' x b dd q : ℤ) (a : ℕ) (τ : ℂ) (hd0 : (dd : ℂ) ≠ 0) (hpC : (p : ℂ) = a * p')
    (hq'C : (p' : ℂ) * b + x * dd = q) :
    ((p' : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((x : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
  rw [hpC, ← hq'C]; field_simp; ring

lemma left_step (m0 m1 A B C D : ℤ) (N : ℕ) (τ : ℂ) (hN : (N : ℂ) ≠ 0) (hD : (C : ℂ) * τ + D ≠ 0) :
    (m0 : ℂ) / N * (((A : ℂ) * τ + B) / ((C : ℂ) * τ + D)) + (m1 : ℂ) / N =
      (((m0 * A + m1 * C : ℤ) : ℂ) * τ + ((m0 * B + m1 * D : ℤ) : ℂ)) / (N * ((C : ℂ) * τ + D)) := by
  have hD' : τ * (C : ℂ) + D ≠ 0 := by rwa [mul_comm]
  rw [eq_div_iff (mul_ne_zero hN hD)]
  push_cast
  field_simp
  ring

end GlobalTheory.HermFN

namespace GlobalTheory.HermFN

theorem hermite (g : GQ) : ∃ n : ℕ, 0 < n ∧ ∀ γ₀ : SL(2, ℤ), ∃ (γ : SL(2, ℤ)) (a d : ℕ) (b : ℤ), a * d = n ∧
    ∀ τ : ℍ, mob g ((γ₀ • τ : ℍ) : ℂ) = mob (ofSL γ) (((a : ℂ) * τ + b) / d) := by
  obtain ⟨N, hN, hm⟩ := common_den g
  choose m hm using hm
  have hdetg : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
    have h := g.2
    rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
    exact h
  set nI : ℤ := m 0 0 * m 1 1 - m 0 1 * m 1 0 with hnI
  have hn : 0 < nI := by
    have hq : (nI : ℚ) = (N : ℚ) ^ 2 * (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0) := by
      rw [hnI]; push_cast; rw [← hm 0 0, ← hm 0 1, ← hm 1 0, ← hm 1 1]; ring
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have : (0 : ℚ) < nI := by rw [hq]; positivity
    exact_mod_cast this
  refine ⟨nI.toNat, by omega, ?_⟩
  intro γ₀
  have hdet0 : γ₀ 0 0 * γ₀ 1 1 - γ₀ 0 1 * γ₀ 1 0 = 1 := by
    have := γ₀.2; rwa [Matrix.det_fin_two] at this
  set p : ℤ := m 0 0 * γ₀ 0 0 + m 0 1 * γ₀ 1 0 with hp_def
  set r : ℤ := m 1 0 * γ₀ 0 0 + m 1 1 * γ₀ 1 0 with hr_def
  set q : ℤ := m 0 0 * γ₀ 0 1 + m 0 1 * γ₀ 1 1 with hq_def
  set s : ℤ := m 1 0 * γ₀ 0 1 + m 1 1 * γ₀ 1 1 with hs_def
  have hps : p * s - q * r = nI := by
    rw [hp_def, hr_def, hq_def, hs_def, hnI]; linear_combination (m 0 0 * m 1 1 - m 0 1 * m 1 0) * hdet0
  have hpr : p ≠ 0 ∨ r ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  set a : ℕ := Int.gcd p r with ha_def
  have ha : 0 < a := Int.gcd_pos_iff.mpr hpr
  set p' : ℤ := p / a
  set r' : ℤ := r / a
  have hp : p = a * p' := (Int.mul_ediv_cancel' (Int.gcd_dvd_left p r)).symm
  have hr : r = a * r' := (Int.mul_ediv_cancel' (Int.gcd_dvd_right p r)).symm
  have cop : IsCoprime p' r' := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd ha)
  obtain ⟨γ, h0, h1⟩ := cop.exists_SL2_col 0
  have hγ : p' * γ 1 1 - γ 0 1 * r' = 1 := by
    have := γ.2; rw [Matrix.det_fin_two, h0, h1] at this; linear_combination this
  set b : ℤ := γ 1 1 * q - γ 0 1 * s with hb_def
  set dd : ℤ := p' * s - r' * q with hdd_def
  have had : (a : ℤ) * dd = nI := by
    rw [hdd_def, ← hps]; linear_combination (-s) * hp + q * hr
  have hd : 0 < dd := by
    have : (0 : ℤ) < a := by exact_mod_cast ha
    nlinarith
  have hq' : p' * b + γ 0 1 * dd = q := by rw [hb_def, hdd_def]; linear_combination q * hγ
  have hs' : r' * b + γ 1 1 * dd = s := by rw [hb_def, hdd_def]; linear_combination s * hγ
  refine ⟨γ, a, dd.toNat, b, ?_, ?_⟩
  · zify; rw [Int.toNat_of_nonneg hd.le, Int.toNat_of_nonneg hn.le]; exact had
  · intro τ
    have hz : 0 < (τ : ℂ).im := τ.im_pos
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hdC : ((dd.toNat : ℕ) : ℂ) = (dd : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hd.le]
    have hd0 : (dd : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hc : ∀ i j, ((ent g i j : ℚ) : ℂ) = (m i j : ℂ) / N := by
      intro i j
      have : ent g i j = (m i j : ℚ) / N := by
        rw [← hm i j]; field_simp
      rw [this]; push_cast; rfl
    have hD0 : ((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ) ≠ 0 := by
      apply lin_ne_zero _ _ _ hz
      by_contra h; push_neg at h; rw [h.1, h.2] at hdet0; simp at hdet0
    have hRS : (r : ℂ) * τ + s ≠ 0 := lin_ne_zero r s _ hz hrs
    have hpC : (p : ℂ) = a * p' := by exact_mod_cast hp
    have hrC : (r : ℂ) = a * r' := by exact_mod_cast hr
    have hq'C : (p' : ℂ) * b + γ 0 1 * dd = q := by exact_mod_cast hq'
    have hs'C : (r' : ℂ) * b + γ 1 1 * dd = s := by exact_mod_cast hs'
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, hdC]
    simp only [mob, hc, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    have eL : ((m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N) /
        ((m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N)
        = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + s) := by
      have e1 : (m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N
          = ((p : ℂ) * τ + q) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 0 0) (m 0 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      have e2 : (m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N
          = ((r : ℂ) * τ + s) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 1 0) (m 1 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      rw [e1, e2, div_div_div_cancel_right₀ (mul_ne_zero hNC hD0)]
    have eR : ((γ 0 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 0 1 : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
      rw [h0]; exact upper_step p p' (γ 0 1) b dd q a τ hd0 hpC hq'C
    have eR2 : ((γ 1 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 1 1 : ℤ) : ℂ) = ((r : ℂ) * τ + s) / dd := by
      rw [h1]; exact upper_step r r' (γ 1 1) b dd s a τ hd0 hrC hs'C
    have hofSL : ∀ i j, ((ent (ofSL γ) i j : ℚ) : ℂ) = ((γ i j : ℤ) : ℂ) := by
      intro i j; show (((γ i j : ℤ) : ℚ) : ℂ) = _; push_cast; rfl
    simp only [hofSL]
    rw [eL, eR, eR2, div_div_div_cancel_right₀ hd0]

end GlobalTheory.HermFN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNMob

theorem det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := (Matrix.mem_glpos (g : GL (Fin 2) ℚ)).1 g.2
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
  simpa [ent] using h

theorem im_frac (a b c d : ℝ) (z : ℂ) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im = (a * d - b * c) * z.im / Complex.normSq ((c : ℂ) * z + d) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem denom_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  simp at hi hr
  have hz' : 0 < z.im := hz
  have hc : ent g 1 0 = 0 := by
    rcases hi with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hz'.ne'
  rw [hc] at hr
  have hd : ent g 1 1 = 0 := by simpa using hr
  have := det_pos g
  rw [hc, hd] at this
  simp at this

theorem mob_mem (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  have hne := denom_ne g hz
  have e : mob g z = ((((ent g 0 0 : ℝ)) : ℂ) * z + ((ent g 0 1 : ℝ) : ℂ)) /
      ((((ent g 1 0 : ℝ)) : ℂ) * z + ((ent g 1 1 : ℝ) : ℂ)) := by
    simp [mob]
  show 0 < (mob g z).im
  rw [e, im_frac]
  have hn : 0 < Complex.normSq ((((ent g 1 0 : ℝ)) : ℂ) * z + ((ent g 1 1 : ℝ) : ℂ)) := by
    rw [Complex.normSq_pos]; simpa using hne
  have hd : (0 : ℝ) < (ent g 0 0 : ℝ) * (ent g 1 1 : ℝ) - (ent g 0 1 : ℝ) * (ent g 1 0 : ℝ) := by
    exact_mod_cast det_pos g
  have hz' : 0 < z.im := hz
  positivity

theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem frac_comp (a b c d N D : ℂ) (hD : D ≠ 0) :
    (a * (N / D) + b) / (c * (N / D) + d) = (a * N + b * D) / (c * N + d * D) := by
  rw [show a * (N / D) + b = (a * N + b * D) / D by field_simp,
    show c * (N / D) + d = (c * N + d * D) / D by field_simp, div_div_div_cancel_right₀ hD]

theorem mob_mul (g h : GQ) {z : ℂ} (hz : z ∈ Hs) : mob (g * h) z = mob g (mob h z) := by
  have hne := denom_ne h hz
  simp only [mob, ent_mul]
  push_cast
  rw [frac_comp _ _ _ _ _ _ hne]
  congr 1 <;> ring

theorem mob_one (z : ℂ) : mob 1 z = z := by simp [mob, ent]

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  have hne := denom_ne g hz
  show DifferentiableWithinAt ℂ (fun z : ℂ => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) /
    ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) Hs z
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) z := by fun_prop
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) z := by fun_prop
  exact (h1.div h2 hne).differentiableWithinAt

theorem mob_upper (g : GQ) (hc : ent g 1 0 = 0) : 0 < ent g 0 0 / ent g 1 1 ∧
    ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) := by
  have hdet := det_pos g
  rw [hc, mul_zero, sub_zero] at hdet
  have hd : ent g 1 1 ≠ 0 := by rintro h; rw [h, mul_zero] at hdet; exact lt_irrefl _ hdet
  refine ⟨?_, fun z => ?_⟩
  · have : ent g 0 0 / ent g 1 1 = ent g 0 0 * ent g 1 1 / (ent g 1 1 * ent g 1 1) := by
      field_simp
    rw [this]; exact div_pos hdet (mul_self_pos.2 hd)
  · have hd' : (ent g 1 1 : ℂ) ≠ 0 := by exact_mod_cast hd
    simp only [mob, hc]
    push_cast
    simp only [zero_mul, zero_add]
    rw [add_div, mul_div_right_comm]

end GlobalTheory.FNMob

theorem GlobalTheory.FN.mob_props : (∀ (g : GQ) (z : ℂ), z ∈ Hs → mob g z ∈ Hs) ∧ (∀ (g h : GQ) (z : ℂ), z ∈ Hs → mob (g * h) z = mob g (mob h z)) ∧ (∀ z : ℂ, mob 1 z = z) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ)) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ ∀ g : GQ, ent g 1 0 = 0 → 0 < ent g 0 0 / ent g 1 1 ∧ ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) :=
  ⟨fun g _ hz => GlobalTheory.FNMob.mob_mem g hz, fun g h _ hz => GlobalTheory.FNMob.mob_mul g h hz, GlobalTheory.FNMob.mob_one,
    GlobalTheory.FNMob.mob_ofSL, GlobalTheory.FNMob.mob_diff, GlobalTheory.FNMob.mob_upper⟩
end

section

open Matrix GlobalTheory.KZ
open Filter Topology

theorem _root_.GlobalTheory.T.an_meromorphicAt_upperHalfPlane : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K) (φ : ℂ → ℂ), X.an x = (φ : Mero) → ∀ τ : ℂ, τ ∈ Hs → MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := by
  first | exact @GlobalTheory.KZ.Tower.an_meromorphicAt | exact GlobalTheory.KZ.Tower.an_meromorphicAt | (intros; apply GlobalTheory.KZ.Tower.an_meromorphicAt <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRoots

theorem alg_mem_range (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (z : ℂ) (hz : IsAlgebraic ℚ z) : z ∈ ε.range := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hi : IsIntegral ℚ z := hz.isIntegral
  set p := minpoly ℚ z with hp
  have hm : p.Monic := minpoly.monic hi
  have hqm : (p.map (algebraMap ℚ Ω)).Monic := hm.map _
  have hroots := hqm.roots_map_of_card_eq_natDegree ε IsAlgClosed.card_roots_eq_natDegree
  have hcomp : ε.comp (algebraMap ℚ Ω) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  rw [Polynomial.map_map, hcomp] at hroots
  have hne : p.map (algebraMap ℚ ℂ) ≠ 0 := (hm.map _).ne_zero
  have hzr : z ∈ (p.map (algebraMap ℚ ℂ)).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact minpoly.aeval ℚ z
  rw [← hroots] at hzr
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hzr
  exact ⟨w, hw⟩

theorem exp_isAlgebraic (x : ℚ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) := by
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hx : (x : ℂ) = (x.num : ℂ) / (x.den : ℂ) := by
        exact_mod_cast (Rat.num_div_den x).symm
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_nz
      rw [hx]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  refine ⟨Polynomial.X ^ x.den - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero x.pos 1, ?_⟩
  simp [hpow]

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range) ∧ (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ eOm ε 0 = 1 ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ N : ℕ, 0 < N → IsPrimitiveRoot (eOm ε (1 / N)) N) ∧ ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ ε.range := by
  intro Ω _ _ _ ε
  have hr : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range :=
    fun x => alg_mem_range Ω ε _ (exp_isAlgebraic x)
  have he : ∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
    intro x
    obtain ⟨w, hw⟩ := hr x
    exact Function.invFun_eq ⟨w, hw⟩
  have hinj : Function.Injective ε := ε.injective
  refine ⟨hr, he, ?_, ?_, ?_, fun z hz => alg_mem_range Ω ε z hz⟩
  · apply hinj; rw [he, map_one]; simp
  · intro x y; apply hinj
    rw [map_mul, he, he, he, ← Complex.exp_add]; congr 1; push_cast; ring
  · intro N hN
    apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ hinj
    rw [he]
    have h := Complex.isPrimitiveRoot_exp N hN.ne'
    convert h using 2
    push_cast; ring

end GlobalTheory.FNRoots
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.towerGaloisAction_preserves_gammaLevel : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := by
  first | exact @GlobalTheory.Tower.gal_level | exact GlobalTheory.Tower.gal_level | (intros; apply GlobalTheory.Tower.gal_level <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exponents_integral_of_translation_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K), X.sl (ofSL ModularGroup.T) h = h → ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ m : ℤ, r = m := by
  first | exact @GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant | exact GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant | (intros; apply GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant <;> assumption)
end
