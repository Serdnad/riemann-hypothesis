module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle053
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCocyclesLeGamma1
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle113
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle115
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
import Mathlib.Geometry.Manifold.StructureGroupoid
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.JStab

theorem eps_eOm_of_alg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  apply GlobalTheory.Glue.KTExp.map_eOm <;> assumption

theorem eOm_ne_zero' {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    eOm ε x ≠ 0 := by
  intro h0
  have := eps_eOm_of_alg ε x
  rw [h0, map_zero] at this
  exact Complex.exp_ne_zero _ this.symm

end GlobalTheory.KZ.ES.JStab
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) (N : ℕ), 0 < N → (∃ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d) ∧ ∀ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∃ u : (ZMod N)ˣ, (u : ZMod N) = d ∧ ∀ g : ℂ ≃+* ℂ, (∀ x, g (ε x) = ε (s x)) → ZetaAct g N u := by
  first | exact @GlobalTheory.ZetaExp.main | exact GlobalTheory.ZetaExp.main | (intros; apply GlobalTheory.ZetaExp.main <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem map_mapGL_rat (σ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ σ) =
      Matrix.SpecialLinearGroup.mapGL ℝ σ := by
  ext i j
  simp

theorem isZeroAt_sum {c : OnePoint ℝ} {k : ℤ} {ι : Type} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (F i) k) : c.IsZeroAt (∑ i ∈ s, F i) k := by
  refine Finset.sum_induction F (fun G => c.IsZeroAt G k) (fun a b ha hb => ha.add hb) ?_ h
  intro g _
  show IsZeroAtImInfty ((0 : ℍ → ℂ) ∣[k] g)
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

theorem heckeT_cuspForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k,
    ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  intro N l q k σ hN hq hql hσ f
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at hql
    · exact h
  have hq0 : 0 < q := hq.pos
  have hinv := GlobalTheory.T.heckeT_slash_eq_of_slash_eq N l q k σ (⇑f) hN hq hql hσ
    (fun γ hγ => by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩)
  have hhol := (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k σ (⇑f) hq0 (CuspFormClass.holo f)).2.2
  refine ⟨{ toFun := GlobalTheory.Hk.heckeT k q σ ⇑f
            slash_action_eq' := ?_
            holo' := hhol
            zero_at_cusps' := ?_ }, rfl⟩
  · rintro A ⟨γ, hγ, rfl⟩
    exact hinv γ hγ
  · intro c hc
    show c.IsZeroAt (GlobalTheory.Hk.heckeT k q σ ⇑f) k
    rw [GlobalTheory.Hk.heckeT, GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq0, GlobalTheory.T.pow_smul_heckeVOperatorExplicit_eq_slash_diag q k _ hq0, ModularForm.SL_slash,
      ← SlashAction.slash_mul]
    refine OnePoint.IsZeroAt.add (isZeroAt_sum _ _ fun j _ => ?_) ?_
    · exact GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
    · have h := GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt N l k (Matrix.SpecialLinearGroup.mapGL ℚ σ *
        Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1]
          (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0.ne')) hN hl
        (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
      rw [map_mul, map_mapGL_rat] at h
      exact h

end GlobalTheory.Hk
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.glTwoPosRatMobius_basic_laws : (∀ (g : GQ), ∀ z ∈ Hs, mob g z ∈ Hs) ∧ (∀ (g h : GQ), ∀ z ∈ Hs, mob (g * h) z = mob g (mob h z)) ∧ (∀ z, mob 1 z = z) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ (∀ γ : SL(2, ℤ), toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ) ∧ (∀ m m' : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det → 0 < m'.det → toGQ (m * m') = toGQ m * toGQ m') := by
  first | exact @GlobalTheory.KZ.mob_laws | exact GlobalTheory.KZ.mob_laws | (intros; apply GlobalTheory.KZ.mob_laws <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isDia_mul {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : IsDia N l d σ) (hτ : IsDia N l e τ) :
    IsDia N l (d * e) (σ * τ) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  obtain ⟨hτ0, hτ1⟩ := hτ
  have hσ0' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    have := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hσ0
    simpa using this
  constructor
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hσ0, hτ0]; ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hσ0', hσ1, hτ1]; ring

theorem dia_mul : ∀ (N l : ℕ) (k d e : ℤ) (σ τ ρ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    GlobalTheory.Hk.IsDia N l e τ → GlobalTheory.Hk.IsDia N l (d * e) ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.dia k τ (GlobalTheory.Hk.dia k σ ⇑f) = GlobalTheory.Hk.dia k ρ ⇑f := by
  intro N l k d e σ τ ρ hN hσ hτ hρ f
  have h := GlobalTheory.T.diamondOperatorOfMatrix_congr N l k (d * e) (σ * τ) ρ hN (isDia_mul hσ hτ) hρ f
  rw [← h]
  simp only [dia]
  rw [SlashAction.slash_mul]

end GlobalTheory.Hk
end

section

noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.LevelOne

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem eq_const_of_nonneg [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (h : X.K) (hinv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h)
    (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs) (ha : X.an h = (φ : Mero))
    (hneg : ∀ r : ℚ, r < 0 → (X.exp h).coeff r = 0) :
    h = algebraMap Ω X.K ((X.exp h).coeff 0) := by
  set a0 := (X.exp h).coeff 0 with ha0
  have hsupp : ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n := by
    intro r hr
    obtain ⟨m, rfl⟩ := GlobalTheory.T.exponents_integral_of_translation_invariant X h (hinv _) r hr
    have hm : 0 ≤ m := by
      by_contra hm
      exact hr (hneg _ (by exact_mod_cast (not_le.1 hm)))
    exact ⟨m.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hm]⟩
  obtain ⟨B, t, hB⟩ := GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential X h φ hd.continuousOn ha hsupp
  have hinvφ := GlobalTheory.T.modularTower_function_slTwoInt_invariant X h φ hd.continuousOn ha hinv
  have hexp1 : ∀ z : ℂ, t < z.im → Real.exp (-(2 * Real.pi * (z.im - t))) ≤ 1 := by
    intro z hz
    rw [Real.exp_le_one_iff]
    have : 0 < z.im - t := by linarith
    have := Real.pi_pos
    nlinarith
  obtain ⟨c, hc⟩ := GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane φ hd hinvφ ⟨‖ε a0‖ + |B|, t, fun z hz hzt => by
    have h1 := hB z hz hzt
    have h2 := hexp1 z hzt
    have h3 : B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| := by
      calc B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| * Real.exp (-(2 * Real.pi * (z.im - t))) :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
        _ ≤ |B| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
        _ = |B| := mul_one _
    calc ‖φ z‖ = ‖(φ z - ε a0) + ε a0‖ := by ring_nf
      _ ≤ ‖φ z - ε a0‖ + ‖ε a0‖ := norm_add_le _ _
      _ ≤ ‖ε a0‖ + |B| := by linarith⟩
  have hca : c = ε a0 := by
    have hle : ∀ s : ℝ, max t 0 < s → ‖c - ε a0‖ ≤ B * Real.exp (-(2 * Real.pi * (s - t))) := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
      have hst : t < s := lt_of_le_of_lt (le_max_left _ _) hs
      have hz : ((s : ℂ) * Complex.I) ∈ Hs := by simp [Hs, hs0]
      have := hB _ hz (by simpa using hst)
      rw [hc _ hz] at this
      simpa using this
    have ht : Filter.Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.const_mul_atTop Real.two_pi_pos
        exact Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
      simpa using h2
    have h0 : ‖c - ε a0‖ ≤ 0 := ge_of_tendsto ht (Filter.eventually_gt_atTop (max t 0) |>.mono hle)
    have := norm_le_zero_iff.1 h0
    exact sub_eq_zero.1 this
  apply SiegelModel.an_injective X
  rw [ha, X.an_c]
  exact SiegelModel.germ_eq_of_eqOn fun z hz => by rw [hc z hz, hca]

theorem mem_adjoin_j : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ h : X.K,
    (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
    h ∈ Algebra.adjoin Ω {X.jK} := by
  intro Ω _ _ _ ε X _ hj
  obtain ⟨ψ, hψ, hψa⟩ := hj
  have key : ∀ n : ℕ, ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
      (∀ r : ℚ, r < -(n : ℚ) → (X.exp h).coeff r = 0) → h ∈ Algebra.adjoin Ω {X.jK} := by
    intro n
    induction n with
    | zero =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      rw [eq_const_of_nonneg X h hinv φ hd ha (by simpa using hneg)]
      exact Subalgebra.algebraMap_mem _ _
    | succ n ih =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      obtain ⟨c, hcdef⟩ : ∃ c : Ω, c = (X.exp h).coeff (-((n + 1 : ℕ) : ℚ)) := ⟨_, rfl⟩
      obtain ⟨h', hh'⟩ : ∃ h' : X.K, h' = h - algebraMap Ω X.K c * X.jK ^ (n + 1) := ⟨_, rfl⟩
      have hj := GlobalTheory.T.hahnSeries_pow_of_leading_qInv (X.exp X.jK) X.j_exp.1 X.j_exp.2.1 (n + 1)
      have hinv' : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h' = h' := by
        intro γ
        rw [hh', map_sub, map_mul, map_pow, X.j_inv, hinv, AlgEquiv.commutes]
      have hol' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h' = (φ : Mero) := by
        refine ⟨fun z => φ z - ε c * ψ z ^ (n + 1), ?_, ?_⟩
        · exact hd.sub ((hψ.pow _).const_mul _)
        · rw [hh', map_sub, map_mul, map_pow, X.an_c, ha, hψa]
          rfl
      have hneg' : ∀ r : ℚ, r < -(n : ℚ) → (X.exp h').coeff r = 0 := by
        intro r hr
        by_contra hrz
        obtain ⟨m, rfl⟩ := GlobalTheory.T.exponents_integral_of_translation_invariant X h' (hinv' _) r hrz
        apply hrz
        have hcoe : (X.exp h').coeff (m : ℚ) =
            (X.exp h).coeff m - c * ((X.exp X.jK) ^ (n + 1)).coeff m := by
          rw [hh', map_sub, map_mul, AlgHom.commutes, map_pow, HahnSeries.coeff_sub, HahnSeries.algebraMap_apply',
            PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C,
            HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
        rw [hcoe]
        have hm : m ≤ -((n : ℤ) + 1) := by
          have : (m : ℚ) < -(n : ℚ) := hr
          have : m < -(n : ℤ) := by exact_mod_cast this
          omega
        rcases hm.lt_or_eq with hlt | heq
        · have hq : (m : ℚ) < -((n + 1 : ℕ) : ℚ) := by push_cast; exact_mod_cast hlt
          rw [hneg _ hq, hj.2 _ hq]
          ring
        · have hq : (m : ℚ) = -((n + 1 : ℕ) : ℚ) := by rw [heq]; push_cast; ring
          rw [hq, hj.1, hcdef]
          ring
      have hmem := ih h' hinv' hol' hneg'
      have hsum : h = h' + algebraMap Ω X.K c * X.jK ^ (n + 1) := by rw [hh']; abel
      have hjm : X.jK ∈ Algebra.adjoin Ω {X.jK} := Algebra.self_mem_adjoin_singleton Ω X.jK
      rw [hsum]
      exact add_mem hmem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hjm _))
  intro h hinv hol
  refine key ⌈-(X.exp h).order⌉₊ h hinv hol fun r hr => HahnSeries.coeff_eq_zero_of_lt_order ?_
  have := Nat.le_ceil (-(X.exp h).order)
  linarith

end GlobalTheory.KZ.LevelOne
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.chosenDiamondMatrix_letterOperators_cosetSums : ∀ (N l : ℕ), 0 < N → l.Prime → ¬ l ∣ N → (∀ d : ℕ, Nat.Coprime d N → GlobalTheory.HeckeFamilyMatrices.IsDiam N l (d : ZMod N) (sgD N l d)) ∧ (∀ q : ℕ, opL ℂ N l (Letter.T q) = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.tqFam q (sgD N l q) i)) ∧ opL ℂ N l Letter.U = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.ulFam l i) ∧ ∀ d : ℕ, opL ℂ N l (Letter.D d) = ∑ _i : Unit, opP ℂ (GlobalTheory.HeckeFamilyMatrices.mat (sgD N l d)) := by
  first | exact @GlobalTheory.KZ.DiamondOperatorFamilies.sgD_fams | exact GlobalTheory.KZ.DiamondOperatorFamilies.sgD_fams | (intros; apply GlobalTheory.KZ.DiamondOperatorFamilies.sgD_fams <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.finrank_z1_le_of_le_gamma1_of_finiteIndex : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → FiniteDimensional ℂ (Z1 Γ w) ∧ 12 * Module.finrank ℂ (Z1 Γ w) ≤ (w + 1) * (12 + Γ.index) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 | exact GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 | (intros; apply GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerPeriodPolynomial_limit_at_cusp : ∀ (k : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]) (σ : SL(2, ℤ)) (Cf cf Ch ch : ℝ), 2 ≤ k → 0 < cf → 0 < ch → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[(k : ℤ)] σ) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h ∣[(k : ℤ)] σ) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(f ∣[(k : ℤ)] σ) τ‖ ≤ Cf * Real.exp (-cf * τ.im)) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(h ∣[(k : ℤ)] σ) τ‖ ≤ Ch * Real.exp (-ch * τ.im)) → p ∈ degreeLT ℂ (k - 1) → ∃ (Q : ℂ[X]) (C' c : ℝ), Q ∈ degreeLT ℂ (k - 2 + 1) ∧ 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ k - 2, ‖(slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p) - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (k - 2) := by
  first | exact @GlobalTheory.EichlerLimit.polySlash_eichler_limit | exact GlobalTheory.EichlerLimit.polySlash_eichler_limit | (intros; apply GlobalTheory.EichlerLimit.polySlash_eichler_limit <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.hecke_Ul_sq_sub_mem_oldforms_Gamma1 : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Lev N l) (k : ℤ)),
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) ∧
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) ∧
    UlF (k : ℤ) l (UlF (k : ℤ) l ⇑f) - (χ l * (l : ℂ) ^ (k - 2)) • ⇑f = ⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulSq_old | exact GlobalTheory.HeckeFamilyMatrices.ulSq_old | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulSq_old <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.kummer_generator_approx_critical_radius : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → v (p : L) < 1 → ∀ α : L, α ^ p ∈ F → 0 < v (p : L) → ∀ s : ℝ≥0, 1 < s → ∃ y ∈ F, v (α - y) ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := by
  first | exact @GlobalTheory.AlmostEt.kummer_approx_critical | exact GlobalTheory.AlmostEt.kummer_approx_critical | (intros; apply GlobalTheory.AlmostEt.kummer_approx_critical <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → (∀ u ∈ aug π H θ, IsEig π H θ u → u = 0) ∧ ∀ w : V, ∃ w' : V, IsEig π H θ w' ∧ w - w' ∈ aug π H θ := by
  first | exact @GlobalTheory.PsType.eig_compl_aug | exact GlobalTheory.PsType.eig_compl_aug | (intros; apply GlobalTheory.PsType.eig_compl_aug <;> assumption)
end
