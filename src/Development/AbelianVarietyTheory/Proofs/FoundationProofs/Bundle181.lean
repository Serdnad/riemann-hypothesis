module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exp_sl_coeff_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (T : Frac Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : T.K) (r : ℚ) :
    (T.exp (T.sl g f)).coeff (r * ent g 0 0 / ent g 1 1) =
      eOm ε (r * ent g 0 1 / ent g 1 1) * (T.exp f).coeff r := by
  obtain ⟨hl, hmob⟩ := (GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties).2.2.2.2.2 g hg
  obtain ⟨_, hε, h0, hadd, _, _⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (RingHom.id Ω) (ent g 0 0 / ent g 1 1)
    (fun r => eOm ε (r * (ent g 0 1 / ent g 1 1))) hl (by simpa using h0)
    (fun r r' => by simp only [add_mul, hadd])
  have key : (T.exp.toRingHom.comp (T.sl g).toRingEquiv.toRingHom) = Φ.comp T.exp.toRingHom := by
    apply (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1
    intro a
    obtain ⟨a', ha', hsl⟩ := (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a
    have hE : IsExp ε a' (Φ (T.exp (T.io a))) := by
      refine GlobalTheory.T.isCuspExpansionAtInfinity_comp_rat_affine Ω ε a a' (ent g 0 0 / ent g 1 1) (ent g 0 1 / ent g 1 1) _ _ hl
        (fun z hz => ?_) (fun s => ?_) (T.exp_io a)
      · rw [ha', (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz, hmob z]
      · rw [hΦ, map_mul, hε]
        rfl
    have hu := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 _ _ _ (T.exp_io a') hE
    show T.exp (T.sl g (T.io a)) = Φ (T.exp (T.io a))
    rw [hsl, hu]
  have hc := congrArg (fun h : HahnSeries ℚ Ω => h.coeff (r * (ent g 0 0 / ent g 1 1)))
    (RingHom.congr_fun key f)
  simp only [RingHom.comp_apply] at hc
  rw [mul_div_assoc, mul_div_assoc]
  refine (show (T.exp (T.sl g f)).coeff (r * (ent g 0 0 / ent g 1 1)) = _ from hc).trans ?_
  rw [hΦ]
  rfl

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_const_and_quot : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ c : Ω, T.an (algebraMap Ω T.K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)) ∧ ∀ f : T.K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T
  have hmem := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs := fun a =>
    ((GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict).2.1 _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ε.range _ ((hmem.1 _).1 a.2))
  refine ⟨fun c => ?_, fun f => ?_⟩
  · have hc : (fun _ : ℍ => ε c) ∈ ring ε.range := (hmem.1 _).2 (hmem.2 _ ⟨c, rfl⟩)
    rw [← T.io_c c ⟨_, hc⟩ rfl, T.an_io]
    rfl
  · obtain ⟨a, b, hb, h⟩ := T.io_surj f
    refine ⟨up (a : ℍ → ℂ), up (b : ℍ → ℂ), hdiff a, hdiff b, ?_, ?_⟩
    · intro h0
      have h1 : T.an (T.io b) = T.an (T.io 0) := by
        rw [T.an_io, map_zero, map_zero]; exact h0
      exact hb (T.io_inj ((GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.2.2 h1))
    · have := congrArg T.an h
      rw [map_mul, T.an_io, T.an_io] at this
      exact this

end GlobalTheory.FN
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.OnGammaOne

theorem slash_inv {k L N : ℕ} {ε : DirichletCharacter ℂ N} (hNL : N ∣ L) {f : ℍ → ℂ}
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 L) : f ∣[(k : ℤ)] γ = f := by
  obtain ⟨-, h11, h10⟩ := (Gamma1_mem L γ).1 hγ
  have hc : (L : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
  have hd1 : (L : ℤ) ∣ γ 1 1 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11, sub_self]
  have hd : ch ε (γ 1 1) = 1 := by
    have h2 : (N : ℤ) ∣ γ 1 1 - 1 := (Int.natCast_dvd_natCast.2 hNL).trans hd1
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    have h3 : ((γ 1 1 : ℤ) : ZMod N) = 1 := sub_eq_zero.1 h2
    simp [ch, h3]
  funext τ
  rw [ModularForm.slash_action_eq'_iff, hf γ hc τ, hd, one_mul, zpow_natCast]

theorem periodic {k L : ℕ} {f : ℍ → ℂ} (hinv : ∀ γ ∈ Gamma1 L, f ∣[(k : ℤ)] γ = f)
    (γ : SL(2, ℤ)) (τ : ℍ) : (f ∣[(k : ℤ)] γ) ((L : ℝ) +ᵥ τ) = (f ∣[(k : ℤ)] γ) τ := by
  have hT : (ModularGroup.T ^ (L : ℤ)) • τ = (L : ℝ) +ᵥ τ := by
    rw [modular_T_zpow_smul]; simp
  have hδ : γ * ModularGroup.T ^ (L : ℤ) * γ⁻¹ ∈ Gamma1 L := by
    have h1 : ModularGroup.T ^ (L : ℤ) ∈ CongruenceSubgroup.Gamma L := by
      simpa using ModularGroup_T_pow_mem_Gamma (L : ℤ) (L : ℤ) dvd_rfl
    have h2 := (Gamma_normal L).conj_mem _ h1 γ
    rw [Gamma_mem] at h2
    rw [Gamma1_mem]
    exact ⟨h2.1, h2.2.2.2, h2.2.2.1⟩
  have e : (f ∣[(k : ℤ)] γ) ∣[(k : ℤ)] (ModularGroup.T ^ (L : ℤ)) = f ∣[(k : ℤ)] γ := by
    rw [← SlashAction.slash_mul,
      (inv_mul_cancel_right (γ * ModularGroup.T ^ (L : ℤ)) γ).symm,
      SlashAction.slash_mul, hinv _ hδ]
  have h := congrFun e τ
  have hden : denom (ModularGroup.T ^ (L : ℤ) : SL(2, ℤ)) τ = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
  rw [ModularForm.SL_slash_apply (f := f ∣[(k : ℤ)] γ), hT, hden, one_zpow, mul_one] at h
  exact h

end GlobalTheory.EisM.OnGammaOne

namespace GlobalTheory.EisM.OnGammaOne

theorem normSq_denom_bounds (L : ℕ) (γ : SL(2, ℤ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ L →
      1 ≤ Complex.normSq (denom γ τ) ∧ Complex.normSq (denom γ τ) ≤ K * τ.im ^ 2 := by
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ)
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ)
  refine ⟨(|c| * L + |d|) ^ 2 + c ^ 2, by positivity, fun τ h1 h2 => ?_⟩
  have hns : Complex.normSq (denom γ τ) = (c * τ.re + d) ^ 2 + (c * τ.im) ^ 2 := by
    rw [ModularGroup.denom_apply, Complex.normSq_apply]
    simp [c, d]
    ring
  rw [hns]
  have hy0 : 0 ≤ τ.im := τ.im_pos.le
  have hy2 : 1 ≤ τ.im ^ 2 := by nlinarith
  constructor
  · by_cases hc : γ 1 0 = 0
    · have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have := γ.2; rw [Matrix.det_fin_two] at this; exact this
      rw [hc, mul_zero, sub_zero] at hdet
      have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2
      have hc' : c = 0 := by simp [c, hc]
      have hd' : d ^ 2 = 1 := by rcases hd with h | h <;> simp [d, h]
      rw [hc']; nlinarith
    · have hc1 : 1 ≤ c ^ 2 := by
        have : (1 : ℤ) ≤ (γ 1 0) ^ 2 := by
          have := Int.one_le_abs hc
          nlinarith [sq_abs (γ 1 0)]
        have : ((1 : ℤ) : ℝ) ≤ (((γ 1 0) ^ 2 : ℤ) : ℝ) := by exact_mod_cast this
        simpa [c] using this
      nlinarith [sq_nonneg (c * τ.re + d)]
  · have hM : |c * τ.re + d| ≤ |c| * L + |d| := by
      calc |c * τ.re + d| ≤ |c * τ.re| + |d| := abs_add_le _ _
        _ = |c| * |τ.re| + |d| := by rw [abs_mul]
        _ ≤ |c| * L + |d| := by gcongr
    have hM2 : (c * τ.re + d) ^ 2 ≤ (|c| * L + |d|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hM0 : 0 ≤ (|c| * L + |d|) ^ 2 := by positivity
    nlinarith

theorem growth {f : ℍ → ℂ} (hf : Mod f) (k L : ℕ) (γ : SL(2, ℤ)) :
    ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ L → ‖(f ∣[(k : ℤ)] γ) τ‖ ≤ C * τ.im ^ A := by
  obtain ⟨C, A, hC⟩ := hf
  obtain ⟨K, hK0, hK⟩ := normSq_denom_bounds L γ
  refine ⟨|C| * (1 + K ^ A), A, fun τ h1 h2 => ?_⟩
  obtain ⟨hD1, hDK⟩ := hK τ h1 h2
  set D := Complex.normSq (denom γ τ) with hD
  set y := τ.im with hy
  have hy0 : 0 < y := τ.im_pos
  have hD0 : 0 < D := by linarith
  have him : (γ • τ).im = y / D := ModularGroup.im_smul_eq_div_normSq γ τ
  have hw1 : (γ • τ).im ^ A ≤ y ^ A := by
    rw [him]
    exact pow_le_pow_left₀ (by positivity) (div_le_self hy0.le hD1) A
  have hw2 : ((γ • τ).im ^ A)⁻¹ ≤ K ^ A * y ^ A := by
    rw [him, ← inv_pow, inv_div, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ A
    rw [div_le_iff₀ hy0]
    nlinarith
  have hden : ‖denom γ τ ^ (-(k : ℤ))‖ ≤ 1 := by
    have hn : 1 ≤ ‖denom γ τ‖ := by
      have : 1 ≤ ‖denom γ τ‖ ^ 2 := by rw [← Complex.normSq_eq_norm_sq]; exact hD1
      nlinarith [norm_nonneg (denom γ τ)]
    rw [norm_zpow, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hn)
  rw [ModularForm.SL_slash_apply, norm_mul]
  have hfw := hC (γ • τ)
  have hpos : 0 ≤ (γ • τ).im ^ A + ((γ • τ).im ^ A)⁻¹ := by
    have := (γ • τ).im_pos; positivity
  calc ‖f (γ • τ)‖ * ‖denom γ τ ^ (-(k : ℤ))‖ ≤ ‖f (γ • τ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ ≤ |C| * ((γ • τ).im ^ A + ((γ • τ).im ^ A)⁻¹) := by
        rw [mul_one]; exact hfw.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpos)
    _ ≤ |C| * (y ^ A + K ^ A * y ^ A) := by gcongr
    _ = |C| * (1 + K ^ A) * y ^ A := by ring

end GlobalTheory.EisM.OnGammaOne


open GlobalTheory.EisM.OnGammaOne in
theorem GlobalTheory.EisM.modularForm_gammaOne_of_MF :
    ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 0 < L → N ∣ L → MF k L (ch ε) a →
      ∃ f : ModularForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  intro k L N ε a hL hNL ha
  haveI : NeZero L := ⟨hL.ne'⟩
  have hinv : ∀ γ ∈ Gamma1 L, qs a ∣[(k : ℤ)] γ = qs a := fun γ hγ => slash_inv hNL ha.2 γ hγ
  have hhol := GlobalTheory.T.mdifferentiable_qExpansion_of_coeffPolynomialGrowth a ha.1
  refine ⟨{ toFun := qs a, slash_action_eq' := ?_, holo' := hhol, bdd_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨A, (hA : A ∈ Gamma1 L), rfl⟩
    exact hinv A hA
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    obtain ⟨C, A, hC⟩ := growth (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1) k L γ
    have hs : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a ∣[(k : ℤ)] γ) := by
      rw [ModularForm.SL_slash]; exact hhol.slash _ _
    exact GlobalTheory.T.isBoundedAtImInfty_of_periodic_polynomial_bound _ L C A hL hs (periodic hinv γ) hC
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

def hch (n : ℕ) (x : ℝ) : ℂ := cexp (2 * π * Complex.I * n * x)

theorem hch_norm (n : ℕ) (x : ℝ) : ‖hch n x‖ = 1 := by
  have : (2 * π * Complex.I * n * x : ℂ) = ((2 * π * n * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hch, this, Complex.norm_exp_ofReal_mul_I]

theorem hch_cont (n : ℕ) : Continuous (hch n) := by unfold hch; fun_prop

theorem hch_orth (m n : ℕ) : ∫ x in (0 : ℝ)..1, conj (hch m x) * hch n x = if m = n then 1 else 0 := by
  have e : ∀ x : ℝ, conj (hch m x) * hch n x = cexp ((2 * π * Complex.I * ((n : ℂ) - m)) * x) := fun x => by
    rw [hch, hch, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
    ring
  simp only [e]
  split_ifs with h
  · simp [h]
  · have h0 : ((n : ℂ) - m) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast Ne.symm h)
    have hc : (2 * π * Complex.I * ((n : ℂ) - m)) ≠ 0 := mul_ne_zero Complex.two_pi_I_ne_zero h0
    rw [integral_exp_mul_complex hc]
    have := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
    push_cast at this
    rw [mul_comm] at this
    simp [this]

theorem hasSum_parseval_unit (a b : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (F G : ℝ → ℂ) (hF : ∀ x, HasSum (fun n => a n * hch n x) (F x))
    (hG : ∀ x, HasSum (fun n => b n * hch n x) (G x)) :
    HasSum (fun n => conj (b n) * a n) (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
  let T : ℕ × ℕ → ℝ → ℂ := fun p x => conj (b p.1 * hch p.1 x) * (a p.2 * hch p.2 x)
  have hT : ∀ p, Continuous (T p) := fun p =>
    (Complex.continuous_conj.comp (continuous_const.mul (hch_cont p.1))).mul
      (continuous_const.mul (hch_cont p.2))
  have hn : ∀ p x, ‖T p x‖ = ‖b p.1‖ * ‖a p.2‖ := fun p x => by
    simp [T, hch_norm]
  have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := T)
    (fun p => (hT p).integrableOn_Ioc) (by
      refine (summable_mul_of_summable_norm' hb.norm hb ha.norm ha).congr fun p => ?_
      simp only [hn]
      simp)
  have hs : ∀ x, ∑' p, T p x = conj (G x) * F x := fun x => by
    have h1 : HasSum (fun n => conj (b n * hch n x)) (conj (G x)) := by
      simpa using (Complex.hasSum_conj'.2 (hG x))
    have h2 := tsum_mul_tsum_of_summable_norm h1.summable.norm (hF x).summable.norm
    rw [h1.tsum_eq, (hF x).tsum_eq] at h2
    exact h2.symm
  have hi : ∀ p, ∫ x in Set.Ioc (0 : ℝ) 1, T p x = conj (b p.1) * a p.2 * if p.1 = p.2 then 1 else 0 := fun p => by
    rw [← hch_orth, ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    simp only [T, map_mul]
    ring
  simp only [hs, hi] at h
  rw [← intervalIntegral.integral_of_le zero_le_one] at h
  have hinj : Function.Injective fun n : ℕ => (n, n) := fun _ _ h => (Prod.ext_iff.1 h).1
  have := (hinj.hasSum_iff (f := fun p : ℕ × ℕ => conj (b p.1) * a p.2 * if p.1 = p.2 then 1 else 0) (fun p hp => by
    rw [if_neg, mul_zero]
    intro h
    exact hp ⟨p.1, Prod.ext rfl h⟩)).2 h
  refine cast (congrArg (HasSum · _) (funext fun n => ?_)) this
  simp

theorem qs_line (a : ℕ → ℂ) (ha : PolyB a) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun n : ℕ => (a n * (Real.exp (-2 * π * n * y) : ℝ)) * hch n x)
      (qs a (ofComplex (x + y * Complex.I))) := by
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
  have hterm : ∀ n : ℕ, a n * cexp (2 * π * Complex.I * n * (ofComplex ((x : ℂ) + y * Complex.I) : ℂ)) =
      (a n * (Real.exp (-2 * π * n * y) : ℝ)) * hch n x := fun n => by
    rw [ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_mk, hch, Complex.ofReal_exp, mul_assoc (a n), ← Complex.exp_add]
    congr 2
    push_cast
    linear_combination (2 * π * n * y : ℂ) * Complex.I_mul_I
  have hs := ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 (ofComplex ((x : ℂ) + y * Complex.I))).of_norm
  have := hs.hasSum
  simp only [qs]
  simpa only [hterm] using this

theorem parseval_line : ∀ (h b : ℕ → ℂ) (y : ℝ), PolyB h → PolyB b → 0 < y →
    HasSum (fun n : ℕ => conj (h n) * b n * (Real.exp (-4 * π * n * y) : ℝ))
      (∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I))) := by
  intro h b y hh hb hy
  have sm : ∀ a : ℕ → ℂ, PolyB a → Summable fun n : ℕ => ‖a n * (Real.exp (-2 * π * n * y) : ℝ)‖ := fun a ha => by
    have := (qs_line a ha y hy 0).summable.norm
    simpa [hch_norm] using this
  have H := hasSum_parseval_unit _ _ (sm b hb) (sm h hh) _ _ (qs_line b hb y hy) (qs_line h hh y hy)
  refine cast (congrArg (HasSum · _) (funext fun n => ?_)) H
  have : Real.exp (-4 * π * n * y) = Real.exp (-2 * π * n * y) * Real.exp (-2 * π * n * y) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

end GlobalTheory.EisM
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem polyB_mul (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : PolyB (mul a b) := by
  obtain ⟨C, A, hC⟩ := ha
  obtain ⟨C', A', hC'⟩ := hb
  have C0 : 0 ≤ C := by
    have := hC 0
    simp at this
    exact le_trans (norm_nonneg _) this
  have C0' : 0 ≤ C' := by
    have := hC' 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C * C', A + A' + 1, fun n => ?_⟩
  unfold mul
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2‖
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖a p.1 * b p.2‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, C * C' * ((n : ℝ) + 1) ^ (A + A') := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [norm_mul]
        have h1 : ((p.1 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : p.1 ≤ n := by omega
          exact_mod_cast Nat.add_le_add_right this 1
        have h2 : ((p.2 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : p.2 ≤ n := by omega
          exact_mod_cast Nat.add_le_add_right this 1
        have e1 : ‖a p.1‖ ≤ C * ((n : ℝ) + 1) ^ A :=
          (hC p.1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 A) C0)
        have e2 : ‖b p.2‖ ≤ C' * ((n : ℝ) + 1) ^ A' :=
          (hC' p.2).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 A') C0')
        calc ‖a p.1‖ * ‖b p.2‖ ≤ (C * ((n : ℝ) + 1) ^ A) * (C' * ((n : ℝ) + 1) ^ A') :=
              mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
          _ = C * C' * ((n : ℝ) + 1) ^ (A + A') := by rw [pow_add]; ring
    _ = (n + 1 : ℕ) * (C * C' * ((n : ℝ) + 1) ^ (A + A')) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    _ = C * C' * ((n : ℝ) + 1) ^ (A + A' + 1) := by push_cast; ring

theorem qs_mul (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) :
    qs (mul a b) = fun τ => qs a τ * qs b τ := by
  funext τ
  have sa := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 τ
  have sb := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).1 τ
  unfold qs
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm sa sb]
  congr 1
  funext n
  unfold mul
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have e : cexp (2 * π * Complex.I * (n : ℂ) * τ) =
      cexp (2 * π * Complex.I * (p.1 : ℂ) * τ) * cexp (2 * π * Complex.I * (p.2 : ℂ) * τ) := by
    rw [← Complex.exp_add, ← hp]
    congr 1
    push_cast
    ring
  rw [e]
  ring

theorem mul_main : (∀ a b : ℕ → ℂ, PolyB a → PolyB b → PolyB (mul a b) ∧ qs (mul a b) = fun τ => qs a τ * qs b τ) ∧ ∀ (k k' L : ℕ) (χ χ' : ℤ → ℂ) (a b : ℕ → ℂ), MF k L χ a → MF k' L χ' b → MF (k + k') L (fun d => χ d * χ' d) (mul a b) := by
  refine ⟨fun a b ha hb => ⟨polyB_mul a b ha hb, qs_mul a b ha hb⟩, ?_⟩
  intro k k' L χ χ' a b ha hb
  refine ⟨polyB_mul a b ha.1 hb.1, ?_⟩
  intro γ hγ τ
  rw [qs_mul a b ha.1 hb.1]
  simp only
  rw [ha.2 γ hγ τ, hb.2 γ hγ τ, pow_add]
  ring

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eq_zero_of_mf_ch_sum_eq_zero : ∀ (k L N : ℕ) (a : DirichletCharacter ℂ N → ℕ → ℂ), 0 < L → N ∣ L → (∀ ε, MF k L (ch ε) (a ε)) → (∑ ε, a ε) = 0 → ∀ ε, a ε = 0 := by
  first | exact @GlobalTheory.EisM.Indep.forms_of_characters_independent | exact GlobalTheory.EisM.Indep.forms_of_characters_independent | (intros; apply GlobalTheory.EisM.Indep.forms_of_characters_independent <;> assumption)
end
