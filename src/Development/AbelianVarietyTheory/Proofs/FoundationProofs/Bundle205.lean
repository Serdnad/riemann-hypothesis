module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle200
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle196
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IndexAtLevel
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumHeckeTAdjoint
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle197
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.FinDim

open Asymptotics Filter Topology Function

theorem bigO_qParam_pow {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (hc : ∀ n < m, (qExpansion h f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam h τ ^ m := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
    intro i hi
    have := hc i hi
    rw [qExpansion_coeff] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt ha).mp h1
  have ht := qParam_tendsto_atImInfty hh
  have h2 : (fun τ : ℍ => g (Periodic.qParam h τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp ht).isBigO_one ℂ
  have h3 := (isBigO_refl (fun τ : ℍ => Periodic.qParam h τ ^ m) atImInfty).mul h2
  simp only [mul_one] at h3
  refine h3.congr' ?_ EventuallyEq.rfl
  filter_upwards [ht.eventually hfg] with τ hτ
  rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne'] at hτ
  rw [hτ]; simp

theorem coeff_eq_zero_of_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hlt.ne_top
    rw [← hj] at hlt
    have hjm : j < m := by exact_mod_cast hlt
    obtain ⟨g, hg, hg0, hfg⟩ := ha.analyticOrderAt_eq_natCast.mp hj.symm
    have ht := qParam_tendsto_atImInfty (h := 1) one_pos
    have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty]
        fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j) := by
      have h3 := (isBigO_refl (fun τ : ℍ => (Periodic.qParam 1 τ ^ j)⁻¹) atImInfty).mul h
      refine h3.congr' ?_ ?_
      · filter_upwards [ht.eventually hfg] with τ hτ
        rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        rw [hτ, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
      · refine Eventually.of_forall fun τ => ?_
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        simp only
        rw [pow_sub₀ _ hq hjm.le, mul_comm]
    have h4 : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)) atImInfty (𝓝 0) := by
      have := ht.pow (m - j)
      rwa [zero_pow (by omega)] at this
    exact hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.comp ht) (h2.trans_tendsto h4))
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha] at h1
  intro n hn
  rw [qExpansion_coeff, h1 n hn, mul_zero]

theorem qParam_pow_bigO {h : ℝ} (hh : 0 < h) {m M : ℕ} (hm : (M : ℝ) * h ≤ m) :
    (fun τ : ℍ => Periodic.qParam h τ ^ m) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ M := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
  rw [one_mul, norm_pow, norm_pow, Periodic.norm_qParam, Periodic.norm_qParam, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul, Real.exp_le_exp]
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have key : (M : ℝ) * (τ : ℂ).im ≤ m * (τ : ℂ).im / h := by
    rw [le_div_iff₀ hh]; nlinarith
  have e1 : (m : ℝ) * (-2 * Real.pi * (τ : ℂ).im / h) = -2 * Real.pi * (m * (τ : ℂ).im / h) := by ring
  have e2 : (M : ℝ) * (-2 * Real.pi * (τ : ℂ).im / 1) = -2 * Real.pi * (M * (τ : ℂ).im) := by ring
  rw [e1, e2]
  nlinarith [Real.pi_pos]

theorem norm_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  apply GlobalTheory.EisM.modularFormNorm_isBigO_self_atImInfty <;> assumption

theorem sturm {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : ModularForm Γ k, (∀ n < m, (qExpansion h f).coeff n = 0) → f = 0 := by
  set M := (k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1
  refine ⟨⌈(M : ℝ) * h⌉₊, fun f hf => ?_⟩
  have h1 := coeff_eq_zero_of_bigO one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) M
    ((norm_bigO f).trans ((bigO_qParam_pow hh hΓ f _ hf).trans (qParam_pow_bigO hh (Nat.le_ceil _))))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

def coeffMap {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ)
    (m : ℕ) : ModularForm Γ k →ₗ[ℂ] (Fin m → ℂ) where
  toFun f n := (qExpansion h f).coeff n
  map_add' f g := by
    funext n
    simp only [Pi.add_apply]
    rw [ModularForm.coe_add, ModularForm.qExpansion_add hh hΓ f g, map_add (f := _)]
  map_smul' c f := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [ModularForm.coe_smul, ModularForm.qExpansion_smul hh hΓ c f, PowerSeries.coeff_smul, smul_eq_mul]

theorem finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne]
    (k : ℤ) :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  obtain ⟨m, hm⟩ := sturm Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k
  refine Module.Finite.of_injective (coeffMap Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k m) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  exact hm f fun n hn => congr_fun hf ⟨n, hn⟩

end GlobalTheory.HeckeFamilyMatrices.FinDim


open GlobalTheory.HeckeFamilyMatrices.FinDim in
theorem GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm :
    ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex →
      FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  intro Γ k hΓ
  have h1 := finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) k
  refine ⟨h1, ?_⟩
  haveI := h1
  exact Module.Finite.equiv (CuspForm.equivCuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) k).symm
end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.centredHarishChandraParameter_isParam_blattner : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) → IsParam (hcParam n ap am) ∧ blattner (hcParam n ap am) = wtK n ap am ∧ ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
  first | exact @GlobalTheory.HarmonicParam.hcParam_isParam_blattner | exact GlobalTheory.HarmonicParam.hcParam_isParam_blattner | (intros; apply GlobalTheory.HarmonicParam.hcParam_isParam_blattner <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fock_tensor_intertwiner_unique_and_range : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2) (M₁ : GKMod p q) (W : Submodule ℂ M₁.V) (M : GKMod n 0) (I : M₁.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (e₀ : W) (v₀ : M.V), genSub M₁.act (W : Set M₁.V) = ⊤ → KStable M₁.act W → (∀ N : Submodule ℂ M₁.V, N ≤ W → KStable M₁.act N → N = ⊥ ∨ N = W) → IrrGK M → e₀ ≠ 0 → v₀ ≠ 0 → IsGIntw F M₁ M I → (∀ io', IsKIntw F M₁ W M io' → io' (e₀ ⊗ₜ v₀) = I ((e₀ : M₁.V) ⊗ₜ v₀) → io' = I ∘ₗ TensorProduct.map W.subtype LinearMap.id) ∧ (∀ I', IsGIntw F M₁ M I' → (∀ (e : W) (v : M.V), I' ((e : M₁.V) ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v)) → I' = I) ∧ ∀ v : M.V, Set.range (fun x : M₁.V => I (x ⊗ₜ v)) = (genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) : Set (Pol p q n 0)) := by
  first | exact @GlobalTheory.FockUniq.intertwiner_unique_and_range | exact GlobalTheory.FockUniq.intertwiner_unique_and_range | (intros; apply GlobalTheory.FockUniq.intertwiner_unique_and_range <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isKilledByLowerNilradical_act_blockDiagonal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z → ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  first | exact @GlobalTheory.KilledByLowerStable.killedByLower_act | exact GlobalTheory.KilledByLowerStable.killedByLower_act | (intros; apply GlobalTheory.KilledByLowerStable.killedByLower_act <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.normSq_centredHarishChandraParameter_sub_rhoSq : ∀ (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ), normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  first | exact @GlobalTheory.normSq_hcParam_sub_rhoSq | exact GlobalTheory.normSq_hcParam_sub_rhoSq | (intros; apply GlobalTheory.normSq_hcParam_sub_rhoSq <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.casimir_scalar_on_module_generated_killedByLower : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  first | exact @GlobalTheory.CasimirLowest.casimir_on_generated | exact GlobalTheory.CasimirLowest.casimir_on_generated | (intros; apply GlobalTheory.CasimirLowest.casimir_on_generated <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LevelIndexCompare

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

section General

end General

variable (D : D7) (u : D.what₂.Word)

def incl (w : D.what₂.places.Pl) : LT.Sram D u w →ₗ[LT.Ow D w] (D.fm u).ramSub where
  toFun x := ⟨x.1, x.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def URamStable (v : (D.mem u).A.vT) : Prop :=
  ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)

theorem T_ne_zero : ((D.mem u).A.T : ℂ) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero

theorem emb_zpow_smul (n : ℤ) (x : LT.Vl D u 0) :
    (D.fm u).emb 0 ((((D.mem u).A.T : D.what₂.LL) ^ n) • x) = (((D.mem u).A.T : ℂ) ^ n) • (D.fm u).emb 0 x := by
  rw [LinearMap.map_smulₛₗ, map_zpow₀, map_natCast]

theorem exists_isScaledU_iff (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) :
    (∃ g, IsScaledU D u w v g) ↔ URamStable D u v := by
  constructor
  · rintro ⟨g, hg⟩ x hx
    refine ⟨(((D.mem u).A.T : D.what₂.LL) ^ (-(D.fm u).bTop ((D.fm u).tauOf w v))) • (g ⟨x, hx⟩ : LT.Vl D u 0),
      (D.fm u).ramSub.smul_mem _ (g ⟨x, hx⟩).2, ?_⟩
    rw [emb_zpow_smul, hg, smul_smul, ← zpow_add₀ (T_ne_zero D u), neg_add_cancel, zpow_zero, one_smul]
  · intro h
    let e : (D.fm u).ramSub →ₛₗ[D.what₂.embLL] LT.Fn D u 0 := ((D.fm u).emb 0).comp (D.fm u).ramSub.subtype
    have he : Function.Injective e := ((D.fm u).emb_inj 0).comp Subtype.val_injective
    let f : LT.Fn D u 0 →ₗ[ℂ] LT.Fn D u 0 :=
      (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • LT.Uop D u 0 v
    have hf : ∀ x, ∃ y, e y = f (e x) := by
      intro x
      obtain ⟨y, hy, hxy⟩ := h x.1 x.2
      refine ⟨⟨(((D.mem u).A.T : D.what₂.LL) ^ ((D.fm u).bTop ((D.fm u).tauOf w v))) • y,
        (D.fm u).ramSub.smul_mem _ hy⟩, ?_⟩
      exact (emb_zpow_smul D u _ y).trans (by rw [hxy]; rfl)
    exact ⟨descend e e he f hf, fun x => descend_spec e e he f hf x⟩

theorem emb_list_prod (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (l : List (D.mem u).A.vT) (hg : ∀ v ∈ l, IsScaledU D u w v (g v)) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((l.map g).prod x : LT.Vl D u 0) =
      (((D.mem u).A.T : ℂ) ^ (l.map fun v => (D.fm u).bTop ((D.fm u).tauOf w v)).sum) •
        (l.foldr (fun v f => (LT.Uop D u 0 v).comp f) LinearMap.id) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, hg v List.mem_cons_self,
      ih (fun v' hv' => hg v' (List.mem_cons_of_mem _ hv')), map_smul, smul_smul, List.map_cons, List.sum_cons,
      zpow_add₀ (T_ne_zero D u)]
    rfl

theorem emb_pow (G : Module.End D.what₂.LL (D.fm u).ramSub) (c : ℂ) (U : Module.End ℂ (LT.Fn D u 0))
    (h : ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (G x : LT.Vl D u 0) = c • U ((D.fm u).emb 0 (x : LT.Vl D u 0)))
    (n : ℕ) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((G ^ n) x : LT.Vl D u 0) = c ^ n • (U ^ n) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ' c, pow_succ' U, Module.End.mul_apply]

theorem mem_Nlam_iff (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (hg : ∀ v ∈ LT.VVT D u w, IsScaledU D u w v (g v)) (y : LT.Vl D u 0) :
    y ∈ LT.Nlam D u w ↔ ∃ x : LT.Sram D u w,
      y = ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) (incl D u w x) : (D.fm u).ramSub) := by
  have key : ∀ x : (D.fm u).ramSub,
      (D.fm u).emb 0 ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) x : (D.fm u).ramSub) =
        ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (LT.Uprod D u 0 w) ^ D.R.m) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
    intro x
    rw [emb_pow D u _ _ (LT.Uprod D u 0 w)
      (emb_list_prod D u w g _ (fun v hv => hg v (Finset.mem_toList.1 hv))), Finset.sum_map_toList,
      ← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, (D.fm u).emb_inj 0 (hxy.trans (key (incl D u w ⟨x, hx⟩)).symm)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, key _⟩

end GlobalTheory.LevelIndexCompare

end
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (c : ℂ), GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (⇑g + c • ⇑h) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g + c * GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑h ∧ GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑g ⇑f = (starRingEnd ℂ) (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g) := by
  first | exact @GlobalTheory.Hk.pet_sesq | exact GlobalTheory.Hk.pet_sesq | (intros; apply GlobalTheory.Hk.pet_sesq <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint : ∀ (N l q : ℕ) (k : ℤ) (σ σ' : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l q σ' → ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.heckeT k q σ ⇑f) (GlobalTheory.Hk.dia k σ' ⇑g) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (GlobalTheory.Hk.heckeT k q σ ⇑g) := by
  first | exact @GlobalTheory.Hk.pet_heckeT_adj | exact GlobalTheory.Hk.pet_heckeT_adj | (intros; apply GlobalTheory.Hk.pet_heckeT_adj <;> assumption)
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_valuation_almostEtale_towerFixer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω), ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ GlobalTheory.K5.IsInt (p := p) x) ∧ (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 ∧ ∀ S : Finset Ω, ∃ U : Subgroup ↥(⨅ n, Gn T n), U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix Ω U) ∧ AlmostSep v U := by
  first | exact @GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | exact GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | (intros; apply GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_injective_cuspExpansion_ringHom : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω, Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) := by
  first | exact @GlobalTheory.FN.expansion_injective_ringHom | exact GlobalTheory.FN.expansion_injective_ringHom | (intros; apply GlobalTheory.FN.expansion_injective_ringHom <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_smul (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ) (hx : admitted c x) :
    sg c x (γ • τ) = sg c (act x γ) τ :=
  GlobalTheory.T.modular_law_of_s_and_t (admitted c) (sg c) (fun x γ h => GlobalTheory.T.admissible_of_sl2_action c x γ h)
    (fun x τ h => GlobalTheory.T.smoothedSiegelUnit_modularS_smul c x τ h) (fun x τ _ => GlobalTheory.T.smoothedSiegelUnit_modularGroupT_smul c x τ) γ x τ hx

end GlobalTheory.Sieg
end
