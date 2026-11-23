module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle670
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Mathlib.Algebra.Module.ZLattice.Summable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem norm_qPow_eq_exp {F : Type} [Field F] [NumberField F] (ξ : F) (w : Emb F → ℂ) :
    ‖qPow ξ w‖ = Real.exp (-(2 * Real.pi * ∑ i : Emb F, i ξ * (w i).im)) := by
  unfold qPow
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.im_sum]

theorem norm_eTr_eq_one {F : Type} [Field F] [NumberField F] (y : F) : ‖eTr y‖ = 1 := by
  unfold eTr
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem exists_summable_bound_terms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ), IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → ∃ M : F → ℝ, Summable M ∧ ∀ (ξ : F) (z : Emb F → ℂ), (∀ i, 1 / 2 ≤ ‖1 + z i * c‖ ∧ τ.im / 2 ≤ (τ + t * z i / (1 + z i * c)).im) → ‖a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))‖ ≤ M ξ := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t hc hτ
  obtain ⟨-, -, hpos, hsum⟩ := hc
  set w₀ : Emb F → ℂ := fun _ ↦ ((τ.im / 2 : ℝ) : ℂ) * Complex.I with hw₀
  have him : ∀ i, (w₀ i).im = τ.im / 2 := fun i ↦ by simp [hw₀]
  have hw : w₀ ∈ upperHalf F := fun i ↦ by rw [him i]; positivity
  have hs : Summable fun ξ : F ↦ ‖a ξ * qPow ξ w₀‖ := summable_norm_iff.mpr (hsum w₀ hw).summable
  refine ⟨fun ξ ↦ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) * ‖a ξ * qPow ξ w₀‖, hs.mul_left _, ?_⟩
  intro ξ z hz
  by_cases ha : a ξ = 0
  · simp [ha]
  have hnn : ∀ i : Emb F, 0 ≤ i ξ := fun i ↦ by
    by_cases h0 : ξ = 0
    · simp [h0]
    · exact ((hpos ξ h0 ha).2 i).le
  set w : Emb F → ℂ := fun i ↦ τ + t * z i / (1 + z i * c) with hwdef
  have key : Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) *
      ∏ i : Emb F, Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)) = qPow ξ w := by
    rw [← Complex.exp_sum, ← Complex.exp_add, ← GlobalTheory.HilbFam.sum_realEmb_eq_trace F ξ]
    unfold qPow
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hwdef]
    ring
  have hq : ‖qPow ξ w‖ ≤ ‖qPow ξ w₀‖ := by
    rw [norm_qPow_eq_exp, norm_qPow_eq_exp]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [him i]
    exact mul_le_mul_of_nonneg_left (hz i).2 (hnn i)
  have hp : ‖∏ i : Emb F, (1 + z i * c)⁻¹ ^ k‖ ≤ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) := by
    rw [norm_prod, ← Finset.card_univ]
    have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun i : Emb F ↦ ‖(1 + z i * c)⁻¹ ^ k‖)
      (g := fun _ ↦ (2 : ℝ) ^ k) (fun i _ ↦ norm_nonneg _) (fun i _ ↦ by
        rw [norm_pow, norm_inv]
        apply pow_le_pow_left₀ (by positivity)
        have := (hz i).1
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith)
    rwa [Finset.prod_const] at h
  have e : a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c))) =
      (∏ i : Emb F, (1 + z i * c)⁻¹ ^ k) * (eTr (ξ * x) * (a ξ * qPow ξ w)) := by
    rw [← key, Finset.prod_mul_distrib]
    ring
  rw [e, norm_mul, norm_mul, norm_eTr_eq_one, one_mul, norm_mul]
  show _ ≤ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) * ‖a ξ * qPow ξ w₀‖
  rw [norm_mul (a ξ)]
  gcongr

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem exists_unit_transfQuot_out_eq_smul {F : Type} [Field F] [NumberField F]
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (q : Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F))) :
    ∃ ε : (𝓞 F)ˣ, (_root_.GlobalTheory.HilbFam.transfQuot T q).out = ε • T q.out := by
  have h : _root_.GlobalTheory.HilbFam.transfQuot T q = Quotient.mk _ (T q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [h]
  obtain ⟨ε, hε⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
    (Quotient.mk_out (s := MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) (T q.out)))
  exact ⟨ε, hε.symm⟩

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem gTerm_eq_of_linear_change {F : Type} [Field F] [NumberField F]
    {k : ℕ} (σ : ℂ) {b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))
    (hc : ∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i =
      lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) (x : Fin 2 → F) :
    _root_.GlobalTheory.HilbFam.gTerm k σ b a x =
      ((∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ)) *
        _root_.GlobalTheory.HilbFam.gTerm k σ b' a' (T x) := by
  unfold _root_.GlobalTheory.HilbFam.gTerm
  simp only [hc, Finset.prod_mul_distrib, norm_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _), mul_inv, mul_pow]
  ring

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem isGVal_of_linear_change {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] {k : ℕ} (hk : Even k) {L L' : _root_.GlobalTheory.HilbFam.Lat F}
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) {b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (hL : ∀ x, x ∈ L ↔ T x ∈ L') (hlam : ∀ i, lam i ≠ 0)
    (hc : ∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i =
      lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) {G : ℂ}
    (hG : _root_.GlobalTheory.HilbFam.IsGVal k L' b' a' G) :
    _root_.GlobalTheory.HilbFam.IsGVal k L b a ((∏ i, lam i)⁻¹ ^ k * G) := by
  have hmem : ∀ q, q ∈ _root_.GlobalTheory.HilbFam.cls L ↔
      _root_.GlobalTheory.HilbFam.transfQuot T q ∈ _root_.GlobalTheory.HilbFam.cls L' := by
    intro q
    obtain ⟨ε, hε⟩ := exists_unit_transfQuot_out_eq_smul T q
    simp only [_root_.GlobalTheory.HilbFam.cls, Set.mem_setOf_eq, hε]
    have hz : ε • T q.out ≠ 0 ↔ q.out ≠ 0 := by
      constructor
      · intro h h0
        exact h (by rw [h0, map_zero, smul_zero])
      · intro h h0
        apply h
        apply T.injective
        rw [map_zero]
        simpa using congrArg (fun y => ε⁻¹ • y) h0
    rw [Submodule.smul_mem_iff', hz, ← hL]
  let e : _root_.GlobalTheory.HilbFam.cls L ≃ _root_.GlobalTheory.HilbFam.cls L' :=
    (_root_.GlobalTheory.HilbFam.transfQuot T).subtypeEquiv hmem
  have hterm : ∀ (σ : ℂ) (q : _root_.GlobalTheory.HilbFam.cls L),
      _root_.GlobalTheory.HilbFam.gTerm k σ b' a' (e q).1.out =
        _root_.GlobalTheory.HilbFam.gTerm k σ b' a' (T q.1.out) := by
    intro σ q
    obtain ⟨ε, hε⟩ := exists_unit_transfQuot_out_eq_smul T q
    simp only [e, Equiv.subtypeEquiv_apply]
    rw [hε, _root_.GlobalTheory.HilbFam.gTerm_unit_smul F k σ b' a' ε _ hk]
  have hsum : ∀ (σ G' : ℂ),
      HasSum (fun q : _root_.GlobalTheory.HilbFam.cls L' ↦
        _root_.GlobalTheory.HilbFam.gTerm k σ b' a' q.1.out) G' →
      HasSum (fun q : _root_.GlobalTheory.HilbFam.cls L ↦
        _root_.GlobalTheory.HilbFam.gTerm k σ b a q.1.out)
        ((∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ) * G') := by
    intro σ G' h
    have h' := (e.hasSum_iff.mpr h).mul_left ((∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ))
    have hfun : (fun q : _root_.GlobalTheory.HilbFam.cls L ↦
        _root_.GlobalTheory.HilbFam.gTerm k σ b a q.1.out) = fun q ↦
        (∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ) *
          ((fun q : _root_.GlobalTheory.HilbFam.cls L' ↦
            _root_.GlobalTheory.HilbFam.gTerm k σ b' a' q.1.out) ∘ e) q := by
      funext q
      simp only [Function.comp_apply, hterm]
      exact gTerm_eq_of_linear_change σ T hc _
    rw [hfun]
    exact h'
  obtain ⟨h₁, h₂⟩ := hG
  refine ⟨fun hk2 => ?_, fun hk2 => ?_⟩
  · simpa using hsum 0 G (h₁ hk2)
  · subst hk2
    obtain ⟨H, hH, hs, rfl⟩ := h₂ rfl
    have hne : ((‖∏ i, lam i‖ : ℝ) : ℂ) ≠ 0 := by
      simp [Finset.prod_ne_zero_iff, hlam]
    refine ⟨fun σ => (∏ i, lam i)⁻¹ ^ 2 * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ) * H σ, ?_,
      fun σ hσ => hsum σ _ (hs σ hσ), by simp⟩
    exact (((differentiable_const _).mul
      ((differentiable_id.const_mul (-2 : ℂ)).const_cpow (Or.inl hne))).differentiableOn).mul hH


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.gval_linear_change : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L L' : _root_.GlobalTheory.HilbFam.Lat F) (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), Even k → (∀ x, x ∈ L ↔ T x ∈ L') → (∀ i, lam i ≠ 0) → (∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i = lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) → _root_.GlobalTheory.HilbFam.gval k L b a = (∏ i, lam i)⁻¹ ^ k * _root_.GlobalTheory.HilbFam.gval k L' b' a' := by
  intro F _ _ _ k L L' T b a b' a' lam hk hL hlam hc
  by_cases h : ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L' b' a' G
  · obtain ⟨G, hG⟩ := h
    rw [_root_.GlobalTheory.HilbFam.gval_eq_of_isGVal F k L' b' a' G hG,
      _root_.GlobalTheory.HilbFam.gval_eq_of_isGVal F k L b a _
        (isGVal_of_linear_change hk T hL hlam hc hG)]
  · have h' : ¬ ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L b a G := by
      rintro ⟨G, hG⟩
      refine h ⟨_, isGVal_of_linear_change hk T.symm
        (lam := fun i => (lam i)⁻¹) ?_ (fun i => inv_ne_zero (hlam i)) ?_ hG⟩
      · intro x
        rw [hL (T.symm x), T.apply_symm_apply]
      · intro x i
        rw [hc (T.symm x) i, T.apply_symm_apply, inv_mul_cancel_left₀ (hlam i)]
    rw [_root_.GlobalTheory.HilbFam.gval, dite_eq_right h', _root_.GlobalTheory.HilbFam.gval, dite_eq_right h,
      mul_zero]

end GlobalTheory.HilbFam
end

section

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.SchwartzMajorant

variable (F : Type) [Field F] [NumberField F]

theorem pureA_add_algebraMap {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (ξ : κ → F) (x : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j) =
      f ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1) *
      g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j => (x j).2) := by
  unfold GlobalTheory.WeilM.pureA
  congr 2
  funext j
  simp only [Pi.add_apply]
  rw [show (algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j).1 = (algebraMap F (AdeleRing (𝓞 F) F) (ξ j)).1 + (x j).1 from rfl,
    map_add, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem norm_le_of_decay {V : Type} [NormedAddCommGroup V] {φ : V → ℂ} {k : ℕ} {C0 Ck : ℝ}
    (h0 : ∀ v, ‖φ v‖ ≤ C0) (hk : ∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) (w a : V) :
    ‖φ (w + a)‖ * (1 + ‖w‖) ^ k ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k := by
  set u := w + a with hu
  have hCk : 0 ≤ Ck := le_trans (by positivity) (hk 0)
  have hC0 : 0 ≤ C0 := le_trans (norm_nonneg _) (h0 0)
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have h1 : ‖φ u‖ * (1 + ‖u‖) ^ k ≤ 2 ^ k * (C0 + Ck) := by
    rcases le_total ‖u‖ 1 with hu1 | hu1
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ C0 * 2 ^ k :=
            mul_le_mul (h0 u) (pow_le_pow_left₀ (by positivity) (by linarith) k) (by positivity) hC0
        _ ≤ _ := by nlinarith
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ ‖φ u‖ * (2 * ‖u‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k) (norm_nonneg _)
        _ = 2 ^ k * (‖u‖ ^ k * ‖φ u‖) := by rw [mul_pow]; ring
        _ ≤ 2 ^ k * Ck := mul_le_mul_of_nonneg_left (hk u) h2k.le
        _ ≤ _ := by nlinarith
  have h2 : (1 + ‖w‖) ^ k ≤ (1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : ‖w‖ ≤ ‖u‖ + ‖a‖ := by
      calc ‖w‖ = ‖u - a‖ := by rw [hu, add_sub_cancel_right]
        _ ≤ ‖u‖ + ‖a‖ := norm_sub_le _ _
    nlinarith [norm_nonneg u, norm_nonneg a]
  calc ‖φ u‖ * (1 + ‖w‖) ^ k ≤ ‖φ u‖ * ((1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = (‖φ u‖ * (1 + ‖u‖) ^ k) * (1 + ‖a‖) ^ k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

theorem summable_one_add_norm_pow_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)

theorem exists_majorant_pureA {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (x : κ → AdeleRing (𝓞 F) F) :
    ∃ k : ℕ, ∃ M : (κ → F) → ℝ, Summable M ∧ ∀ (C0 Ck : ℝ) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
      (∀ v, ‖φ v‖ ≤ C0) → (∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) → ∀ ξ : κ → F,
        ‖GlobalTheory.WeilM.pureA F φ g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ (C0 + Ck) * M ξ := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  let xf : κ → FiniteAdeleRing (𝓞 F) F := fun j => (x j).2
  let a : κ → mixedEmbedding.mixedSpace F := fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1
  have hK : IsCompact ((fun y => y - xf) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  let v : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ j => mixedEmbedding F (ξ j)
  let S : Set (κ → F) := {ξ | v ξ ∈ GlobalTheory.WeilM.denomLattice F κ N}
  let k := Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1
  refine ⟨k, S.indicator fun ξ => 2 ^ k * (1 + ‖a‖) ^ k * B * ((1 + ‖v ξ‖) ^ k)⁻¹, ?_, ?_⟩
  · rw [← summable_subtype_iff_indicator]
    let j : S → GlobalTheory.WeilM.denomLattice F κ N := fun ξ => ⟨v ξ, ξ.2⟩
    have hj : Function.Injective j := fun p q h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    exact ((summable_one_add_norm_pow_inv (GlobalTheory.WeilM.denomLattice F κ N)).comp_injective hj).mul_left _
  · intro C0 Ck φ h0 hk ξ
    rw [pureA_add_algebraMap, norm_mul]
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]
      have hd := norm_le_of_decay h0 hk (v ξ) a
      have hpos : 0 < (1 + ‖v ξ‖) ^ k := by positivity
      have h1 : ‖φ (v ξ + a)‖ ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hd
      calc ‖φ (v ξ + a)‖ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖
          ≤ (2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹) * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) (le_trans (norm_nonneg _) h1)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hξ, mul_zero]
      have hz : g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf) = 0 := by
        by_contra h0'
        apply hξ
        have hmem : (fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) ∈ (fun y => y - xf) '' tsupport g :=
          ⟨_, subset_tsupport _ h0', add_sub_cancel_right _ _⟩
        show ∀ i, (N : ℝ) • v ξ i ∈ mixedEmbedding.integerLattice F
        intro i
        obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun w => by
          rw [map_mul, map_natCast]
          exact hKN _ hmem i w
        refine ⟨y, ?_⟩
        have h2 := congrArg (mixedEmbedding F) hy
        rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
        exact h2.symm
      show _ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖ ≤ 0
      rw [hz, norm_zero, mul_zero]

theorem exists_summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {P : Type}
    [TopologicalSpace P]
    (Ψ : P → (κ → AdeleRing (𝓞 F) F) → ℂ) (p0 : P) (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : P → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ᶠ p in nhds p0, Ψ p = ∑ i, GlobalTheory.WeilM.pureA F (f p i) (g i)) →
    (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C) →
    ∀ x : κ → AdeleRing (𝓞 F) F, ∃ M : (κ → F) → ℝ, Summable M ∧
      ∀ᶠ p in nhds p0, ∀ ξ : κ → F, ‖Ψ p (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ M ξ := by
  intro F _ _ κ _ P _ Ψ p0 m g f hg hΨ hC x
  choose k M hM hbound using fun i => exists_majorant_pureA F (hg i) x
  choose C hCev using hC
  refine ⟨fun ξ => ∑ i, (C 0 + C (k i)) * M i ξ, summable_sum fun i _ => (hM i).mul_left _, ?_⟩
  have hall : ∀ᶠ p in nhds p0, ∀ i, (∀ v, ‖v‖ ^ 0 * ‖f p i v‖ ≤ C 0) ∧
      (∀ v, ‖v‖ ^ k i * ‖f p i v‖ ≤ C (k i)) :=
    Filter.eventually_all.2 fun i => ((hCev 0).and (hCev (k i))).mono fun p hp => ⟨hp.1 i, hp.2 i⟩
  filter_upwards [hΨ, hall] with p hp hb ξ
  rw [hp, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbound i _ _ _ (fun v => ?_) (hb i).2 ξ)
  simpa using (hb i).1 v

end GlobalTheory.SchwartzMajorant
end
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

noncomputable def twoSidedEquiv (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
    {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν]
    (u : GL α E) (a : GL ν E) : Matrix α ν E ≃ₗ[F] Matrix α ν E where
  toFun x := (u : Matrix α α E) * x * (a : Matrix ν ν E)
  invFun x := ((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv x := by
    show ((u⁻¹ : GL α E) : Matrix α α E) * ((u : Matrix α α E) * x * (a : Matrix ν ν E)) * ((a⁻¹ : GL ν E) : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  right_inv x := by
    show (u : Matrix α α E) * (((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)) * (a : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]

theorem map_twoSided_haar : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ _ _ μ _ u a
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  have := hfd
  have := (hmat α ν).1
  let T := twoSidedEquiv F E u a

  have hdet : LinearEquiv.det T =
      (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u) ^ Fintype.card ν *
        (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a) ^
          Fintype.card α := by
    ext
    rw [LinearEquiv.coe_det, GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul F E α ν (u : Matrix α α E) (a : Matrix ν ν E)
      (T : Matrix α ν E →ₗ[F] Matrix α ν E) (fun x ↦ rfl)]
    simp
  have hT : (fun x ↦ (u : Matrix α α E) * x * (a : Matrix ν ν E)) = ⇑T := rfl
  rw [hT, GlobalTheory.T.map_linearEquiv_addHaar_localField F (Matrix α ν E) μ T, hdet, map_mul, map_pow, map_pow]

end GlobalTheory.KSp
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_defect_coboundary_of_obstructionClass_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F) (θ : ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T⁄R₀] →+ L.B T''), L.IsObs θ → L.IsOb2 α w 0 → ∃ g : ∀ (T T' : C) (_ : T ⟶ T'), L.B T', (∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))) ∧ ∀ T T' T'' a b, θ T T' T'' a b (w.1 T) = L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b := by
  first | exact @GlobalTheory.ObsCob.exists_cob | exact GlobalTheory.ObsCob.exists_cob | (intros; apply GlobalTheory.ObsCob.exists_cob <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.approximation_quotients_agree : ∀ (q : ℕ) (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] (f : B) (I J : Ideal B) (n i : ℤ) (y : Ht q (sp B) n i), IsCoprime I J → (∀ a : A₁, ∃ b : B, a - algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f}) → (∀ b : B, algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f} ↔ b ∈ I) → (∀ a : A₂, ∃ b : B, a - algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f}) → (∀ b : B, algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f} ↔ b ∈ J) → pull _ (spMap (algebraMap B A₁)) _ _ y = 0 → pull _ (spMap (algebraMap B A₂)) _ _ y = 0 → (∀ a : A₁ × A₂, ∃ b : B, a - algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f}) ∧ (∀ b : B, algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f} ↔ b ∈ I ⊓ J) ∧ pull _ (spMap (algebraMap B (A₁ × A₂))) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.ProdStep.prodStep) | (exact GlobalTheory.EtC.ProdStep.prodStep) | (intros; apply GlobalTheory.EtC.ProdStep.prodStep  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cohomology_vanishes_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ), (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  first | (exact @GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (exact GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (intros; apply GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cupProduct_assoc_of_pairing_assoc : ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M') (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) → ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w) a b c, ν.cup E h2 (μ.cup E h1 a b) c = ν'.cup E h4 a (μ'.cup E h3 b c) := by
  first | exact @GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc | exact GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc | (intros; apply GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc <;> assumption)
end
