module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle017
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossZeroOfExpTwoPiIBound
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle007
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Affine.Convex
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Pow

@[expose] public section

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SupPowNorm

open Formalism.IndefR.Arith

section Clear

variable {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type} [AddCommGroup WL] [Module Ks WL] [Module (𝓞 Ks) WL]
  [IsScalarTower (𝓞 Ks) Ks WL]

theorem exists_smul_mem_span_int {T : Set WL} {g : WL} (hg : g ∈ Submodule.span Ks T) :
    ∃ d : 𝓞 Ks, d ≠ 0 ∧ d • g ∈ Submodule.span (𝓞 Ks) T := by
  first
  | exact @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | (apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers ..)

end Clear

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

theorem exists_pow_smul_mem_MK (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1)
    {t : WL} (ht : t ∈ A.MK) : ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := by
  obtain ⟨htW, htb⟩ := ht
  have hg := hW t htW
  obtain ⟨d, hd, hdg⟩ := exists_smul_mem_span_int (hspan _ hg)
  have hdM : d • hL t ∈ A.MK := (Submodule.span_le.2 fun x hx => hT x hx) hdg
  have hb : ∀ la y, FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ ≤ 1 := by
    intro la y
    obtain ⟨h1, h2⟩ := hdM
    have := h2 la y
    have e : (⟨d • hL t, h1⟩ : A.WK) = (algebraMap (𝓞 Ks) Ks d) • ⟨hL t, hg⟩ :=
      Subtype.ext (algebraMap_smul Ks d (hL t)).symm
    rwa [e, A.nrm_smul] at this
  have hfin : {la : HeightOneSpectrum (𝓞 Ks) | la.asIdeal ∣ Ideal.span {(p : 𝓞 Ks)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hex : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∈ la.asIdeal →
      ∃ n : ℕ, FinitePlace.mk la (N : Ks) ^ n ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := by
    intro la hla
    have hNla : (N : 𝓞 Ks) ∈ la.asIdeal := by
      obtain ⟨k, rfl⟩ := hpN
      push_cast
      exact la.asIdeal.mul_mem_right _ hla
    have h1 : FinitePlace.mk la (N : Ks) < 1 := by
      rw [FinitePlace.mk_apply]
      have := (FinitePlace.norm_lt_one_iff_mem Ks la (N : 𝓞 Ks)).2 hNla
      simpa using this
    have h2 : 0 < FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := FinitePlace.pos_iff.2 (by simpa using hd)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h2 h1
    exact ⟨n, hn.le⟩
  classical
  choose! nf hnf using hex
  refine ⟨hfin.toFinset.sup nf, fun m hm => ?_⟩
  have hmW : N ^ m • hL t ∈ A.WK := by
    rw [← Nat.cast_smul_eq_nsmul Ks]
    exact A.WK.smul_mem _ hg
  refine ⟨hmW, fun la y => ?_⟩
  have e : (⟨N ^ m • hL t, hmW⟩ : A.WK) = ((N : Ks) ^ m) • ⟨hL t, hg⟩ :=
    Subtype.ext (by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl)
  rw [e, A.nrm_smul, map_pow]
  have hN1 : FinitePlace.mk la (N : Ks) ≤ 1 := by
    rw [FinitePlace.mk_apply]
    simpa using FinitePlace.norm_le_one Ks la (N : 𝓞 Ks)
  have hN0 : 0 ≤ FinitePlace.mk la (N : Ks) := by positivity
  have h0 := A.nrm_nonneg la y ⟨hL t, hg⟩
  by_cases hla : (p : 𝓞 Ks) ∈ la.asIdeal
  · have hmem : la ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hla
    have hle : nf la ≤ m := (Finset.le_sup hmem).trans hm
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩
        ≤ FinitePlace.mk la (N : Ks) ^ nf la * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hN0 hN1 hle) h0
      _ ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (hnf la hla) h0
      _ ≤ 1 := hb la y
  · have := hsup la hla t htW (htb la) y
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hN0 hN1) this h0 zero_le_one
      _ = 1 := one_mul 1

end Forms

section Span

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

theorem exists_pow_smul_mem_span (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hMK : ∀ x ∈ A.MK, x ∈ Submodule.span (𝓞 Ks) (T : Set WL))
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1) :
    ∃ n : ℕ, ∀ x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL),
      N ^ n • hL x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL) := by
  classical
  have hex : ∀ t ∈ T, ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := fun t ht =>
    exists_pow_smul_mem_MK A hL T hT hspan hW hp hpN hsup (hT t ht)
  choose! nf hnf using hex
  set n := T.sup nf
  have hks : ∀ (a : Ks) (x : WL), hL (a • x) = a • hL x := fun a x => LinearMap.map_smul_of_tower hL a x
  have h0 : ∀ f ∈ Submodule.span (𝓞 Ks) (T : Set WL), N ^ n • hL f ∈ A.MK := by
    intro f hfs
    induction hfs using Submodule.span_induction with
    | mem t ht => exact hnf t ht n (Finset.le_sup ht)
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul Ks a x, hks, algebraMap_smul, smul_comm]
      exact A.MK.smul_mem a hx
  have h1 : ∀ f ∈ A.MK, N ^ n • hL f ∈ A.MK := fun f hf => h0 f (hMK f hf)
  refine ⟨n, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem f hf => exact Submodule.subset_span (h1 f hf)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | smul b x _ hx =>
    rw [LinearMap.map_smul_of_tower, smul_comm]
    exact Submodule.smul_mem _ b hx

end Span

section Prime

variable {E : Type} [Field E] [NumberField E]

theorem exists_mem_of_list_prod_mem (P : HeightOneSpectrum (𝓞 E)) :
    ∀ l : List (𝓞 E), l.prod ∈ P.asIdeal → ∃ x ∈ l, x ∈ P.asIdeal := by
  intro l
  simpa only [Multiset.prod_coe, Multiset.mem_coe] using
    (P.isPrime.multiset_prod_mem_iff_exists_mem (l : Multiset (𝓞 E))).mp

theorem exists_prime_dvd_card (P : HeightOneSpectrum (𝓞 E)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P.asIdeal ∧ p ∣ Nat.card (𝓞 E ⧸ P.asIdeal) := by
  have e : Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  rw [← Nat.prod_primeFactorsList hN, Nat.cast_list_prod] at hmem
  obtain ⟨x, hx, hxP⟩ := exists_mem_of_list_prod_mem P _ hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hxP, e ▸ Nat.dvd_of_mem_primeFactorsList hp⟩

theorem prime_eq_of_mem (P : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpP : (p : 𝓞 E) ∈ P.asIdeal) (hqP : (q : 𝓞 E) ∈ P.asIdeal) : p = q := by
  by_contra hne
  have hco : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := ((Nat.coprime_primes hp hq).2 hne).cast
  obtain ⟨u, v, huv⟩ := hco
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpP) (P.asIdeal.mul_mem_left _ hqP)))

end Prime

end GlobalTheory.SupPowNorm
end
end

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.Mem.GaussPhase

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem differentiableAt_det (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) :
    DifferentiableAt ℝ (fun s => (M s).det) t :=
  _root_.GlobalTheory.DifferentiableDet.differentiableAt_det M t hM

theorem differentiableAt_inv_apply (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) (hne : (M t).det ≠ 0) (i j : σ) :
    DifferentiableAt ℝ (fun s => (M s)⁻¹ i j) t := by
  have hadj : DifferentiableAt ℝ (fun s => (M s).adjugate i j) t := by
    have := differentiableAt_det (fun s => (M s).updateRow j (Pi.single i 1)) t (by
      intro a b
      by_cases h : a = j
      · simp only [updateRow_apply, h, ite_true]
        exact differentiableAt_const _
      · simp only [updateRow_apply, h, ite_false]
        exact hM a b)
    simpa only [adjugate_apply] using this
  have := ((differentiableAt_det M t hM).fun_inv hne).mul hadj
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

omit [DecidableEq σ] in
theorem hasDerivAt_dot (x : σ → ℂ) {w : ℝ → σ → ℂ} {w' : σ → ℂ} {t : ℝ} (h : HasDerivAt w w' t) :
    HasDerivAt (fun s => x ⬝ᵥ w s) (x ⬝ᵥ w') t := by
  simp only [dotProduct]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pi.mp h k).const_mul _

omit [DecidableEq σ] in
theorem hasDerivAt_mulVec (S : Matrix σ σ ℂ) {w : ℝ → σ → ℂ} {w' : σ → ℂ} {t : ℝ}
    (h : HasDerivAt w w' t) : HasDerivAt (fun s => S *ᵥ w s) (S *ᵥ w') t :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_dot (S i) h

omit [DecidableEq σ] in
theorem dot_symm {S : Matrix σ σ ℂ} (hS : Sᵀ = S) (a b : σ → ℂ) :
    (S *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (S *ᵥ b) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS]

theorem hasDerivAt_phase (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ)
    (x y : σ → ℂ) (t : ℝ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (hu : IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det) :
    (let w : ℝ → σ → ℂ := fun s => (1 - ((s : ℂ) ^ 2) • (T * S))⁻¹ *ᵥ (y + (s : ℂ) • T *ᵥ x)
    let u : ℝ → σ → ℂ := fun s => x + (s : ℂ) • S *ᵥ w s
    HasDerivAt (fun s : ℝ => (s : ℂ) / 2 * (x ⬝ᵥ w s + y ⬝ᵥ u s)) (u t ⬝ᵥ w t) t) := by
  intro w u
  have hof : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  set M : ℝ → Matrix σ σ ℂ := fun s => 1 - ((s : ℂ) ^ 2) • (T * S) with hMdef
  have hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t := by
    intro i j
    simp only [hMdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (differentiableAt_const _).fun_sub ((hof.differentiableAt.fun_pow 2).mul_const _)
  have hne : (M t).det ≠ 0 := hu.ne_zero
  have hev : ∀ᶠ s in nhds t, (M s).det ≠ 0 :=
    (differentiableAt_det M t hM).continuousAt.eventually_ne hne
  have hwd : DifferentiableAt ℝ w t := by
    refine differentiableAt_pi.mpr fun i => ?_
    change DifferentiableAt ℝ (fun s => ∑ k, (M s)⁻¹ i k * (y k + (s : ℂ) * (T *ᵥ x) k)) t
    exact DifferentiableAt.fun_sum fun k _ =>
      (differentiableAt_inv_apply M t hM hne i k).fun_mul
        ((differentiableAt_const _).fun_add (hof.differentiableAt.mul_const _))
  obtain ⟨w', hw⟩ : ∃ w', HasDerivAt w w' t := ⟨_, hwd.hasDerivAt⟩
  have hU : HasDerivAt u ((t : ℂ) • S *ᵥ w' + S *ᵥ w t) t := by
    have := (hof.fun_smul (hasDerivAt_mulVec S hw)).const_add x
    simpa only [one_smul] using this
  set u' := (t : ℂ) • S *ᵥ w' + S *ᵥ w t with hu'
  have hkey : ∀ s, (M s).det ≠ 0 → w s = y + (s : ℂ) • T *ᵥ u s := by
    intro s hs
    have h1 : M s *ᵥ w s = y + (s : ℂ) • T *ᵥ x := by
      change M s *ᵥ ((M s)⁻¹ *ᵥ _) = _
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs), one_mulVec]
    simp only [hMdef, sub_mulVec, one_mulVec, smul_mulVec] at h1
    simp only [u, mulVec_add, mulVec_smul, mulVec_mulVec, smul_add, smul_smul]
    rw [← add_assoc, ← h1, pow_two, sub_add_cancel]
  have hw2 : HasDerivAt w ((t : ℂ) • T *ᵥ u' + T *ᵥ u t) t := by
    have := (hof.fun_smul (hasDerivAt_mulVec T hU)).const_add y
    simp only [one_smul] at this
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs using hkey s hs
  have hw' : w' = (t : ℂ) • T *ᵥ u' + T *ᵥ u t := hw.unique hw2
  have hx : x = u t - (t : ℂ) • S *ᵥ w t := by simp [u]
  have hy : y = w t - (t : ℂ) • T *ᵥ u t := by rw [eq_sub_iff_add_eq]; exact (hkey t hne).symm
  have hmain := (hof.div_const 2).fun_mul ((hasDerivAt_dot x hw).fun_add (hasDerivAt_dot y hU))
  refine hmain.congr_deriv ?_
  have e1 : x ⬝ᵥ w t = u t ⬝ᵥ w t - t * (w t ⬝ᵥ S *ᵥ w t) := by
    conv_lhs => rw [hx]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]
  have e2 : y ⬝ᵥ u t = u t ⬝ᵥ w t - t * (u t ⬝ᵥ T *ᵥ u t) := by
    conv_lhs => rw [hy]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul, dotProduct_comm]
  have e3 : x ⬝ᵥ w' = u t ⬝ᵥ w' - t * (w t ⬝ᵥ S *ᵥ w') := by
    conv_lhs => rw [hx]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]
  have e4 : y ⬝ᵥ u' = w t ⬝ᵥ u' - t * (u t ⬝ᵥ T *ᵥ u') := by
    conv_lhs => rw [hy]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul]
  have e5 : w t ⬝ᵥ u' = t * (w t ⬝ᵥ S *ᵥ w') + w t ⬝ᵥ S *ᵥ w t := by
    rw [hu', dotProduct_add, dotProduct_smul, smul_eq_mul]
  have e6 : u t ⬝ᵥ w' = t * (u t ⬝ᵥ T *ᵥ u') + u t ⬝ᵥ T *ᵥ u t := by
    conv_lhs => rw [hw']
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [e1, e2, e3, e4, e5, e6]
  ring

end GlobalTheory.Mem.GaussPhase
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_const_substitution_of_holomorphic_families' : ∀ (L D : Type) [Countable D] (g : ℕ) (act : D → L → L) (U : Set ℂ) (s s' : ℂ → L → Fin g → ℂ), IsOpen U → IsPreconnected U → U.Nonempty → (∀ a, DifferentiableOn ℂ (fun w => s w a) U) → (∀ a, DifferentiableOn ℂ (fun w => s' w a) U) → (∀ w ∈ U, ∃ δ, ∀ a, s' w a = s w (act δ a)) → ∃ δ, ∀ w ∈ U, ∀ a, s' w a = s w (act δ a) := by
  first | exact @GlobalTheory.exists_const_substitution_of_holomorphic_families | exact GlobalTheory.exists_const_substitution_of_holomorphic_families | (intros; apply GlobalTheory.exists_const_substitution_of_holomorphic_families <;> assumption)
end

section

open Complex

namespace GlobalTheory.ExpSeries

theorem convexOn_norm_mul_cexp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (c : ℂ) (L : V →ₗ[ℂ] ℂ) :
    ConvexOn ℝ Set.univ (fun z : V => ‖c * cexp (L z)‖) := by
  have h := (convexOn_exp.comp_linearMap
    (Complex.reLm ∘ₗ (L.restrictScalars ℝ))).smul (norm_nonneg c)
  rw [Set.preimage_univ] at h
  have e : (fun z : V => ‖c * cexp (L z)‖) = fun z : V =>
      ‖c‖ • (Real.exp ∘ ⇑(Complex.reLm ∘ₗ (L.restrictScalars ℝ))) z := by
    funext z
    simp [Complex.norm_exp]
  rw [e]
  exact h

theorem convex_and_differentiableOn_tsum_cexp :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (J : Type)
      (c : J → ℂ) (L : J → V →ₗ[ℂ] ℂ),
      Convex ℝ {z : V | Summable fun j => c j * cexp (L j z)} ∧
      DifferentiableOn ℂ (fun z : V => ∑' j, c j * cexp (L j z))
        (interior {z : V | Summable fun j => c j * cexp (L j z)}) := by
  intro V _ _ _ J c L
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [← summable_norm_iff] at hx hy ⊢
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      ((hx.mul_left a).add (hy.mul_left b))
    exact (convexOn_norm_mul_cexp (c j) (L j)).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  · intro z0 hz0
    have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
    obtain ⟨b, hb0, hb⟩ := exists_mem_interior_convexHull_affineBasis
      (mem_interior_iff_mem_nhds.1 hz0)
    have hsum : Summable fun j => ∑ i, ‖c j * cexp (L j (b i))‖ := by
      refine summable_sum fun i _ => ?_
      have : b i ∈ {z : V | Summable fun j => c j * cexp (L j z)} :=
        hb (subset_convexHull ℝ _ ⟨i, rfl⟩)
      exact summable_norm_iff.2 this
    have hd := (GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts
      (F := fun j z => c j * cexp (L j z)) (U := interior (convexHull ℝ (Set.range b)))
      isOpen_interior
      (fun j => ((((L j).toContinuousLinearMap.differentiable).cexp).const_mul
        (c j)).differentiableOn)
      (fun K hK _ => ⟨_, hsum, fun j z hz => by
        obtain ⟨y, ⟨i, rfl⟩, hy⟩ := (convexOn_norm_mul_cexp (c j) (L j)).exists_ge_of_mem_convexHull
          (Set.subset_univ _) (interior_subset (hK hz))
        exact hy.trans (Finset.single_le_sum (f := fun i => ‖c j * cexp (L j (b i))‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ i))⟩)).1
    exact (hd.differentiableAt (isOpen_interior.mem_nhds hb0)).differentiableWithinAt

end GlobalTheory.ExpSeries
end

section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.locally_bounded_off_coordinate_hyperplanes : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  first | exact @GlobalTheory.HyperplaneLocBound.locally_bounded | exact GlobalTheory.HyperplaneLocBound.locally_bounded | (intros; apply GlobalTheory.HyperplaneLocBound.locally_bounded <;> assumption)
end

section


theorem _root_.GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos : ∀ (c : ℝ) (f : ℂ → ℂ) (m : ℤ), DifferentiableOn ℂ f {s : ℂ | s.re < c} → (∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m) → (∀ s : ℂ, s.re < c → 0 < (f s).im) → 0 ≤ m := by
  first | exact @GlobalTheory.periodic_strip_shift_nonneg | exact GlobalTheory.periodic_strip_shift_nonneg | (intros; apply GlobalTheory.periodic_strip_shift_nonneg <;> assumption)
end

section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.extension_across_zero_of_exp_two_pi_I_bound : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t := by
  first | exact @GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound | exact GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound | (intros; apply GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.germSections_halfPlane_global_section : ∀ (Y : Type) (G : ℂ → (ℂ → Y) → Prop) (T : ℝ), (∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s') → (∀ w : ℂ, T < w.im → ∃ s, ∀ᶠ z in 𝓝 w, G z s) → (∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) → (∀ z ∈ U, G z s) → (∀ z ∈ U, G z s') → ∀ w ∈ U, s w = s' w → Set.EqOn s s' U) → (∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) → (∀ z ∈ U, G z s) → ∀ w ∈ U, G w s' → ∃ s'' : ℂ → Y, (∀ z ∈ U, G z s'') ∧ s'' w = s' w) → ∃ s : ℂ → Y, ∀ w : ℂ, T < w.im → G w s := by
  first | exact @GlobalTheory.germSections_halfPlane_global | exact GlobalTheory.germSections_halfPlane_global | (intros; apply GlobalTheory.germSections_halfPlane_global <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.finiteDimensional_of_uniformly_almost_invariant_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)), (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K), (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) → FiniteDimensional ℂ E := by
  first | exact @GlobalTheory.finiteDimensional_of_uniformly_almost_invariant | exact GlobalTheory.finiteDimensional_of_uniformly_almost_invariant | (intros; apply GlobalTheory.finiteDimensional_of_uniformly_almost_invariant <;> assumption)
end

section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.cauchy_slice_eq_removable_extension : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by
  first | exact @GlobalTheory.cauchy_slice_removable_extension | exact GlobalTheory.cauchy_slice_removable_extension | (intros; apply GlobalTheory.cauchy_slice_removable_extension <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_finite_extension_capitulation_complex : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (ι : Type) [Finite ι] (I : ι → Submodule (𝓞 E) E), (∀ τ, (I τ).FG) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ x, φ x ∈ M) ∧ ∀ τ, ∃ s : M, Submodule.span (𝓞 M) {y : M | ∃ x ∈ I τ, (y : ℂ) = φ x} = Submodule.span (𝓞 M) {s} := by
  first | exact @GlobalTheory.exists_finite_extension_capitulation | exact GlobalTheory.exists_finite_extension_capitulation | (intros; apply GlobalTheory.exists_finite_extension_capitulation <;> assumption)
end
