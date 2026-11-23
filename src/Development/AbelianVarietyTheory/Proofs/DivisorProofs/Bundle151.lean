module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open NumberField IsDedekindDomain TensorProduct

noncomputable section

namespace GlobalTheory.NormLevelCompare

section Adeles

open Rat.HeightOneSpectrum

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem padic_cast {p q : Nat.Primes} (h : p = q) :
    ∃ e : ℚ_[p] ≃ₐ[ℚ] ℚ_[q], ∀ x, e x ∈ PadicInt.subring q ↔ x ∈ PadicInt.subring p := by
  subst h
  exact ⟨AlgEquiv.refl, fun _ => Iff.rfl⟩

theorem padicEquiv_mem {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
    [IsDedekindDomain R] [IsFractionRing R ℚ] (v : HeightOneSpectrum R)
    (x : v.adicCompletion ℚ) :
    adicCompletion.padicEquiv v x ∈ PadicInt.subring (primesEquiv v) ↔
      x ∈ v.adicCompletionIntegers ℚ := by
  refine ⟨fun hx => ?_, fun hx => (adicCompletion.padicEquiv_bijOn v).mapsTo hx⟩
  obtain ⟨y, hy, hxy⟩ := (adicCompletion.padicEquiv_bijOn v).surjOn hx
  obtain rfl : y = x := (adicCompletion.padicEquiv v).injective hxy
  exact hy

def primeCorr : HeightOneSpectrum ℤ ≃ HeightOneSpectrum (𝓞 ℚ) :=
  (primesEquiv (R := ℤ)).trans (primesEquiv (R := 𝓞 ℚ)).symm

theorem exists_local (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃ₐ[ℚ] w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have h : primesEquiv (primeCorr w) = primesEquiv w := by simp [primeCorr]
  obtain ⟨c, hc⟩ := padic_cast h
  refine ⟨((adicCompletion.padicEquiv (primeCorr w)).toAlgEquiv.trans c).trans
    (adicCompletion.padicEquiv w).symm.toAlgEquiv, fun x => ?_⟩
  rw [← padicEquiv_mem w, ← padicEquiv_mem (primeCorr w), ← hc]
  change adicCompletion.padicEquiv w ((adicCompletion.padicEquiv w).symm _) ∈ _ ↔ _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  rfl

theorem exists_adele_equiv_of_local {R R' K : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing R'] [IsDedekindDomain R'] [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra R' K] [IsFractionRing R' K] (σ : HeightOneSpectrum R' ≃ HeightOneSpectrum R)
    (e : ∀ w, (σ w).adicCompletion K ≃ₐ[K] w.adicCompletion K)
    (he : ∀ w x, e w x ∈ w.adicCompletionIntegers K ↔ x ∈ (σ w).adicCompletionIntegers K) :
    ∃ e : FiniteAdeleRing R K ≃ₐ[K] FiniteAdeleRing R' K,
      ∀ a, (∀ w, e a w ∈ w.adicCompletionIntegers K) ↔
        ∀ v, a v ∈ v.adicCompletionIntegers K := by
  let φ : FiniteAdeleRing R K →ₐ[K] FiniteAdeleRing R' K :=
    { toFun := fun a => ⟨fun w => e w (a (σ w)), by
        have h1 := σ.injective.tendsto_cofinite.eventually a.2
        exact h1.mono fun w hw => (he w _).2 hw⟩
      map_one' := FiniteAdeleRing.ext _ fun w => map_one (e w)
      map_mul' := fun a b => FiniteAdeleRing.ext _ fun w => map_mul (e w) _ _
      map_zero' := FiniteAdeleRing.ext _ fun w => map_zero (e w)
      map_add' := fun a b => FiniteAdeleRing.ext _ fun w => map_add (e w) _ _
      commutes' := fun r => FiniteAdeleRing.ext _ fun w => (e w).commutes r }
  have hφ : ∀ a w, φ a w = e w (a (σ w)) := fun _ _ => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    refine FiniteAdeleRing.ext _ fun v => ?_
    obtain ⟨w, rfl⟩ := σ.surjective v
    apply (e w).injective
    rw [← hφ, ← hφ, hab]
  have hsurj : Function.Surjective φ := by
    intro b
    let f : ∀ v : HeightOneSpectrum R, v.adicCompletion K :=
      Equiv.piCongrLeft (fun v : HeightOneSpectrum R => v.adicCompletion K) σ
        (fun w => (e w).symm (b w))
    have hf : ∀ w, f (σ w) = (e w).symm (b w) := fun w =>
      Equiv.piCongrLeft_apply_apply _ _ _ _
    refine ⟨⟨f, ?_⟩, FiniteAdeleRing.ext _ fun w => ?_⟩
    · have h1 := σ.symm.injective.tendsto_cofinite.eventually b.2
      refine h1.mono fun v hv => ?_
      obtain ⟨w, rfl⟩ := σ.surjective v
      rw [Equiv.symm_apply_apply] at hv
      change f (σ w) ∈ (σ w).adicCompletionIntegers K
      rw [hf, ← he, AlgEquiv.apply_symm_apply]
      exact hv
    · change e w (f (σ w)) = _
      rw [hf, AlgEquiv.apply_symm_apply]
  refine ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun a => ?_⟩
  change (∀ w, φ a w ∈ w.adicCompletionIntegers K) ↔
    ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K
  rw [σ.surjective.forall]
  exact forall_congr' fun w => he w _

theorem exists_adele_equiv :
    ∃ e : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af ≃ₐ[ℚ] IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af,
      ∀ a, e a ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHat ↔ a ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat := by
  choose e he using exists_local
  exact exists_adele_equiv_of_local primeCorr e he

end Adeles

section Transport

variable {A A' : Type} [CommRing A] [Algebra ℚ A] [CommRing A'] [Algebra ℚ A'] (e : A ≃ₐ[ℚ] A')

variable {V V' : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']

end Transport

section Adelic

variable (e : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af ≃ₐ[ℚ] IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af)
  (he : ∀ a, e a ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHat ↔ a ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat)



section Ideles

variable {K : Type} [Field K] [NumberField K]




end Ideles

section Groups

variable {E : Type} [Field E] [NumberField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]


include he



variable [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

end Groups

end Adelic

section Hypotheses

variable {K : Type} [Field K] [NumberField K] {d : ℕ} {δ : K}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E]



variable {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]
  [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]





end Hypotheses

end GlobalTheory.NormLevelCompare
end
end

section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

def NzElt (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Type :=
  {b : F // b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ b ≠ 0}

def unitRel (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Setoid (NzElt 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1 = ((ε : 𝓞 F) : F) * p.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun {p q} ⟨ε, h⟩ => ⟨ε⁻¹, by rw [h, ← mul_assoc, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h⟩ ⟨ε', h'⟩ => ⟨ε' * ε, by rw [h', h, ← mul_assoc]; simp⟩ }

def NzCls (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Type := Quotient (unitRel 𝔟)

def rep {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : F := (Quotient.out β : NzElt 𝔟).1

theorem rep_mem {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : rep β ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) :=
  (Quotient.out β : NzElt 𝔟).2.1

theorem rep_ne_zero {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : rep β ≠ 0 :=
  (Quotient.out β : NzElt 𝔟).2.2

def posCone (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F) : Type :=
  {ν : F // ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)}

end GlobalTheory.SlopeTestRemainingChoices.EisFibre
end
end

section

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory

theorem norm_sq_mul_exp_neg_trace_le : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : ℝ), 0 < δ →
    ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) →
      |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤
        C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) := by
  intro F _ _ _ δ hδ
  set n := 2 * Fintype.card (Emb F) with hn
  refine ⟨(n.factorial : ℝ) * (2 / δ) ^ n, fun x hx => ?_⟩
  set T := ∑ τ : Emb F, τ x with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun τ _ => (hx τ).le
  have hnorm : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ τ : Emb F, τ x := by
    have h := prod_emb x
    have h' : ((∏ τ : Emb F, τ x : ℝ) : ℂ) = (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) := by
      rw [ofReal_prod, h]; simp
    exact_mod_cast h'.symm
  have hprod : |((Algebra.norm ℚ x : ℚ) : ℝ)| ≤ T ^ Fintype.card (Emb F) := by
    rw [hnorm, abs_of_nonneg (Finset.prod_nonneg fun τ _ => (hx τ).le)]
    calc ∏ τ : Emb F, τ x ≤ ∏ _τ : Emb F, T :=
          Finset.prod_le_prod₀ (fun τ _ => (hx τ).le) (fun τ _ =>
            Finset.single_le_sum (f := fun σ : Emb F => σ x) (fun σ _ => (hx σ).le) (Finset.mem_univ τ))
      _ = T ^ Fintype.card (Emb F) := by rw [Finset.prod_const, Finset.card_univ]
  have hsq : |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ 2 ≤ T ^ n := by
    calc _ ≤ (T ^ Fintype.card (Emb F)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hprod 2
      _ = T ^ n := by rw [← pow_mul, mul_comm]
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hexp : (δ * T / 2) ^ n / n.factorial ≤ Real.exp (δ * T / 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have e2 : (δ * T / 2) ^ n ≤ Real.exp (δ * T / 2) * n.factorial := (div_le_iff₀ hf).1 hexp
  have e1 : T ^ n = (2 / δ) ^ n * (δ * T / 2) ^ n := by
    rw [← mul_pow]; congr 1; field_simp
  have hTn : T ^ n ≤ (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (δ * T / 2) := by
    rw [e1]
    calc _ ≤ (2 / δ) ^ n * (Real.exp (δ * T / 2) * n.factorial) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  calc |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ 2 * Real.exp (-δ * T)
        ≤ T ^ n * Real.exp (-δ * T) := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ ≤ (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (δ * T / 2) * Real.exp (-δ * T) :=
          mul_le_mul_of_nonneg_right hTn (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (-(δ / 2) * T) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end GlobalTheory
end

section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.Div.LipschitzCone

theorem sign_cone_iff (x y w : ℝ) (hx : x ≠ 0) (hw : 0 < w) :
    0 < (SignType.sign (x * w) : ℝ) * y ↔ 0 < y * x := by
  rw [sign_mul, sign_pos hw, mul_one]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [sign_neg h]
    simp only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul, Left.neg_pos_iff]
    constructor
    · intro hy; exact mul_pos_of_neg_of_neg hy h
    · intro hyx
      by_contra hc
      push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos hc h.le
      linarith
  · rw [sign_pos h]
    simp only [SignType.coe_one, one_mul]
    constructor
    · intro hy; exact mul_pos hy h
    · intro hyx; exact pos_of_mul_pos_left hyx h.le

theorem cone_iff : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ ν : F,
      ν ∈ GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) (fun τ => ((τ b : ℝ) : ℂ) * z τ) ↔
        (ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)) := by
  intro F _ _ 𝔞 b hb z hz ν
  have ha : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔞.ne_zero
  have hM : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 ≠ 0 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ ha
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone
  simp only [Set.mem_setOf_eq]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff hM, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.dual_dual]
  refine and_congr Iff.rfl (forall_congr' fun τ => ?_)
  rw [Complex.im_ofReal_mul, map_mul τ ν b]
  exact sign_cone_iff _ _ _ ((map_ne_zero τ).2 hb) (hz τ)

end GlobalTheory.Div.LipschitzCone
end

section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.LipEisConst

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

theorem absNorm_latM {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) :
    ((FractionalIdeal.absNorm (latM 𝔞) : ℚ) : ℝ) = (dF F * nrm 𝔞)⁻¹ := by
  rw [latM, map_mul, map_inv₀, Units.val_inv_eq_inv_val, map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    absNorm_differentIdeal F (𝓞 F), dF, nrm]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, mul_inv]

theorem lip_const_eis : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 1 ≤ k →
    ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lipConst k (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℂ) ^ (k - 1) = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) := by
  intro F _ _ 𝔞 k hk
  have hd : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hn : 0 < nrm 𝔞 := by
    have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
    have h3 := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) h2.symm
    unfold nrm; exact_mod_cast h3
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F) ≠ 0 := by
    apply pow_ne_zero
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  have hcov : covol (latM 𝔞) = (Real.sqrt (dF F) * nrm 𝔞)⁻¹ := by
    rw [covol, absNorm_latM, ← dF]
    have hs : Real.sqrt (dF F) * Real.sqrt (dF F) = dF F := Real.mul_self_sqrt hd.le
    have hs0 : 0 < Real.sqrt (dF F) := Real.sqrt_pos.2 hd
    field_simp
    rw [Real.sq_sqrt hd.le]

  set fac : ℝ := ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F with hfac
  have hfac0 : 0 < fac := by positivity
  have hreal : nrm 𝔞 ^ (k - 1) / (fac * covol (latM 𝔞)) = omegaFactor 𝔞 ^ k / cK F k := by
    rw [hcov, omegaFactor, cK, ← hfac, mul_pow, ← Real.rpow_natCast (dF F ^ ((1:ℝ)/2)), ← Real.rpow_mul hd.le,
      Real.sqrt_eq_rpow]
    have hk' : ((k : ℝ) - 1) / 2 = (1:ℝ)/2 * k - 1/2 := by ring
    rw [hk', Real.rpow_sub hd]
    have hA : 0 < dF F ^ ((1:ℝ)/2 * k) := Real.rpow_pos_of_pos hd _
    have hB : 0 < dF F ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hd _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  have hc : (covol (latM 𝔞) : ℂ) ≠ 0 := by
    rw [hcov]; exact_mod_cast (inv_pos.2 (mul_pos (Real.sqrt_pos.2 hd) hn)).ne'
  have hf : (fac : ℂ) ≠ 0 := by exact_mod_cast hfac0.ne'
  calc _ = (((nrm 𝔞 ^ (k - 1) / (fac * covol (latM 𝔞)) : ℝ)) : ℂ) := by
        rw [lipConst, hfac]; push_cast
        rw [hfac] at hf; push_cast at hf
        field_simp
    _ = _ := by rw [hreal]; push_cast; rfl

end GlobalTheory.LipEisConst
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem dM_X_inl_entry {n : ℕ} (ε : Fin n → Bool) (x : Mode ε) (a b : Fin n) :
    dM ε x (X (Sum.inl (a, b))) =
      (if x.1.1 = b then X (Sum.inl (a, x.1.2)) else 0) - (if a = x.1.2 then X (Sum.inl (x.1.1, b)) else 0) := by
  classical
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inl]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single x.1.2]
    · by_cases h : x.1.1 = b <;> simp [Matrix.single_apply, h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp
  · rw [Finset.sum_eq_single x.1.1]
    · by_cases h : a = x.1.2
      · simp [Matrix.single_apply, h]
      · simp [Matrix.single_apply, h, Ne.symm h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp

theorem dM_block_entries : BlockDeterminantCondition := by
  intro n ε a b hab
  classical
  cases ha : ε a with
  | true =>
    refine ⟨fun x y => if x.1.1 = b ∧ y = ⟨(a, x.1.2), ha, x.2.2⟩ then 1 else 0, fun x => ?_⟩
    have hne : a ≠ x.1.2 := by
      intro h
      have := x.2.2
      rw [← h, ha] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, sub_zero, Finset.sum_eq_single (⟨(a, x.1.2), ha, x.2.2⟩ : Mode ε)]
    · by_cases h : x.1.1 = b <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp
  | false =>
    have hb : ε b = false := by rw [← hab, ha]
    refine ⟨fun x y => if a = x.1.2 ∧ y = ⟨(x.1.1, b), x.2.1, hb⟩ then -1 else 0, fun x => ?_⟩
    have hne : x.1.1 ≠ b := by
      intro h
      have := x.2.1
      rw [h, hb] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, zero_sub, Finset.sum_eq_single (⟨(x.1.1, b), x.2.1, hb⟩ : Mode ε)]
    · by_cases h : a = x.1.2 <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp

end GlobalTheory.PsCo.Cw2a
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem isFam_iff_values (ι : Type) (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) :
    IsFam act w f ↔ ∀ (i : ι) (γ : SL(2, ℤ)) (τ : ℍ),
      f i (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * f (act i γ) τ := by
  unfold IsFam
  refine forall_congr' fun i => forall_congr' fun γ => ?_
  rw [funext_iff]
  refine forall_congr' fun τ => ?_
  have hD : UpperHalfPlane.denom γ τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hne : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [ModularForm.SL_slash_apply, zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hne), hD,
    mul_comm (f (act i γ) τ)]

end GlobalTheory.QFam
end
