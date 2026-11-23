module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AnisotropicFiniteLengthsOfShortLatticeVector
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm

theorem _root_.GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ), ¬ IsSquare (δ : F) → ∃ S : Finset (HeightOneSpectrum (𝓞 F)), admitted F S ∧ δ ∈ sUnits F S ∧ ∀ t : Fˣ, (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → t ∈ normSub (algebraMap F (v.adicCompletion F)) (δ : F)) → t ∈ sUnits F S ⊔ normSub (RingHom.id F) (δ : F) := by
  first | exact @GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub | exact GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub | (intros; apply GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
open scoped Pointwise

namespace GlobalTheory.SplitCriterion

theorem frob_fix_of_ncard_primes_eq_finrank (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N]
    [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard
      = Module.finrank K M) (σ : N ≃ₐ[K] N) (hσ : GlobalTheory.NT.IsFrob N 𝔭 σ) : ∀ x ∈ M, σ x = x := by
  have := 𝔭.isPrime
  obtain ⟨P, hP, hPo, hx⟩ := hσ
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hq : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.ne_bot
  have hfix : σ⁻¹ • P = P := by
    symm
    refine hPm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun x hxP => ?_
    rw [Ideal.mem_inv_pointwise_smul_iff]
    have h1 := P.add_mem (hx x) (P.pow_mem_of_mem hxP _ (Nat.pos_of_ne_zero hq))
    rw [sub_add_cancel] at h1
    exact h1
  let f : (N ≃ₐ[K] N) → Ideal (𝓞 M) := fun σ => (σ⁻¹ • P).under (𝓞 M)
  have hker : ∀ σ τ, σ⁻¹ * τ ∈ M.fixingSubgroup → f σ = f τ := by
    intro σ τ e
    have e' := (IntermediateField.mem_fixingSubgroup_iff _ _).1 e
    ext x
    simp only [f, Ideal.under, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff]
    have : (σ⁻¹ * τ) • algebraMap (𝓞 M) (𝓞 N) x = algebraMap (𝓞 M) (𝓞 N) x := by
      apply RingOfIntegers.ext
      exact e' _ (x : M).2
    rw [mul_smul, inv_smul_eq_iff] at this
    rw [this]
  have hr : Set.range f = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨inferInstance, ⟨?_⟩⟩
      simp only [f]
      rw [Ideal.under_under]
      exact Ideal.LiesOver.over
    · rintro ⟨hQ, hQo⟩
      obtain ⟨P', hP', hPo'⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 N)))
      have : P'.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans P' Q _
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 N) (N ≃ₐ[K] N) P P'
        (hPo.over.symm.trans this.over)
      exact ⟨g⁻¹, by simp only [f]; rw [inv_inv, ← hg]; exact hPo'.over.symm⟩
  have hs : (fun Q : HeightOneSpectrum (𝓞 M) => Q.asIdeal) ''
      {Q | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal} = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩
    · rintro ⟨hQ, hQo⟩
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQo.over.symm, rfl⟩
  rw [← Set.ncard_image_of_injective _ (fun _ _ e => HeightOneSpectrum.ext e), hs, ← hr,
    IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq] at h
  let F : (N ≃ₐ[K] N) ⧸ M.fixingSubgroup → Set.range f :=
    Quotient.lift (fun g => ⟨f g, g, rfl⟩) fun a b e =>
      Subtype.ext (hker a b (QuotientGroup.leftRel_apply.1 e))
  have hF : Function.Surjective F := by
    rintro ⟨_, g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hinj : Function.Injective F := (hF.bijective_of_nat_card_le h.ge).1
  have h1 : F (QuotientGroup.mk 1) = F (QuotientGroup.mk σ) := by
    apply Subtype.ext
    change f 1 = f σ
    simp only [f]
    rw [hfix, inv_one, one_smul]
  have h2 := QuotientGroup.eq.1 (hinj h1)
  rw [inv_one, one_mul] at h2
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h2

end GlobalTheory.SplitCriterion
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
open scoped Pointwise

namespace GlobalTheory.SplitCriterion

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N]

theorem mem_of_smul_eq (H : Subgroup (N ≃ₐ[K] N)) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ σ, GlobalTheory.NT.IsFrob N 𝔭 σ → σ ∈ H) (P : Ideal (𝓞 N)) [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal]
    (τ : N ≃ₐ[K] N) (hτ : τ • P = P) : τ ∈ H := by
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 N ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := hP.isMaximal hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (N ≃ₐ[K] N) P
  have hu : P.under (𝓞 K) = 𝔭.asIdeal := hPo.over.symm
  set q := Ideal.absNorm 𝔭.asIdeal with hq
  have hq' : q = Nat.card (𝓞 K ⧸ 𝔭.asIdeal) := by rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hσ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ q := fun x => by
    have := hσ x
    rw [hu, ← hq'] at this
    rw [← map_pow, Ideal.Quotient.eq]
    exact this
  have hσH : σ ∈ H := h σ ⟨P, hP, hPo, fun x => by
    rw [← Ideal.Quotient.eq, map_pow]; exact hσ' x⟩
  have hpow : ∀ (i : ℕ) (x : 𝓞 N), Ideal.Quotient.mk P ((σ ^ i) • x) = Ideal.Quotient.mk P x ^ (q ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro x; rw [pow_succ', mul_smul, hσ', ih, ← pow_mul, pow_succ]
  letI : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 N ⧸ P) := Ideal.Quotient.field _
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ 𝔭.asIdeal)
  have : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 K ⧸ 𝔭.asIdeal) p⟩
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (𝓞 K ⧸ 𝔭.asIdeal) p (𝓞 N ⧸ P)
    (Ideal.Quotient.stabilizerHom P 𝔭.asIdeal (N ≃ₐ[K] N) ⟨τ, hτ⟩)
  have hτ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (τ • x) = Ideal.Quotient.mk P x ^ (q ^ i) := fun x => by
    rw [hq', ← hi, Ideal.Quotient.stabilizerHom_apply]
    rfl
  have h1 : σ * τ * (σ ^ i)⁻¹ ∈ H := h _ ⟨P, hP, hPo, fun x => by
    rw [← Ideal.Quotient.eq, map_pow, mul_smul, mul_smul, hσ', hτ', ← hpow, smul_inv_smul]⟩
  have h2 := H.mul_mem (H.mul_mem (H.inv_mem hσH) h1) (H.pow_mem hσH i)
  simpa [mul_assoc] using h2

theorem ncard_primes_eq_finrank_of_frob_fix (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N]
    [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x) :
    {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard
      = Module.finrank K M := by
  have := 𝔭.isPrime
  have hH : ∀ σ, GlobalTheory.NT.IsFrob N 𝔭 σ → σ ∈ M.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 (h σ hσ)
  obtain ⟨P, hP, hPo⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 N)))
  let f : (N ≃ₐ[K] N) → Ideal (𝓞 M) := fun σ => (σ⁻¹ • P).under (𝓞 M)
  have hker : ∀ σ τ, f σ = f τ ↔ σ⁻¹ * τ ∈ M.fixingSubgroup := by
    intro σ τ
    constructor
    · intro e
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 M) (𝓞 N) (N ≃ₐ[M] N)
        (σ⁻¹ • P) (τ⁻¹ • P) e
      have hg' : τ⁻¹ • P = (g.restrictScalars K) • (σ⁻¹ • P) := by
        rw [hg]; rfl
      have hgH : g.restrictScalars K ∈ M.fixingSubgroup :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩
      have h1 := mem_of_smul_eq M.fixingSubgroup 𝔭 hH (σ⁻¹ • P) (σ⁻¹ * τ * g.restrictScalars K) (by
        rw [mul_smul, ← hg', mul_smul, smul_inv_smul])
      exact (M.fixingSubgroup.mul_mem_cancel_right hgH).1 h1
    · intro e
      have e' := (IntermediateField.mem_fixingSubgroup_iff _ _).1 e
      ext x
      simp only [f, Ideal.under, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff]
      have : (σ⁻¹ * τ) • algebraMap (𝓞 M) (𝓞 N) x = algebraMap (𝓞 M) (𝓞 N) x := by
        apply RingOfIntegers.ext
        exact e' _ (x : M).2
      rw [mul_smul, inv_smul_eq_iff] at this
      rw [this]
  have hr : Set.range f = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨inferInstance, ⟨?_⟩⟩
      simp only [f]
      rw [Ideal.under_under]
      exact Ideal.LiesOver.over
    · rintro ⟨hQ, hQo⟩
      obtain ⟨P', hP', hPo'⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 N)))
      have : P'.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans P' Q _
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 N) (N ≃ₐ[K] N) P P'
        (hPo.over.symm.trans this.over)
      exact ⟨g⁻¹, by simp only [f]; rw [inv_inv, ← hg]; exact hPo'.over.symm⟩
  have hs : (fun Q : HeightOneSpectrum (𝓞 M) => Q.asIdeal) ''
      {Q | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal} = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩
    · rintro ⟨hQ, hQo⟩
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQo.over.symm, rfl⟩
  rw [← Set.ncard_image_of_injective _ (fun _ _ e => HeightOneSpectrum.ext e), hs, ← hr,
    IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq,
    ← Nat.card_congr (Setoid.quotientKerEquivRange f)]
  have : Setoid.ker f = QuotientGroup.leftRel M.fixingSubgroup := by
    ext σ τ
    rw [Setoid.ker_def, QuotientGroup.leftRel_apply, hker]
  rw [this]
  rfl

end GlobalTheory.SplitCriterion
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize Pointwise
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.DifferentBound

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem algebraMap_intTrace_eq_sum (x : 𝓞 L) :
    algebraMap (𝓞 K) (𝓞 L) (Algebra.intTrace (𝓞 K) (𝓞 L) x) = ∑ σ : L ≃ₐ[K] L, σ • x := by
  apply FaithfulSMul.algebraMap_injective (𝓞 L) L

  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L,
  Algebra.algebraMap_intTrace (L := L), trace_eq_sum_automorphisms, map_sum]
  rfl

theorem not_dvd_of_inertia (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)
    (h : ∀ σ : L ≃ₐ[K] L, (∀ x : 𝓞 L, σ • x - x ∈ P) → σ = 1) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP
  have := Ideal.IsPrime.isMaximal inferInstance hP
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L)] at hcard
  have hb : P.inertia (L ≃ₐ[K] L) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    exact h σ hσ
  rw [hb, Subgroup.card_bot] at hcard
  rw [not_dvd_differentIdeal_iff]
  exact Ideal.ramificationIdx_eq_one_iff.1 hcard.symm

theorem not_pow_dvd (n : ℕ) (hn : 0 < n) (P Q : Ideal (𝓞 L)) [hP : P.IsMaximal] (m : ℕ) (hnP : (n : 𝓞 L) ∈ P)
    (hPQ : P ⊔ Q = ⊤) (h : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} = P ^ m * Q) :
    ¬ P ^ m ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  classical
  have hco : IsCoprime (P ^ m) Q := (Ideal.isCoprime_iff_sup_eq.2 hPQ).pow_left
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1
    ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hco))
  refine not_dvd_differentIdeal_of_intTrace_not_mem (𝓞 K)
    (p := Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 K)}) (P ^ m) Q ?_ x hx ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast, h]
  intro htr
  have hle : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≤ P ^ m := h ▸ Ideal.mul_le_left
  have h1 : ∑ σ : L ≃ₐ[K] L, σ • x ∈ P ^ m := by
    rw [← algebraMap_intTrace_eq_sum]
    apply hle
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) htr
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  set S := MulAction.stabilizer (L ≃ₐ[K] L) P
  have h2 : ∀ σ : L ≃ₐ[K] L, σ • x - (if σ ∈ S then 1 else 0) ∈ P ^ m := by
    intro σ
    split_ifs with hσ
    · have h3 : σ • a ∈ σ • P ^ m := Ideal.smul_mem_pointwise_smul σ a _ ha
      rw [smul_pow', MulAction.mem_stabilizer_iff.1 hσ] at h3
      have h4 : σ • x - 1 = -(σ • a) := by
        rw [← smul_one σ, ← hax, smul_add]; ring
      rw [h4]
      exact neg_mem h3
    · rw [sub_zero]
      have h3 : σ • x ∈ σ • Q := Ideal.smul_mem_pointwise_smul σ x _ hx
      have h4 : σ • Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} =
          Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} := by
        rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton, map_natCast]
      have h5 : P ^ m ∣ (σ • P) ^ m * σ • Q := by
        rw [← smul_pow', ← smul_mul', ← h, h4]
        exact Ideal.dvd_iff_le.2 hle
      have hM : (σ • P).IsMaximal := by
        rw [Ideal.pointwise_smul_def]
        exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ)
      have h6 : IsCoprime P (σ • P) :=
        Ideal.isCoprime_iff_sup_eq.2 (hP.coprime_of_ne hM fun e => hσ (MulAction.mem_stabilizer_iff.2 e.symm))
      exact Ideal.dvd_iff_le.1 ((h6.pow).dvd_of_dvd_mul_left h5) h3
  have h7 : ((Nat.card S : ℕ) : 𝓞 L) ∈ P ^ m := by
    have h8 := sub_mem h1 (Ideal.sum_mem _ fun σ (_ : σ ∈ Finset.univ) => h2 σ)
    rw [Finset.sum_sub_distrib, sub_sub_cancel, Finset.sum_boole] at h8
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h9 : ((Module.finrank K L : ℕ) : 𝓞 L) ∈ P ^ m := by
    obtain ⟨c, hc⟩ := S.card_subgroup_dvd_card
    rw [← IsGalois.card_aut_eq_finrank, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h7
  have h10 : P ^ m * P ∣ P ^ m * Q := by
    rw [← h, Ideal.dvd_span_singleton, Nat.cast_mul, mul_comm (n : 𝓞 L)]
    exact Ideal.mul_mem_mul h9 hnP
  have h0 : P ^ m ≠ 0 := by
    intro e
    rw [e, zero_mul, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at h
    exact (Nat.mul_pos hn Module.finrank_pos).ne' h
  have h11 := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left h0).1 h10)
  exact hP.ne_top (by rw [← hPQ, sup_eq_left.2 h11])


omit K L in
theorem natCast_mul_finrank_mem_differentIdeal :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (n : ℕ), 0 < n →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn L 𝔭) →
      ((n * Module.finrank K L : ℕ) : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  intro K L _ _ _ _ _ _ n hn hu
  classical
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := differentIdeal_ne_bot
  have hI : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Nat.mul_pos hn Module.finrank_pos).ne'
  rw [← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0]
  intro P hP
  have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hPm := hPp.isMaximal hP0
  by_cases hnP : (n : 𝓞 L) ∈ P
  · obtain ⟨Q, hPQ, h⟩ := Ideal.eq_prime_pow_mul_coprime hI P
    have h1 := not_pow_dvd K L n hn P Q _ hnP hPQ h
    exact (emultiplicity_lt_iff_not_dvd.2 h1).le.trans (le_emultiplicity_of_pow_dvd ⟨Q, h⟩)
  · have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0
    have h1 := hu ⟨P.under (𝓞 K), inferInstance, hp⟩ (fun e => hnP (by simpa using Ideal.mem_comap.1 e))
    have h2 := not_dvd_of_inertia K L P hP0 fun σ hσ => h1 σ ⟨P, hPp, ⟨rfl⟩, hσ⟩
    rw [emultiplicity_eq_zero.2 h2]
    exact zero_le

end GlobalTheory.DifferentBound
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ShortSmall E → AnisoSmall E := by
  first | exact @GlobalTheory.AnisoSize.anisoSmall_of_shortSmall | exact GlobalTheory.AnisoSize.anisoSmall_of_shortSmall | (intros; apply GlobalTheory.AnisoSize.anisoSmall_of_shortSmall <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

theorem _root_.GlobalTheory.T.map_different_le_different_sup_intermediateField : ∀ (F F' : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField ↥(F ⊔ F')], letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra; (differentIdeal ℤ (𝓞 F')).map (RingOfIntegers.mapRingHom (IntermediateField.inclusion (le_sup_right : F' ≤ F ⊔ F')).toRingHom) ≤ differentIdeal (𝓞 F) (𝓞 ↥(F ⊔ F')) := by
  first | exact @GlobalTheory.DiffBaseChange.map_different_le_sup | exact GlobalTheory.DiffBaseChange.map_different_le_sup | (intros; apply GlobalTheory.DiffBaseChange.map_different_le_sup <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory

theorem log_rootDiscr_le_of_natCast_mem_differentIdeal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (N : ℕ), 0 < N → (N : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) → Real.log |((discr L : ℤ) : ℝ)| / Module.finrank ℚ L ≤ Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K + Real.log N := by
  intro K L _ _ _ _ _ N hN hmem
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have h2 : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have h3 : Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) = N ^ Module.finrank ℚ L := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  rw [h3] at h2
  have h4 := Nat.le_of_dvd (pow_pos hN _) h2
  have h5 : (discr L).natAbs ≤ N ^ Module.finrank ℚ L * (discr K).natAbs ^ Module.finrank K L := by
    rw [h1]; exact Nat.mul_le_mul_right _ h4
  have hL : (0 : ℝ) < |((discr L : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero L)
  have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h6 : |((discr L : ℤ) : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ L * |((discr K : ℤ) : ℝ)| ^ Module.finrank K L := by
    have : (((discr L).natAbs : ℕ) : ℝ) ≤ ((N ^ Module.finrank ℚ L * (discr K).natAbs ^ Module.finrank K L : ℕ) : ℝ) := by
      exact_mod_cast h5
    simpa [Nat.cast_natAbs] using this
  have h7 := Real.log_le_log hL h6
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h7
  have h8 : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L := Module.finrank_mul_finrank ℚ K L
  have hk : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hl : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have h9 : (Module.finrank ℚ K : ℝ) * Module.finrank K L = Module.finrank ℚ L := by exact_mod_cast h8
  rw [div_le_iff₀ hl]
  refine h7.trans (le_of_eq ?_)
  rw [← h9]
  field_simp
  ring

end GlobalTheory
end
