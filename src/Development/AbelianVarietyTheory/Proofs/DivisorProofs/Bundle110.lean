module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.Tactic.Continuity
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
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

@[expose] public section

section

open NumberField

namespace GlobalTheory

theorem exists_trace_dual_system (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    ∃ (m : ℕ) (ω : Fin m → 𝓞 L) (η : Fin m → L),
      (∀ i, η i ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ t : L, t = ∑ i, algebraMap K L (Algebra.trace K L (η i * t)) * (ω i : L) := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, F, G, -, -, hFG⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 L)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) L :=
    IsIntegralClosure.isLocalization (𝓞 K) K L (𝓞 L)
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K _
  let f : Fin m → Module.Dual K L := fun i =>
    hbc.lift ((Algebra.linearMap (𝓞 K) K) ∘ₗ (LinearMap.proj i) ∘ₗ G)
  have hf : ∀ i (a : 𝓞 L), f i (a : L) = algebraMap (𝓞 K) K (G a i) := fun i a =>
    hbc.lift_eq _ a
  let η : Fin m → L := fun i =>
    ((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)).symm (f i)
  have hη : ∀ i t, Algebra.trace K L (η i * t) = f i t := fun i t =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate K L) (f i) t
  refine ⟨m, fun i => F (Pi.single i 1), η, fun i => ?_, fun t => ?_⟩
  · rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨G b i, ?_⟩
    rw [Algebra.traceForm_apply, hη]
    exact (hf i b).symm
  · simp_rw [hη]
    have h := hbc.algHom_ext (LinearMap.id : L →ₗ[K] L)
      (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (fun a => by
        have ha : a = ∑ i, G a i • F (Pi.single i 1) := by
          have h1 : a = F (G a) := (LinearMap.congr_fun hFG a).symm
          conv_lhs => rw [h1, LinearMap.pi_apply_eq_sum_univ]
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 2
          ext j
          simp [Pi.single_apply, eq_comm]
        change (a : L) = (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (a : L)
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, hf, algebraMap_smul]
        conv_lhs => rw [ha]
        change algebraMap (𝓞 L) L _ = _

        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap.map_smul _ _)
    have h2 := LinearMap.congr_fun h t
    simpa [LinearMap.sum_apply, Algebra.smul_def] using h2

open NumberField in
private theorem exists_integral_traceDual_expansion (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    ∃ (N : ℕ) (e : Fin N → 𝓞 L) (c : Fin N → L),
      (∀ k, c k ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ y : L, y = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) • c k := by
  classical
  obtain ⟨N, F, hF⟩ := Module.Finite.exists_fin' (𝓞 K) (𝓞 L)
  have : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  have hP : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨h, hh⟩ := Module.projective_lifting_property F LinearMap.id hF
  obtain ⟨e, hdec⟩ : ∃ e : Fin N → 𝓞 L, ∀ b : 𝓞 L, b = ∑ k, h b k • e k := by
    refine ⟨fun k => F (Pi.single k 1), fun b => ?_⟩
    have hb := LinearMap.congr_fun hh b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hb
    conv_lhs => rw [← hb, ← Finset.univ_sum_single (h b)]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Pi.single k (h b k) : Fin N → 𝓞 K) = h b k • Pi.single k 1 by
      rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul]
  let φ : Fin N → (𝓞 L →ₗ[𝓞 K] 𝓞 K) := fun k => LinearMap.proj k ∘ₗ h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin N → Module.Dual K L,
      ∀ k (b : 𝓞 L), ψ k (algebraMap (𝓞 L) L b) = algebraMap (𝓞 K) K (h b k) :=
    ⟨fun k => IsLocalizedModule.mapExtendScalars (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K) K
      (φ k), fun k b => IsLocalizedModule.map_apply (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K)
      (φ k) b⟩
  have hB := traceForm_nondegenerate K L
  obtain ⟨c, hc⟩ : ∃ c : Fin N → L, ∀ k y, Algebra.trace K L (c k * y) = ψ k y :=
    ⟨fun k => ((Algebra.traceForm K L).toDual hB).symm (ψ k), fun k y => by
      rw [← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_toDual_symm_apply _ _⟩
  clear hh hF F this hP
  have hexpO : ∀ b : 𝓞 L,
      algebraMap (𝓞 L) L b = ∑ k, ψ k (algebraMap (𝓞 L) L b) • algebraMap (𝓞 L) L (e k) := by
    intro b
    conv_lhs => rw [hdec b]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L, Algebra.smul_def]
  have hexp : ∀ y : L, y = ∑ k, ψ k y • algebraMap (𝓞 L) L (e k) := by
    intro y
    obtain ⟨⟨b, s⟩, hbs⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) y
    obtain ⟨a, ha, has⟩ := s.2
    have ha0 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    have hy : y = (algebraMap (𝓞 K) K a)⁻¹ • algebraMap (𝓞 L) L b := by
      rw [← hbs, ← has, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L, mul_comm, ← Algebra.smul_def, smul_smul,
        inv_mul_cancel₀ ha0, one_smul]
    clear hbs has
    rw [hy]
    conv_lhs => rw [hexpO b]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_assoc]
  refine ⟨N, e, c, fun k => ?_, fun y => ?_⟩
  · rw [Submodule.mem_traceDual]
    rintro _ ⟨b, rfl⟩
    rw [Algebra.traceForm_apply]
    exact ⟨h b k, by simpa [hψ, Algebra.smul_def, mul_comm] using (hc k (algebraMap (𝓞 L) L b)).symm⟩
  · rw [← sub_eq_zero]
    refine hB.1 _ fun u => ?_
    have h1 : Algebra.trace K L (y * u) = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) *
        Algebra.trace K L (c k * u) := by
      conv_lhs => rw [hexp u]

      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hc]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm y]; ring

    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Algebra.traceForm_apply, smul_eq_mul, h1]
    rw [sub_eq_zero]


open NumberField in
theorem _root_.GlobalTheory.differentIdeal_smul_mem_span_rational :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (n : ℕ) (M : Submodule (𝓞 L) (Fin n → L)), (∀ (σ : L ≃ₐ[K] L), ∀ x ∈ M, (fun i => σ (x i)) ∈ M) → ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∀ x ∈ M, d • x ∈ Submodule.span (𝓞 L) {y : Fin n → L | y ∈ M ∧ ∃ y0 : Fin n → K, y = fun i => algebraMap K L (y0 i)} := by
  intro K L _ _ _ _ _ _ n M hM d hd x hx
  classical
  obtain ⟨N, e, c, hcD, hswap⟩ := exists_integral_traceDual_expansion K L
  have hdL : algebraMap (𝓞 L) L d ∈ (1 : Submodule (𝓞 L) L) / Submodule.traceDual (𝓞 K) K 1 := by
    rw [← coeSubmodule_differentIdeal (𝓞 K) K (𝓞 L)]
    exact (IsLocalization.mem_coeSubmodule _ _).mpr ⟨d, hd, rfl⟩
  have hdc : ∀ k, ∃ r : 𝓞 L, algebraMap (𝓞 L) L r = algebraMap (𝓞 L) L d * c k := fun k =>
    Submodule.mem_one.mp (Submodule.mem_div_iff_forall_mul_mem.mp hdL _ (hcD k))
  choose r hr using hdc
  set t : Fin N → Fin n → L :=
    fun k i => algebraMap K L (Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i)) with ht
  have htM : ∀ k, t k ∈ M := by
    intro k
    have : t k = ∑ σ : L ≃ₐ[K] L, fun i => σ ((e k • x) i) := by
      funext i
      simp only [ht, Finset.sum_apply, Pi.smul_apply, trace_eq_sum_automorphisms, Algebra.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun σ _ => hM σ _ (M.smul_mem _ hx)
  have hdx : d • x = ∑ k, r k • t k := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, ht, Algebra.smul_def, hr]
    conv_lhs => rw [hswap (x i)]
    simp only [Finset.mul_sum, Algebra.smul_def]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdx]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨htM k, fun i => Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i), rfl⟩)

end GlobalTheory
end

section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat

variable {E : Type} [Field E] [NumberField E]

def scLat {n : ℕ} (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ}
  zero_mem' := fun c _ => by rw [smul_zero]; exact Λ.zero_mem
  add_mem' := fun hx hy c hc => by rw [smul_add]; exact Λ.add_mem (hx c hc) (hy c hc)
  smul_mem' := fun r y hy c hc => by rw [smul_comm]; exact Λ.smul_mem r (hy c hc)

theorem mem_scLat {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {Λ : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} :
    y ∈ scLat 𝔞 Λ ↔ ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ := Iff.rfl

def blkA {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin a → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inl)

def blkB {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin b → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inr)

def pairLat {a b d : ℕ} (ΛA : Submodule (𝓞 E) (Fin a → E)) (ΛB : Submodule (𝓞 E) (Fin b → E))
    (e : Fin a ⊕ Fin b ≃ Fin d) : Submodule (𝓞 E) (Fin d → E) :=
  ΛA.comap (blkA e) ⊓ ΛB.comap (blkB e)

theorem mem_pairLat {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}
    {e : Fin a ⊕ Fin b ≃ Fin d} {x : Fin d → E} :
    x ∈ pairLat ΛA ΛB e ↔ (fun k => x (e (.inl k))) ∈ ΛA ∧ (fun k => x (e (.inr k))) ∈ ΛB := Iff.rfl

end GlobalTheory.SkewLat

end
end

section

open NumberField

namespace GlobalTheory

theorem absNorm_map_ringOfIntegers_hom (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (𝔞 : Ideal (𝓞 E)) :
    Module.finrank ℚ E ∣ Module.finrank ℚ K ∧
      Ideal.absNorm (𝔞.map τ) = Ideal.absNorm 𝔞 ^ (Module.finrank ℚ K / Module.finrank ℚ E) := by
  have hτinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    rw [eq_intCast, map_intCast]
    constructor
    · intro h
      have : ((n : 𝓞 K) : K) = 0 := by rw [h]; rfl
      exact_mod_cast this
    · rintro rfl; simp
  have hinj : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective (K := K)).comp hτinj
  let φ : E →+* K := IsFractionRing.lift hinj
  letI : Algebra E K := φ.toAlgebra
  have hmap : τ = algebraMap (𝓞 E) (𝓞 K) := by
    ext x
    change ((algebraMap (𝓞 K) K).comp τ) x = φ (algebraMap (𝓞 E) E x)
    rw [IsFractionRing.lift_algebraMap]
  have htower := Module.finrank_mul_finrank ℚ E K
  have hE : 0 < Module.finrank ℚ E := Module.finrank_pos
  refine ⟨⟨Module.finrank E K, htower.symm⟩, ?_⟩
  have hq : Module.finrank ℚ K / Module.finrank ℚ E = Module.finrank E K := by
    rw [← htower, Nat.mul_div_cancel_left _ hE]
  rw [hq, hmap, Ideal.absNorm_algebraMap (𝓞 E) (𝓞 K) 𝔞,
    ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K]

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem primaryTorsion_divisible_and_gTorsion :
    ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (g : ℕ) (I : Ideal (𝓞 E)), g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → (∀ x : M, ∃ y : M, g • y = x) → (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → ∃ y : M, g • y = x ∧ ∀ a ∈ I ^ (j + 1), a • y = 0) ∧ (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → g • x = 0 → ∀ a ∈ I, a • x = 0) := by
  intro E _ _ M _ _ g I hg hN hg2 hdiv
  have hgI : (g : 𝓞 E) ∈ I := by
    have := Ideal.absNorm_mem I
    rwa [hN] at this
  have hIne : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN
    exact hg.ne_zero hN.symm
  have hprime : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hg)
  have hmax : I.IsMaximal := hprime.isMaximal hIne
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 ((Ideal.span_singleton_le_iff_mem I).2 hgI)
  have hJI : ¬ J ≤ I := by
    intro h
    apply hg2
    have h2 : Ideal.span {(g : 𝓞 E)} ≤ I ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self _)
  have hsup : I ⊔ J = ⊤ := by
    by_contra h
    exact hJI (le_sup_right.trans (le_of_eq (hmax.eq_of_le h le_sup_left).symm))
  have hpow : ∀ k : ℕ, I ^ k ⊔ J = ⊤ := fun k => Ideal.pow_sup_eq_top hsup
  refine ⟨fun j x hx => ?_, fun j x hx hgx a ha => ?_⟩
  · obtain ⟨y0, hy0⟩ := hdiv x
    have h1 : (1 : 𝓞 E) ∈ I ^ j ⊔ J := by rw [hpow j]; exact Submodule.mem_top
    obtain ⟨f, hf, e, he, hfe⟩ := Submodule.mem_sup.1 h1
    refine ⟨e • y0, ?_, ?_⟩
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_comm, Nat.cast_smul_eq_nsmul (𝓞 E), hy0]
      have : e = 1 - f := by rw [← hfe]; ring
      rw [this, sub_smul, one_smul, hx f hf, sub_zero]
    · intro a ha
      have hae : a * e ∈ I ^ j * Ideal.span {(g : 𝓞 E)} := by
        rw [hJ, ← mul_assoc, ← pow_succ]
        exact Ideal.mul_mem_mul ha he
      have hker : I ^ j * Ideal.span {(g : 𝓞 E)} ≤
          LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) M y0) := by
        rw [Ideal.mul_le]
        intro c hc s hs
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hs
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← mul_assoc, mul_smul,
          Nat.cast_smul_eq_nsmul (𝓞 E), hy0]
        exact hx _ (Ideal.mul_mem_right _ _ hc)
      have := hker hae
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this
      rw [smul_smul]; exact this
  · have hker : I ^ j ⊔ Ideal.span {(g : 𝓞 E)} ≤
        LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) M x) := by
      refine sup_le (fun b hb => ?_) ?_
      · rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hx b hb
      · refine (Ideal.span_singleton_le_iff_mem _).2 ?_
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Nat.cast_smul_eq_nsmul]
        exact hgx
    have hIle : I ≤ I ^ j ⊔ Ideal.span {(g : 𝓞 E)} := by
      cases j with
      | zero => rw [pow_zero, Ideal.one_eq_top]; exact le_top.trans le_sup_left
      | succ k =>
        have h : I = I ^ (k + 1) ⊔ Ideal.span {(g : 𝓞 E)} := by
          calc I = I * (I ^ k ⊔ J) := by rw [hpow k, Ideal.mul_top]
            _ = I ^ (k + 1) ⊔ Ideal.span {(g : 𝓞 E)} := by rw [Ideal.mul_sup, hJ, pow_succ']
        exact h.le
    have := hker (hIle ha)
    rwa [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem prod_arg_real_unit_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ)
    (hq : q.Prime) (hq2 : 2 < q)
    (u : (𝓞 E)ˣ) (hu : (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)})
    (hreal : ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E)) :
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) /
      ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  set x : E := ((u : 𝓞 E) : E) with hx
  have hnorm : ∏ w : InfinitePlace E, ‖w.embedding x‖ = 1 := by
    have h1 := InfinitePlace.prod_eq_abs_norm x
    have hN : |Algebra.norm ℚ x| = 1 := Units.norm E u
    rw [hN] at h1
    have h2 : ∏ w : InfinitePlace E, w x ^ w.mult =
        (∏ w : InfinitePlace E, ‖w.embedding x‖) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [IsTotallyComplex.mult_eq, InfinitePlace.norm_embedding_eq]
    rw [h2] at h1
    have h0 : 0 ≤ ∏ w : InfinitePlace E, ‖w.embedding x‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    exact (pow_eq_one_iff_of_nonneg h0 two_ne_zero).mp (by exact_mod_cast h1)
  rw [Finset.prod_div_distrib, ← Complex.ofReal_prod, hnorm, Complex.ofReal_one, div_one]
  set P : ℂ := ∏ w : InfinitePlace E, w.embedding x with hP
  have hPreal : starRingEnd ℂ P = P := by
    rw [hP, map_prod]
    exact Finset.prod_congr rfl fun w _ => hreal w.embedding
  have hPnorm : ‖P‖ = 1 := by rw [hP, norm_prod, hnorm]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hu
  have hxy : x = 1 + ((y : 𝓞 E) : E) * (q : E) := by
    have : (u : 𝓞 E) = 1 + y * (q : 𝓞 E) := by rw [hy]; ring
    rw [hx, this]; push_cast; ring
  have hcong : ∃ s ∈ integralClosure ℤ ℂ, P = 1 + s * (q : ℂ) := by
    rw [hP]
    refine Finset.prod_induction _ (fun z => ∃ s ∈ integralClosure ℤ ℂ, z = 1 + s * (q : ℂ))
      ?_ ⟨0, zero_mem _, by ring⟩ ?_
    · rintro a b ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
      refine ⟨s + t + s * t * q, ?_, by ring⟩
      exact add_mem (add_mem hs ht) (mul_mem (mul_mem hs ht) (Subalgebra.natCast_mem _ q))
    · intro w _
      refine ⟨w.embedding ((y : 𝓞 E) : E), ?_, ?_⟩
      · rw [mem_integralClosure_iff]
        exact (RingOfIntegers.isIntegral_coe y).map w.embedding.toIntAlgHom
      · rw [hxy]; simp
  obtain ⟨s, hs, hPs⟩ := hcong
  have hre : P = (P.re : ℂ) := ((Complex.conj_eq_iff_re).mp hPreal).symm
  have habs : |P.re| = 1 := by
    rw [← hPnorm, hre, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  rcases (abs_eq zero_le_one).mp habs with h | h
  · rw [hre, h, Complex.ofReal_one]
  · exfalso
    have hPm : P = -1 := by rw [hre, h]; simp
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hs' : s = algebraMap ℚ ℂ (-2 / q) := by
      rw [hPm] at hPs
      rw [map_div₀, map_neg, map_ofNat, map_natCast]
      field_simp
      linear_combination -hPs
    rw [mem_integralClosure_iff, hs'] at hs
    have hint : IsIntegral ℤ ((-2 / q : ℚ)) :=
      (isIntegral_algebraMap_iff ).mp hs
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h2 : (n : ℚ) * q = -2 := by
      rw [show (algebraMap ℤ ℚ n) = (n : ℚ) from rfl] at hn
      rw [hn]; field_simp
    have h3 : n * (q : ℤ) = -2 := by exact_mod_cast h2
    have h4 : (q : ℤ) ∣ 2 := ⟨-n, by linarith⟩
    have h5 : q ∣ 2 := by exact_mod_cast h4
    have := Nat.le_of_dvd two_pos h5
    omega

end GlobalTheory
end

section

namespace GlobalTheory.EigenvalueNormAtMostOne

theorem norm_eigenvalue_le_one_of_entries {K : Type} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (c : Fin n → K) (μ : K) (hc : c ≠ 0) (h : A.mulVec c = μ • c) : ‖μ‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hc
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖c j‖)
    ⟨k, Finset.mem_univ k⟩
  have hpos : 0 < ‖c i‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hk) (hi k (Finset.mem_univ k))
  have hrow : ∑ j, A i j * c j = μ * c i := by
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct] using this
  have hle : ‖∑ j, A i j * c j‖ ≤ ‖c i‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j hj
    rw [norm_mul]
    calc ‖A i j‖ * ‖c j‖ ≤ 1 * ‖c i‖ :=
          mul_le_mul (hA i j) (hi j hj) (norm_nonneg _) zero_le_one
      _ = ‖c i‖ := one_mul _
  rw [hrow, norm_mul] at hle
  exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos

theorem norm_eigenvalue_le_one :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (O : Type) [inst_1 : CommRing O]
      (emb : O →+* PadicAlgCl l), (∀ (a : O), ‖(emb : O → PadicAlgCl l) a‖ ≤ (1 : ℝ)) →
      ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l) (μ : PadicAlgCl l),
        c ≠ (0 : Fin n → PadicAlgCl l) →
        Matrix.mulVec (Matrix.map N (⇑emb : O → PadicAlgCl l)) c = μ • c → ‖μ‖ ≤ (1 : ℝ) := by
  intro l _ O _ emb hemb n N c μ hc h
  exact norm_eigenvalue_le_one_of_entries _ (fun i j => hemb (N i j)) c μ hc h

end GlobalTheory.EigenvalueNormAtMostOne
end
