module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.Charpoly.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

open IsDedekindDomain NumberField
namespace GlobalTheory
namespace DegreeOneUniformiser

open IsDedekindDomain NumberField in
private theorem adicCompletionIntegers_integers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers F) :=
  ⟨Subtype.val_injective, fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2,
    fun x hx => ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mpr hx⟩, rfl⟩⟩


open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F)
    (h : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  have hI := adicCompletionIntegers_integers v
  have hunit : ∀ x : v.adicCompletionIntegers F, IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
    fun x => hI.isUnit_iff_valuation_eq_one
  have hle : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) ≤ 1 :=
    fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := (hunit π).mp hu
    rw [h] at this
    exact absurd this (by decide)
  · have hv : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
        WithZero.exp (-1 : ℤ) := by
      rw [← h, hab, Subring.coe_mul, map_mul]
    have ha0 : Valued.v (a : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
    have hb0 : Valued.v (b : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (a : v.adicCompletion F) = WithZero.exp m :=
      ⟨_, (WithZero.exp_log ha0).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (b : v.adicCompletion F) = WithZero.exp n :=
      ⟨_, (WithZero.exp_log hb0).symm⟩
    have ha := hle a
    have hb := hle b
    rw [hm, hn, ← WithZero.exp_add, WithZero.exp_inj] at hv
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb
    rw [hunit, hunit, hm, hn, ← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega


open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.DegreeOneUniformiser.exists_irreducible_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (ψ : E →+* v.adicCompletion F), (∀ a : F, ψ (algebraMap F E a) = algebraMap F (v.adicCompletion F) a) → (∀ x : 𝓞 E, ψ (x : E) ∈ v.adicCompletionIntegers F) → (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ψ ((x : E)⁻¹) ∉ v.adicCompletionIntegers F)) → ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ π : v.adicCompletionIntegers F, Irreducible π ∧ (π : v.adicCompletion F) = ψ (ϖ : E) := by
  intro F E _ _ _ _ _ v P ψ hψ hint hP ϖ hϖP hϖP2
  have hle : ∀ x : 𝓞 E, Valued.v (ψ (x : E)) ≤ 1 := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hint x)
  have hne : ∀ x : 𝓞 E, x ≠ 0 → Valued.v (ψ (x : E)) ≠ 0 := by
    intro x hx
    rw [Valuation.ne_zero_iff, map_ne_zero_iff _ ψ.injective]
    exact_mod_cast hx
  have hone : ∀ x : 𝓞 E, x ∉ P.asIdeal → Valued.v (ψ (x : E)) = 1 := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => hx (h ▸ P.asIdeal.zero_mem)
    have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp
      (not_not.mp (mt (hP x hx0).mpr hx))
    rw [map_inv₀, map_inv₀] at h1
    exact le_antisymm (hle x) ((inv_le_one₀ (zero_lt_iff.mpr (hne x hx0))).mp h1)
  have hϖ0 : ϖ ≠ 0 := fun h => hϖP2 (h ▸ Ideal.zero_mem _)
  have hlt : Valued.v (ψ (ϖ : E)) < 1 := by
    have h1 := (hP ϖ hϖ0).mp hϖP
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀] at h1
    exact (one_lt_inv₀ (zero_lt_iff.mpr (hne ϖ hϖ0))).mp h1
  obtain ⟨u, hu⟩ := v.intValuation_exists_uniformizer
  let f : 𝓞 E := ⟨algebraMap F E (u : F), (RingOfIntegers.isIntegral_coe u).algebraMap⟩
  have hf : Valued.v (ψ (f : E)) = WithZero.exp (-1 : ℤ) := by
    show Valued.v (ψ (algebraMap F E (u : F))) = _
    rw [hψ, ← hu, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (u : F)
  have hf0 : f ≠ 0 := fun h => by
    rw [h] at hf
    simp only [ZeroMemClass.coe_zero, map_zero] at hf
    exact WithZero.exp_ne_zero hf.symm
  have hfP : f ∈ P.asIdeal := by
    rw [hP f hf0, HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀, hf,
      ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem _).mpr hϖP : Ideal.span {ϖ} ≤ P.asIdeal)
  have hJP : ¬ J ≤ P.asIdeal := fun hJP => hϖP2 (by
    have hmem : ϖ ∈ Ideal.span {ϖ} := Ideal.mem_span_singleton_self ϖ
    rw [hJ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hJP hmem)
  obtain ⟨t, htJ, htP⟩ := Set.not_subset.mp hJP
  have hft : f * t ∈ Ideal.span {ϖ} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hfP htJ
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hft
  have hval := congrArg (fun x : 𝓞 E => Valued.v (ψ (x : E))) hs
  simp only [MulMemClass.coe_mul, map_mul] at hval
  rw [hone t htP, mul_one, hf] at hval
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v (ψ (ϖ : E)) := by
    rw [← hval]
    calc Valued.v (ψ (s : E)) * Valued.v (ψ (ϖ : E)) ≤ 1 * Valued.v (ψ (ϖ : E)) :=
          mul_le_mul' (hle s) le_rfl
      _ = Valued.v (ψ (ϖ : E)) := one_mul _
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (ψ (ϖ : E)) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log (hne ϖ hϖ0)).symm⟩
  rw [hm, WithZero.exp_le_exp] at hge
  rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  have hm1 : m = -1 := by omega
  refine ⟨⟨ψ (ϖ : E), hint ϖ⟩, _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued v _ ?_, rfl⟩
  rw [← hm1]
  exact hm

end DegreeOneUniformiser
end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem exists_base_denominator_of_finite {T C K : Type} [CommRing T] [IsDomain T] [CommRing C]
    [IsDomain C] [Field K] [Algebra T C] [Algebra C K] [IsFractionRing C K] [Algebra T K]
    [IsScalarTower T C K] [Module.Finite T C] (k : K) :
    ∃ t : T, t ≠ 0 ∧ ∃ c : C, algebraMap T K t * k = algebraMap C K c := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hint : IsIntegral T b := Algebra.IsIntegral.isIntegral b
  have h := Ideal.comap_ne_bot_of_integral_mem (R := T) (I := Ideal.span {b}) hb0
    (Ideal.mem_span_singleton_self b) hint
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at ht
  obtain ⟨d, hd⟩ := ht
  refine ⟨t, ht0, d * a, ?_⟩
  have hbK : algebraMap C K b ≠ 0 := by
    simpa using hb0
  rw [IsScalarTower.algebraMap_apply T C K, hd, map_mul, map_mul]
  field_simp

theorem finite_fractionRing_of_finite (T C F K : Type) [CommRing T] [IsDomain T] [CommRing C]
    [IsDomain C] [Field F] [Field K] [Algebra T C] [Algebra T F] [IsFractionRing T F]
    [Algebra C K] [IsFractionRing C K] [Algebra T K] [Algebra F K]
    [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C] : Module.Finite F K := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := T) (M := C)
  refine ⟨⟨s.image (algebraMap C K), ?_⟩⟩
  have key : ∀ c : C, algebraMap C K c ∈
      Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K) := by
    intro c
    have hc : c ∈ Submodule.span T (s : Set C) := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hx)))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro k _
  obtain ⟨t, ht, c, hc⟩ := exists_base_denominator_of_finite (T := T) (C := C) k
  have htF : algebraMap T F t ≠ 0 := by simpa using ht
  have : k = (algebraMap T F t)⁻¹ • algebraMap C K c := by
    rw [← hc, IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def, inv_smul_smul₀ htF]
  rw [this]
  exact Submodule.smul_mem _ _ (key c)

theorem isUnit_map_of_mem_nonZeroDivisors_tensor (T U C F K L : Type) [CommRing T] [IsDomain T]
    [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L]
    [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K]
    [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K]
    [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L]
    [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C]
    (φ : U ⊗[T] C →+* L ⊗[F] K) (hinj : Function.Injective φ)
    (hφ : ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) :
    ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by
  have hTU : ∀ t : T, t ≠ 0 → algebraMap T U t ≠ 0 := by
    intro t ht h0
    have h1 : algebraMap T L t = 0 := by
      rw [IsScalarTower.algebraMap_apply T U L, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply T F L] at h1
    apply ht
    simpa using h1
  have den : ∀ ω : L ⊗[F] K, ∃ u : U, u ≠ 0 ∧ ∃ s', φ (u ⊗ₜ 1) * ω = φ s' := by
    intro ω
    induction ω using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul l k =>
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := U) l
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbL : algebraMap U L b ≠ 0 := by simpa using hb0
      obtain ⟨t, ht, c, hc⟩ := exists_base_denominator_of_finite (T := T) (C := C) k
      refine ⟨algebraMap T U t * b, mul_ne_zero (hTU t ht) hb0, a ⊗ₜ c, ?_⟩
      rw [hφ, hφ, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hc,
        IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def (algebraMap T F t) k,
        ← TensorProduct.smul_tmul,
        Algebra.smul_def, ← IsScalarTower.algebraMap_apply T F L, map_mul,
        ← IsScalarTower.algebraMap_apply T U L]
      congr 1
      field_simp
    | add x y hx hy =>
      obtain ⟨u, hu, s₁, h₁⟩ := hx
      obtain ⟨v, hv, s₂, h₂⟩ := hy
      refine ⟨u * v, mul_ne_zero hu hv, (v ⊗ₜ 1) * s₁ + (u ⊗ₜ 1) * s₂, ?_⟩
      have : ((u * v) ⊗ₜ[T] (1 : C)) = (u ⊗ₜ 1) * (v ⊗ₜ 1) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this, map_add (f := _), map_mul, map_mul, map_mul, ← h₁, ← h₂]
      ring
  have : Module.Finite F K := finite_fractionRing_of_finite T C F K
  have : IsArtinianRing (L ⊗[F] K) := IsArtinianRing.of_finite L (L ⊗[F] K)
  intro s hs
  apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro ω hω
  obtain ⟨u, hu, s', h⟩ := den ω
  have h0 : s' * s = 0 := by
    apply hinj
    rw [map_mul, ← h, mul_assoc, hω, mul_zero, map_zero]
  have hs' : s' = 0 := (mem_nonZeroDivisors_iff_right.1 hs) s' h0
  have huL : algebraMap U L u ≠ 0 := by simpa using hu
  have hunit : IsUnit (φ (u ⊗ₜ 1)) := by
    rw [hφ, map_one]
    exact (IsUnit.mk0 _ huL).map (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := L) (B := K))
  rw [hs', map_zero] at h
  exact (hunit.mul_right_eq_zero).1 h

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem flat_tensor_embeds_tensor_fractionFields
    (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C]
    [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F]
    [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L]
    [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L]
    [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Flat T U] :
    ∃ φ : U ⊗[T] C →+* L ⊗[F] K, Function.Injective φ ∧
      ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c := by
  have hF : Module.Flat T F := IsLocalization.flat F (nonZeroDivisors T)
  have hK : Module.Flat T K := Module.Flat.trans T F K
  let f : U →ₐ[T] L := IsScalarTower.toAlgHom T U L
  let g : C →ₐ[T] K := IsScalarTower.toAlgHom T C K
  let e : L ⊗[F] K ≃ₐ[F] L ⊗[T] K :=
    IsLocalization.algebraTensorEquiv (nonZeroDivisors T) F L K
  refine ⟨(e.symm.toRingHom : L ⊗[T] K →+* L ⊗[F] K).comp
    (Algebra.TensorProduct.map f g).toRingHom, ?_, ?_⟩
  · have hf : Function.Injective f.toLinearMap := IsFractionRing.injective U L
    have hg : Function.Injective g.toLinearMap := IsFractionRing.injective C K
    have h1 : Function.Injective (LinearMap.lTensor U g.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hg
    have h2 : Function.Injective (LinearMap.rTensor K f.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hf
    have h3 : Function.Injective (TensorProduct.map f.toLinearMap g.toLinearMap) := by
      rw [← LinearMap.rTensor_comp_lTensor]
      exact h2.comp h1
    intro x y hxy
    apply h3
    exact e.symm.injective hxy
  · intro u c
    show e.symm (f u ⊗ₜ g c) = _
    rw [AlgEquiv.symm_apply_eq]
    rfl

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem eq_zero_of_mem_minimalPrimes {R : Type} [CommRing R] [IsReduced R] {y : R}
    (hy : ∀ P ∈ minimalPrimes R, y ∈ P) : y = 0 := by
  have : y ∈ nilradical R := by
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    intro J hJ
    haveI : Ideal.IsPrime J := hJ
    obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := J) bot_le
    exact hpJ (hy p hp)
  rw [nilradical_eq_zero] at this
  simpa using this

theorem isDomain_of_isIntegrallyClosed_of_isReduced :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R],
      IsIntegrallyClosed R → IsDomain R := by
  intro R _ _ _ _ hic
  classical
  suffices hbot : (⊥ : Ideal R).IsPrime by
    haveI : NoZeroDivisors R := ⟨fun {x y} h => by
      have : x * y ∈ (⊥ : Ideal R) := by simp [h]
      simpa using hbot.mem_or_mem this⟩
    exact NoZeroDivisors.to_isDomain R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  obtain ⟨P, hP⟩ : ∃ P, P ∈ minimalPrimes R := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
      (J := IsLocalRing.maximalIdeal R) bot_le
    exact ⟨p, hp⟩
  have hPprime : P.IsPrime := hP.1.1
  have minle : ∀ {A B : Ideal R}, A ∈ minimalPrimes R → B ∈ minimalPrimes R → A ≤ B → A = B :=
    fun {A B} hA hB hAB => le_antisymm hAB (hB.2 hA.1 hAB)
  set T : Finset (Ideal R) := hfin.toFinset with hT
  have memT : ∀ Q, Q ∈ T ↔ Q ∈ minimalPrimes R := fun Q => by simp [T]
  set Q : Ideal R := (T.erase P).inf id with hQ
  have hQle : ∀ P' ∈ T.erase P, Q ≤ P' := fun P' h => Finset.inf_le (f := id) h
  by_cases hone : T.erase P = ∅
  ·
    have hPbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
        by_cases h : P' = P
        · exact h ▸ hy
        · have : P' ∈ T.erase P := Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩
          simp [hone] at this)
      simp [this]
    exact hPbot ▸ hPprime
  exfalso
  obtain ⟨P₂, hP₂⟩ := Finset.nonempty_iff_ne_empty.2 hone

  have hnot : ¬ ((P ⊔ Q : Ideal R) : Set R) ⊆ ⋃ i ∈ (↑T : Set (Ideal R)), (i : Set R) := by
    intro hsub
    obtain ⟨P', hP'T, hle⟩ := (Ideal.subset_union_prime (f := id) P P
      (fun i hi _ _ => ((memT i).1 hi).1.1)).1 hsub
    have hle' : P ⊔ Q ≤ P' := hle
    have h1 : P = P' := minle hP ((memT P').1 hP'T) (le_sup_left.trans hle')
    have hQP : Q ≤ P := by
      have h2 : Q ≤ P' := le_sup_right.trans hle'
      rw [← h1] at h2
      exact h2
    obtain ⟨P'', hP''e, hP''le⟩ := (Ideal.IsPrime.inf_le' (s := T.erase P) (f := id) hPprime).1 hQP
    have : P'' = P := minle ((memT P'').1 (Finset.mem_of_mem_erase hP''e)) hP hP''le
    exact Finset.ne_of_mem_erase hP''e this
  obtain ⟨s, hsPQ, hsout⟩ := Set.not_subset.1 hnot
  have hsnot : ∀ P' ∈ minimalPrimes R, s ∉ P' := fun P' hP' hs =>
    hsout (Set.mem_biUnion (x := P') (by simpa [memT] using hP') hs)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsPQ
  have hsnzd : ∀ y : R, y * s = 0 → y = 0 := fun y hy =>
    eq_zero_of_mem_minimalPrimes (fun P' hP' => by
      have : y * s ∈ P' := by simp [hy]
      exact (hP'.1.1.mem_or_mem this).resolve_right (hsnot P' hP'))
  have hab0 : a * b = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
    by_cases h : P' = P
    · exact h ▸ P.mul_mem_right b ha
    · exact P'.mul_mem_left a (hQle P' (Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩) hb))
  have hs : s ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_right.2 hsnzd
  let K := FractionRing R
  set e : K := IsLocalization.mk' K a ⟨s, hs⟩ with he_def
  have hspec : e * algebraMap R K s = algebraMap R K a := IsLocalization.mk'_spec K a ⟨s, hs⟩
  have ht : IsUnit (algebraMap R K s) := IsLocalization.map_units K (⟨s, hs⟩ : nonZeroDivisors R)
  have has : a * s = a * a := by rw [← hab, mul_add, hab0, add_zero]
  have hee : e * e = e := by
    refine (ht.mul ht).mul_left_inj.1 ?_
    calc e * e * (algebraMap R K s * algebraMap R K s)
        = (e * algebraMap R K s) * (e * algebraMap R K s) := by ring
      _ = algebraMap R K (a * a) := by rw [hspec, map_mul]
      _ = algebraMap R K (a * s) := by rw [has]
      _ = (e * algebraMap R K s) * algebraMap R K s := by rw [hspec, map_mul]
      _ = e * (algebraMap R K s * algebraMap R K s) := by ring
  have hint : IsIntegral R e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
    · simp [Polynomial.eval₂_sub, sq, hee]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj := IsFractionRing.injective R K
  have hrr : r * r = r := hinj (by rw [map_mul, hr, hee])
  have hrs : r * s = a := hinj (by rw [map_mul, hr, hspec])
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hu | hu
  · have hr1 : r = 1 := hu.mul_left_cancel (by rw [hrr, mul_one])
    rw [hr1, one_mul] at hrs

    exact hsnot P hP (hrs ▸ ha)
  · have hr0 : r = 0 := by
      have : (1 - r) * r = 0 := by rw [sub_mul, one_mul, hrr, sub_self]
      exact (hu.mul_right_eq_zero).1 this
    rw [hr0, zero_mul] at hrs

    have hsb : s = b := by rw [← hab, ← hrs, zero_add]
    exact hsnot P₂ ((memT P₂).1 (Finset.mem_of_mem_erase hP₂)) (hsb ▸ hQle P₂ hP₂ hb)

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.NormalDescent

open Polynomial TensorProduct

variable {A B : Type} [CommRing A] [CommRing B]

def charK (φ : A →+* B) (hφ : φ.Finite) (K : Type) [Field K] [Algebra A K] (b : B) : K[X] :=
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly

def normCoeff [IsDomain A] (φ : A →+* B) (hφ : φ.Finite) (b : B) (k : ℕ) : A :=
  letI := Classical.propDecidable
  if h : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k then
    h.choose else 0

theorem algebraMap_normCoeff [IsDomain A] (φ : A →+* B) (hφ : φ.Finite) (b : B) (k : ℕ)
    (h : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k) :
    algebraMap A (FractionRing A) (normCoeff φ hφ b k) = (charK φ hφ (FractionRing A) b).reverse.coeff k := by
  classical
  unfold normCoeff
  rw [dite_eq_left h]
  exact h.choose_spec

theorem charK_monic (φ : A →+* B) (hφ : φ.Finite) (K : Type) [Field K] [Algebra A K] (b : B) :
    (charK φ hφ K b).Monic := by
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  exact LinearMap.charpoly_monic _

end GlobalTheory.NormalDescent
end
end
