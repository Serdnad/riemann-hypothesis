module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Basic.Real.Basic
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
public import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

theorem algebraicIndependent_one_tmul_of_field {k K L ι : Type} [Field k] [Field K] [CommRing L] [Algebra k K] [Algebra k L]
    {t : ι → L} (ht : AlgebraicIndependent k t) :
    AlgebraicIndependent K (fun i => (1 : K) ⊗ₜ[k] t i) := by
  rw [algebraicIndependent_iff_injective_aeval] at ht ⊢
  have h1 : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L).toLinearMap ht
  have h2 : (MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[k] t i) : MvPolynomial ι K →ₐ[K] K ⊗[k] L) =
      (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L)).comp
        (MvPolynomial.algebraTensorAlgEquiv k K (σ := ι)).symm.toAlgHom := by
    ext i
    simp
  rw [h2]
  exact h1.comp (MvPolynomial.algebraTensorAlgEquiv k K (σ := ι)).symm.injective

theorem trdeg_tensorProduct_eq {k K L : Type} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [IsDomain (K ⊗[k] L)] : Algebra.trdeg K (K ⊗[k] L) = Algebra.trdeg k L := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  have hi := algebraicIndependent_one_tmul_of_field (K := K) hs.1
  set S := Algebra.adjoin K (Set.range fun i : s => (1 : K) ⊗ₜ[k] (i : L)) with hS
  have halg : Algebra.IsAlgebraic S (K ⊗[k] L) := by
    have hA := hs.isAlgebraic
    set T := Algebra.adjoin k (Set.range (Subtype.val : s → L)) with hT
    have hmem : ∀ x : T, (1 : K) ⊗ₜ[k] (x : L) ∈ S := by
      rintro ⟨x, hx⟩
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Algebra.subset_adjoin ⟨i, rfl⟩
      | algebraMap r =>
        have : (1 : K) ⊗ₜ[k] (algebraMap k L r) = algebraMap K (K ⊗[k] L) (algebraMap k K r) := by
          rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply k K (K ⊗[k] L)]
        simp only [this]
        exact S.algebraMap_mem _
      | add x y hx hy ihx ihy =>
        simp only [TensorProduct.tmul_add]
        exact S.add_mem ihx ihy
      | mul x y hx hy ihx ihy =>
        have : (1 : K) ⊗ₜ[k] (x * y) = ((1 : K) ⊗ₜ[k] x) * ((1 : K) ⊗ₜ[k] y) := by simp
        simp only [this]
        exact S.mul_mem ihx ihy
    let g : L →+* K ⊗[k] L := (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := L)).toRingHom
    let f : T →+* S := (g.comp T.val.toRingHom).codRestrict S hmem
    have hf : Function.Injective f := by
      intro x y hxy
      have : g x = g y := congrArg Subtype.val hxy
      exact Subtype.ext (g.injective this)
    refine ⟨fun z => ?_⟩
    induction z using TensorProduct.induction_on with
    | zero => exact isAlgebraic_zero
    | add x y hx hy => exact hx.add hy
    | tmul a b =>
      have h1 : IsAlgebraic S (g b) :=
        (hA.isAlgebraic b).ringHom_of_comp_eq f g hf (by ext; rfl)
      have h2 : IsAlgebraic S (algebraMap S (K ⊗[k] L) (algebraMap K S a)) := isAlgebraic_algebraMap _
      have h3 : a ⊗ₜ[k] b = algebraMap S (K ⊗[k] L) (algebraMap K S a) * g b := by
        simp [g]
      rw [h3]
      exact h2.mul h1
  have hb : IsTranscendenceBasis K (fun i : s => (1 : K) ⊗ₜ[k] (i : L)) :=
    hi.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  rw [← hb.cardinalMk_eq_trdeg, ← hs.cardinalMk_eq_trdeg]

theorem trdeg_complex_baseChange_eq : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] [IsDomain (K ⊗[ℂ] κ')], Algebra.trdeg K (K ⊗[ℂ] κ') = Algebra.trdeg ℂ κ' :=
  trdeg_tensorProduct_eq

end GlobalTheory
end

section

open scoped LaurentSeries

namespace GlobalTheory.PowerSeriesNoPole

open scoped LaurentSeries in
open PowerSeries in
private lemma C_dvd_iff_map_mk_eq_zero {A : Type} [CommRing A] (ϖ : A) (f : PowerSeries A) :
    C ϖ ∣ f ↔ PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    ext d
    simp [coeff_C_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · intro h
    have hd : ∀ d, ϖ ∣ coeff d f := fun d ↦ by
      have := congrArg (coeff d) h
      simpa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
    choose q hq using hd
    refine ⟨mk q, ?_⟩
    ext d
    simp [coeff_C_mul, hq d]

open scoped LaurentSeries in
open PowerSeries in
private lemma prime_C_powerSeries {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (hϖ : Prime ϖ) :
    Prime (C ϖ : PowerSeries A) := by
  haveI : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ
  refine ⟨fun h ↦ hϖ.ne_zero (by simpa using congrArg (coeff 0) h), fun hu ↦ hϖ.not_unit ?_,
    fun f g h ↦ ?_⟩
  · simpa using hu.map (constantCoeff (R := A))
  · rw [C_dvd_iff_map_mk_eq_zero, C_dvd_iff_map_mk_eq_zero]
    rw [C_dvd_iff_map_mk_eq_zero, map_mul] at h
    exact mul_eq_zero.mp h


open scoped LaurentSeries in
open PowerSeries in
theorem _root_.GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap (A : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : Irreducible ϖ) (k : A →+* ℂ) (hk : Function.Injective k)
    (S : Type) [CommRing S] [Algebra (PowerSeries A) S]
    [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S]
    (ι : S →+* ℂ⸨X⸩)
    (hι : ∀ s : PowerSeries A,
      ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s))
    (v : S) (hv : ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range)
    (hst : ∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧
      v * algebraMap _ S t = algebraMap _ S s) :
    ∃ s : PowerSeries A, v = algebraMap _ S s := by
  obtain ⟨s, t, ht, hvt⟩ := hst
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (C ϖ * X : PowerSeries A) v
  rw [← map_pow] at ha
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hu0 : (C ϖ * X : PowerSeries A) ≠ 0 :=
    mul_ne_zero (fun h ↦ hϖ0 (by simpa using congrArg (coeff 0) h)) X_ne_zero
  have hinj : Function.Injective (algebraMap (PowerSeries A) S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hu0)
  have hat : a * t = s * (C ϖ * X) ^ n := by
    apply hinj
    rw [map_mul, map_mul, ← ha, ← hvt]
    ring
  obtain ⟨g, hg⟩ := hv
  have hga : g * PowerSeries.map k ((C ϖ * X) ^ n) = PowerSeries.map k a := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_mul, hg, ← hι, ← hι, ← map_mul, ha]
  have hXa : (X : PowerSeries A) ^ n ∣ a := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    apply hk
    rw [map_zero, ← PowerSeries.coeff_map, ← hga]
    have hdvd : (X : PowerSeries ℂ) ^ n ∣ g * PowerSeries.map k ((C ϖ * X) ^ n) :=
      ⟨g * C (k ϖ) ^ n, by rw [map_pow, map_mul, map_C, map_X, mul_pow]; ring⟩
    exact (PowerSeries.X_pow_dvd_iff.mp hdvd) d hd
  obtain ⟨a₁, rfl⟩ := hXa
  have ha₁ : a₁ * t = (C ϖ) ^ n * s := by
    have hX : (X : PowerSeries A) ^ n ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [mul_pow] at hat
    linear_combination hat
  have hp : Prime (C ϖ : PowerSeries A) := prime_C_powerSeries hϖ.prime
  obtain ⟨a₂, rfl⟩ := hp.pow_dvd_of_dvd_mul_right n ht ⟨s, ha₁⟩
  refine ⟨a₂, ?_⟩
  have hunit : IsUnit (algebraMap (PowerSeries A) S ((C ϖ * X) ^ n)) :=
    IsLocalization.map_units S (⟨(C ϖ * X) ^ n, n, rfl⟩ : Submonoid.powers (C ϖ * X))
  apply hunit.mul_left_inj.mp
  rw [ha, ← map_mul]
  congr 1
  ring

end GlobalTheory.PowerSeriesNoPole
end

section

namespace GlobalTheory

open Filter Topology

theorem locallyConstant_compactSupport_invariant_openAddSubgroup :
    ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
      [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g →
      ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by
  intro X _ _ _ _ g hg hc
  have key : ∀ z : X, ∃ V : OpenAddSubgroup X, ∀ h ∈ V, g (z + h) = g z := by
    intro z
    have hT : Tendsto (fun h : X => z + h) (𝓝 0) (𝓝 z) := by
      have := (continuous_const_add z).tendsto (0 : X)
      simpa using this
    have hn : {h : X | g (z + h) = g z} ∈ 𝓝 (0 : X) := hT.eventually (hg.eventually_eq z)
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hn
    exact ⟨V, fun h hh => hV hh⟩
  choose H hH using key
  have hU : ∀ j y, y - j ∈ H j → g y = g j := by
    intro j y h
    have := hH j (y - j) h
    have e : j + (y - j) = y := by abel
    rwa [e] at this
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun z : X => {y : X | y - z ∈ H z})
    (fun z => (H z).isOpen.preimage (continuous_id.sub continuous_const))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine ⟨t.inf H, fun z a ha => ?_⟩
  have hle : ∀ j ∈ t, a ∈ H j := fun j hj => Finset.inf_le (f := H) hj ha
  by_cases hz : z ∈ tsupport g
  · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 (ht hz)
    have h1 : z - j ∈ H j := hzj
    have h2 : z + a - j ∈ H j := by
      have := (H j).add_mem h1 (hle j hj)
      have e : z - j + a = z + a - j := by abel
      rwa [e] at this
    rw [hU j _ h2, hU j _ h1]
  by_cases hza : z + a ∈ tsupport g
  · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 (ht hza)
    have h1 : z + a - j ∈ H j := hzj
    have h2 : z - j ∈ H j := by
      have := (H j).sub_mem h1 (hle j hj)
      have e : z + a - j - a = z - j := by abel
      rwa [e] at this
    rw [hU j _ h2, hU j _ h1]
  rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hza]

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem twisted_lift_to_localisation (A B A₂ : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [CommRing A₂] [IsLocalRing A₂] (G : Type) [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] (f : B →+* A₂) :
    IsLocalHom (f.comp (algebraMap A B)) → (∀ y : A₂, ∃ b s : B, IsUnit (f s) ∧ y * f s = f b) →
    (∀ b : B, f b = 0 → ∃ s : B, IsUnit (f s) ∧ s * b = 0) →
    ∀ (V' : Type) [CommRing V'] [IsLocalRing V'] (e₁ : A →+* V') (β : B →+* V'),
      IsLocalHom e₁ → β.comp (algebraMap A B) = e₁ →
      ∃ ev₂ : A₂ →+* V', IsLocalHom ev₂ ∧ ev₂.comp (f.comp (algebraMap A B)) = e₁ := by
  intro hfl hsurj hker V' _ _ e₁ β he₁ hβ
  set q : Ideal B := (maximalIdeal A₂).comap f with hq
  set c : Ideal B := (maximalIdeal V').comap β with hc
  haveI : q.IsPrime := Ideal.comap_isPrime f (maximalIdeal A₂)
  haveI : c.IsPrime := Ideal.comap_isPrime β (maximalIdeal V')
  have hqA : Ideal.under A q = maximalIdeal A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, hq, mem_maximalIdeal, mem_nonunits_iff]
    rw [← RingHom.comp_apply, isUnit_map_iff (f.comp (algebraMap A B))]
  have hcA : Ideal.under A c = maximalIdeal A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, hc, mem_maximalIdeal, mem_nonunits_iff]
    rw [← RingHom.comp_apply, hβ, isUnit_map_iff e₁]
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G c q (hcA.trans hqA.symm)
  set β' : B →+* V' := β.comp (MulSemiringAction.toRingHom G B σ⁻¹) with hβ'
  have hβ'q : ∀ b : B, b ∈ q ↔ ¬ IsUnit (β' b) := by
    intro b
    rw [hσ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hc, Ideal.mem_comap, mem_maximalIdeal,
      mem_nonunits_iff]
    rfl
  have hfq : ∀ b : B, b ∈ q ↔ ¬ IsUnit (f b) := by
    intro b
    rw [hq, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  have hβ'A : β'.comp (algebraMap A B) = e₁ := by
    rw [← hβ]
    ext a
    simp only [hβ', RingHom.comp_apply, MulSemiringAction.toRingHom_apply, smul_algebraMap]
  letI : Algebra B A₂ := f.toAlgebra
  haveI hloc : IsLocalization q.primeCompl A₂ := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs⟩
      have : s ∉ q := hs
      rw [hfq, not_not] at this
      exact this
    · intro z
      obtain ⟨b, s, hs, h⟩ := hsurj z
      have hs' : s ∈ q.primeCompl := by
        show s ∉ q
        rw [hfq, not_not]; exact hs
      exact ⟨(b, ⟨s, hs'⟩), h⟩
    · intro x y hxy
      have h0 : f (x - y) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr hxy
      obtain ⟨s, hs, h⟩ := hker _ h0
      have hs' : s ∈ q.primeCompl := by
        show s ∉ q
        rw [hfq, not_not]; exact hs
      refine ⟨⟨s, hs'⟩, ?_⟩
      show s * x = s * y
      rw [mul_sub] at h
      exact sub_eq_zero.mp h
  have hunits : ∀ y : q.primeCompl, IsUnit (β' y) := by
    rintro ⟨s, hs⟩
    have : s ∉ q := hs
    rw [hβ'q, not_not] at this
    exact this
  have hcomp : (IsLocalization.lift hunits).comp f = β' :=
    IsLocalization.lift_comp (M := q.primeCompl) (S := A₂) hunits
  refine ⟨IsLocalization.lift hunits, ?_, ?_⟩
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨b, s, hs, h⟩ := hsurj x
    have hsq : IsUnit (β' s) := by
      have : s ∉ q := by rw [hfq, not_not]; exact hs
      rw [hβ'q, not_not] at this
      exact this
    have hb : IsUnit (β' b) := by
      have h2 := congrArg (IsLocalization.lift hunits) h
      rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hcomp] at h2
      rw [← h2]
      exact hx.mul hsq
    have hfb : IsUnit (f b) := by
      have : b ∉ q := by rw [hβ'q, not_not]; exact hb
      rw [hfq, not_not] at this
      exact this
    rw [← h] at hfb
    exact isUnit_of_mul_isUnit_left hfb
  · rw [← RingHom.comp_assoc, hcomp, hβ'A]

end GlobalTheory
end

section

namespace GlobalTheory.InjectiveOfIntegral

theorem exists_injective_of_isIntegral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal)
    (hv : Valuation.Integers v O) [Algebra A B] [Algebra.IsIntegral A B]
    (hAB : Function.Injective (algebraMap A B)) (j : A →+* O)
    (hj : Function.Injective ((algebraMap O C).comp j)) :
    ∃ j' : B →+* O, Function.Injective ((algebraMap O C).comp j') := by
  classical
  let _ : Algebra A C := ((algebraMap O C).comp j).toAlgebra
  let _ : Algebra A O := j.toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAC : Function.Injective (algebraMap A C) := hj
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hAB
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hAC
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  let ψ : B →ₐ[A] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hker : RingHom.ker (ψ : B →+* C) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot,
      show (ψ : B →+* C) (algebraMap A B a) = algebraMap A C a from ψ.commutes a]
    exact ⟨fun h => hAC (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
  have hψ : Function.Injective (ψ : B →+* C) := (RingHom.injective_iff_ker_eq_bot _).mpr hker
  have hint : ∀ b : B, v (ψ b) ≤ 1 := by
    intro b
    have hb : IsIntegral A (ψ b) := (Algebra.IsIntegral.isIntegral b).map ψ
    exact hv.mem_of_integral hb.tower_top
  choose g hg using fun b => hv.exists_of_le_one (hint b)
  let j' : B →+* O :=
    { toFun := g
      map_one' := hv.hom_inj (by simp only [hg, map_one])
      map_mul' := fun x y => hv.hom_inj (by simp only [hg, map_mul])
      map_zero' := hv.hom_inj (by simp only [hg, map_zero])
      map_add' := fun x y => hv.hom_inj (by simp only [hg, map_add (f := _)]) }
  refine ⟨j', ?_⟩
  have e : (algebraMap O C).comp j' = (ψ : B →+* C) := RingHom.ext hg
  rw [e]
  exact hψ

end GlobalTheory.InjectiveOfIntegral
end

section

namespace GlobalTheory

theorem _root_.GlobalTheory.bar_gap_param_ineq : ∀ (T D c0 h0 N f m k PP : ℝ), 4 * D + 4 ≤ T → 4 * T ^ 2 ≤ h0 → PP * T * N * f ^ 2 * m ^ 2 * k * D ≤ h0 →
    4 * (c0 + 2 * N + T + D + 1) ≤ h0 → 0 ≤ c0 → c0 ≤ 22 * f ^ 2 * N ^ 4 → D = f * (N * (N - 1) / 2) → 40 ≤ PP →
    N + 4 ≤ 2 * k → 2 ≤ m → 6 ≤ N → 8 ≤ f →
    (T + c0) * (T + D + 1) + c0 + 2 * N - 2 ≤ h0 ∧ 2 * N + D ≤ T := by
  intro T D c0 h0 N f m k PP hTD hT2 hP h4 hc0 hc0u hD hPP hk hm hN hf
  have hNN : 5 * N ≤ N * (N - 1) := by nlinarith
  have hD1 : 4 * (N * (N - 1)) ≤ D := by
    rw [hD]; nlinarith [mul_nonneg (sub_nonneg.2 hf) (by nlinarith : (0:ℝ) ≤ N * (N - 1))]
  have hD0 : 0 ≤ D := by nlinarith
  have hgap : 2 * N + D ≤ T := by nlinarith
  refine ⟨?_, hgap⟩
  have hT0 : 0 ≤ T := by linarith
  have hm2 : 4 ≤ m ^ 2 := by nlinarith
  have hk0 : 0 ≤ k := by linarith
  have hA : 160 ≤ PP * m ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hPP) (sq_nonneg m)]
  have hB : 80 * N ≤ PP * m ^ 2 * k := by
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hk0]
  have hC : 320 * (N ^ 2 * (N - 1)) ≤ PP * m ^ 2 * k * D := by
    nlinarith [mul_nonneg (sub_nonneg.2 hB) hD0, mul_nonneg (by linarith : (0:ℝ) ≤ 80 * N) (sub_nonneg.2 hD1)]
  have hE : 264 * N ^ 3 ≤ PP * m ^ 2 * k * D := by
    nlinarith [mul_nonneg (sq_nonneg N) (by linarith : (0:ℝ) ≤ 56 * N - 320)]
  have hX : 0 ≤ T * N * f ^ 2 := by
    have : 0 ≤ N := by linarith
    positivity
  have hF : 264 * N ^ 3 * (T * N * f ^ 2) ≤ PP * T * N * f ^ 2 * m ^ 2 * k * D := by
    have := mul_le_mul_of_nonneg_right hE hX
    calc 264 * N ^ 3 * (T * N * f ^ 2) ≤ PP * m ^ 2 * k * D * (T * N * f ^ 2) := this
      _ = PP * T * N * f ^ 2 * m ^ 2 * k * D := by ring
  have hcT : 12 * (c0 * T) ≤ h0 := by
    have h1 : c0 * T ≤ 22 * f ^ 2 * N ^ 4 * T := mul_le_mul_of_nonneg_right hc0u hT0
    nlinarith
  have hcD : c0 * (4 * (D + 1)) ≤ c0 * T := mul_le_mul_of_nonneg_left (by linarith) hc0
  have hTT : T * (4 * (D + 1)) ≤ T * T := mul_le_mul_of_nonneg_left (by linarith) hT0
  have hexp : (T + c0) * (T + D + 1) + c0 + 2 * N - 2
      = T ^ 2 + T * (D + 1) + c0 * T + c0 * (D + 1) + c0 + 2 * N - 2 := by ring
  rw [hexp]
  nlinarith

end GlobalTheory
end
