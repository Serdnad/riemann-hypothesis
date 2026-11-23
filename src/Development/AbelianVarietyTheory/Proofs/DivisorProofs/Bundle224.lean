module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle038
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveAnnihilator
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle045
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Mathlib.RingTheory.DedekindDomain.Dvr
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite : ∀ (E : Type) [Field E] [NumberField E] (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)),
    (∀ᶠ w in Filter.cofinite, β w ≤ 1) → ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) → IsIntegral ℤ ((D : E) * x) := by
  first | exact @GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | exact GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | (intros; apply GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_inverseDifferent_max_valuation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ e : E, e ≠ 0 ∧ (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧ ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) → w.valuation E f ≤ w.valuation E e := by
  first | exact @GlobalTheory.invDifferent_exists_max_valuation | exact GlobalTheory.invDifferent_exists_max_valuation | (intros; apply GlobalTheory.invDifferent_exists_max_valuation <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.IntegralDenom

theorem exists_denom_not_mem : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  intro E _ _ w a ha
  exact GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem w a ha

end GlobalTheory.IntegralDenom
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocIntPrincipal

variable (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ)

abbrev locS : Submonoid (𝓞 L) := Algebra.algebraMapSubmonoid (𝓞 L) v.asIdeal.primeCompl

theorem locS_le : locS L v ≤ nonZeroDivisors (𝓞 L) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors

abbrev locR : Subalgebra (𝓞 L) L := Localization.subalgebra.ofField L (locS L v) (locS_le L v)

instance : IsDedekindDomain (locR L v) :=
  IsLocalization.isDedekindDomain (𝓞 L) (locS_le L v) _

instance : IsPrincipalIdealRing (locR L v) :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 L) v.asIdeal v.ne_bot

theorem intCast_ne_zero {s : ℤ} (hs : s ∉ v.asIdeal) : (s : L) ≠ 0 := by
  intro h
  apply hs
  rw [show s = 0 by exact_mod_cast h]
  exact zero_mem _

theorem mem_locR_iff (c : L) :
    c ∈ locR L v ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c) := by
  constructor
  · rintro ⟨a, _, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    have h0 := intCast_ne_zero L v ht
    have e : algebraMap (𝓞 L) L (algebraMap ℤ (𝓞 L) t) = (t : L) := by simp
    rw [e, mul_comm, mul_assoc, inv_mul_cancel₀ h0, mul_one]
    exact RingOfIntegers.isIntegral_coe a
  · rintro ⟨s, hs, hi⟩
    have h0 := intCast_ne_zero L v hs
    refine ⟨⟨(s : L) * c, hi⟩, algebraMap ℤ (𝓞 L) s, ⟨s, hs, rfl⟩, ?_⟩
    have e : algebraMap (𝓞 L) L (algebraMap ℤ (𝓞 L) s) = (s : L) := by simp
    rw [e]
    change c = (s : L) * c * (s : L)⁻¹
    field_simp

end GlobalTheory.LocIntPrincipal


open GlobalTheory.LocIntPrincipal in
theorem GlobalTheory.LocIntPrincipal.exists_generator : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ) (K : Set L), 0 ∈ K →
    (∀ a ∈ K, ∀ b ∈ K, a + b ∈ K) →
    (∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K) →
    (∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a)) →
    ∃ g ∈ K, ∀ a ∈ K, ∃ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) ∧ a = c * g := by
  intro L _ _ v K h0 hadd hmul hint
  let J : Ideal (locR L v) :=
    { carrier := {a | (a : L) ∈ K}
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => hadd _ ha _ hb
      smul_mem' := fun c a ha => by
        change (c : L) * (a : L) ∈ K
        exact hmul _ ((mem_locR_iff L v c).1 c.2) _ ha }
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal J).principal
  have hgJ : g ∈ J := by rw [hg]; exact Submodule.mem_span_singleton_self g
  refine ⟨g, hgJ, fun a ha => ?_⟩
  have haR : a ∈ locR L v := (mem_locR_iff L v a).2 (hint a ha)
  have hJ : (⟨a, haR⟩ : locR L v) ∈ J := ha
  rw [hg, Submodule.mem_span_singleton] at hJ
  obtain ⟨c, hc⟩ := hJ
  refine ⟨c, (mem_locR_iff L v c).1 c.2, ?_⟩
  have := congrArg Subtype.val hc
  exact this.symm
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_primitive_annihilator' : ∀ (F : Type) [Field F] [NumberField F] (W Ω : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (f : W →+* Ω), Function.Injective f → ∀ (n : ℕ) (M : 𝓞 F →+* Matrix (Fin n) (Fin n) W) (σ : 𝓞 F →+* Ω), (∀ c : Fin n → Ω, (∀ a, ((M a).map f).mulVec c = σ a • c) → c = 0) → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)), ∃ w : ι → W, (∃ i, IsUnit (w i)) ∧ ∑ i, w i • M (b i) = 0 := by
  first | exact @GlobalTheory.PrimAnnih.exists_primitive_annihilator | exact GlobalTheory.PrimAnnih.exists_primitive_annihilator | (intros; apply GlobalTheory.PrimAnnih.exists_primitive_annihilator <;> assumption)
end

section

open scoped NumberField

namespace GlobalTheory.TorsQuotCount

variable {K : Type} [Field K] [NumberField K] {M : Type} [AddCommGroup M] [Module (𝓞 K) M]

theorem flat_of_free [Module.Free ℤ M] : Module.Flat (𝓞 K) M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : a • x = 0 := hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hI : Ideal.span {a} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using ha0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hN : Ideal.absNorm (Ideal.span {a}) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hI
  have h2 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) • x = 0 := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← ht, mul_smul, hx', smul_zero]
  exact (Submodule.mem_bot _).2 ((smul_eq_zero.1 h2).resolve_left (by exact_mod_cast hN))

theorem finrank_eq [Module.Free ℤ M] [Module.Finite ℤ M] (r : ℕ)
    (hr : Module.finrank ℤ M = r * Module.finrank ℚ K) : Module.finrank (𝓞 K) M = r := by
  haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M
  haveI : Module.Flat (𝓞 K) M := flat_of_free
  have h20 : (2 : 𝓞 K) ≠ 0 := two_ne_zero
  have hI : Ideal.span {(2 : 𝓞 K)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using h20
  haveI : Finite (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have e1 := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(2 : 𝓞 K)})
  haveI : Finite (ℤ ⧸ Ideal.span {((2 : ℕ) : ℤ)}) :=
    Nat.finite_of_card_ne_zero (by rw [Int.card_ideal_quot]; norm_num)
  have e2 := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := ℤ) (N := M) (Ideal.span {((2 : ℕ) : ℤ)})
  rw [Int.card_ideal_quot] at e2
  have hq : Nat.card (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) = 2 ^ Module.finrank ℚ K := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
    have h2 : (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 := by simp
    rw [h2, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    rfl
  have hPQ : (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M).restrictScalars ℤ =
      (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, by simp [two_smul]⟩
  have hsame : Nat.card (M ⧸ (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)) =
      Nat.card (M ⧸ (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M)) := by
    rw [← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ
      (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)).toEquiv, hPQ]
  rw [hsame, e2, hq, hr, ← pow_mul] at e1
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h3 := Nat.pow_right_injective (le_refl 2) e1
  have h4 : Module.finrank ℚ K * r = Module.finrank ℚ K * Module.finrank (𝓞 K) M := by
    rw [mul_comm] at h3; exact h3
  exact (Nat.eq_of_mul_eq_mul_left hn h4).symm

theorem card_killed_eq : ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M],
    Module.Free ℤ M → Module.Finite ℤ M → ∀ (r : ℕ), Module.finrank ℤ M = r * Module.finrank ℚ K →
    ∀ (𝔟 : Ideal (𝓞 K)) (c : ℕ), 0 < c → (c : 𝓞 K) ∈ 𝔟 →
    Nat.card {x : M ⧸ (Ideal.span {(c : 𝓞 K)} • (⊤ : Submodule (𝓞 K) M)) // ∀ a ∈ 𝔟, a • x = 0} =
      Ideal.absNorm 𝔟 ^ r := by
  intro K _ _ M _ _ hfree hfin r hr 𝔟 c hc hcb
  haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M
  haveI : Module.Flat (𝓞 K) M := flat_of_free
  have hd := finrank_eq (K := K) (M := M) r hr
  have hc0 : (c : 𝓞 K) ≠ 0 := by exact_mod_cast hc.ne'
  have hspan : Ideal.span {(c : 𝓞 K)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hc0
  have hb : 𝔟 ≠ ⊥ := fun h => hc0 (by rw [h] at hcb; exact (Submodule.mem_bot _).1 hcb)
  haveI : Finite (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hspan
  haveI : Finite (𝓞 K ⧸ 𝔟) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  have hX := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(c : 𝓞 K)})
  have hNc : Nat.card (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) ≠ 0 := Nat.card_pos.ne'
  set P : Submodule (𝓞 K) M := Ideal.span {(c : 𝓞 K)} • ⊤ with hP
  haveI : Finite (M ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hX]; exact pow_ne_zero _ hNc)
  obtain ⟨b, hbsup⟩ := IsDedekindDomain.exists_sup_span_eq ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb) hspan
  have hcX : ∀ x : M ⧸ P, (c : 𝓞 K) • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  let f : (M ⧸ P) →ₗ[𝓞 K] (M ⧸ P) := b • LinearMap.id
  have hf : ∀ x, f x = b • x := fun x => rfl
  have hmem : ∀ a ∈ 𝔟, ∃ u v : 𝓞 K, a = u * c + v * b := by
    intro a ha
    rw [← hbsup, Submodule.mem_sup] at ha
    obtain ⟨y, hy, z, hz, rfl⟩ := ha
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨u, v, rfl⟩
  have hbmem : b ∈ 𝔟 := hbsup ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  have e1 : {x : M ⧸ P // ∀ a ∈ 𝔟, a • x = 0} ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.1, by rw [LinearMap.mem_ker, hf]; exact x.2 b hbmem⟩
      invFun := fun x => ⟨x.1, fun a ha => by
        obtain ⟨u, v, rfl⟩ := hmem a ha
        have hx : b • (x.1 : M ⧸ P) = 0 := by rw [← hf]; exact x.2
        rw [add_smul, mul_smul, mul_smul, hcX, hx, smul_zero, smul_zero, add_zero]⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 : Nat.card ((M ⧸ P) ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have hker : Nat.card (LinearMap.ker f) = Nat.card ((M ⧸ P) ⧸ LinearMap.range f) := by
    rw [h3] at h1
    have h4 := h1.symm.trans h2
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm]; exact h4)
  have hPle : P ≤ 𝔟 • ⊤ := Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb)
  have hrange : LinearMap.range f = Submodule.map P.mkQ (𝔟 • ⊤) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H m => exact ⟨b • m, Submodule.smul_mem_smul hbmem trivial, by simp [hf]⟩
    · rintro _ ⟨m, hm, rfl⟩
      refine Submodule.smul_induction_on (p := fun m => P.mkQ m ∈ LinearMap.range f) hm ?_ ?_
      · intro a ha n _
        obtain ⟨u, v, rfl⟩ := hmem a ha
        refine ⟨v • P.mkQ n, ?_⟩
        rw [hf, map_smul, add_smul, mul_smul, mul_smul, hcX, smul_zero, zero_add]
        exact smul_comm _ _ _
      · intro x y hx hy
        rw [map_add (f := _)]
        exact add_mem hx hy
  have hQ : Nat.card ((M ⧸ P) ⧸ LinearMap.range f) = Nat.card (M ⧸ (𝔟 • ⊤ : Submodule (𝓞 K) M)) := by
    rw [hrange]
    exact Nat.card_congr (Submodule.quotientQuotientEquivQuotient P (𝔟 • ⊤) hPle).toEquiv
  have hM := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) 𝔟
  rw [Nat.card_congr e1, hker, hQ, hM, hd, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]

end GlobalTheory.TorsQuotCount
end

section

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory

theorem card_le_absNorm_of_forall_le : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ →
    ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by
  intro F _ _ I hI s hs
  classical
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  have hgen : ∀ J : Ideal (𝓞 F), ∃ a : 𝓞 F, I ≤ J → I ⊔ Ideal.span {a} = J := by
    intro J
    by_cases h : I ≤ J
    · obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq h hI
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose g hg using hgen
  have hle : ∀ J K : Ideal (𝓞 F), I ≤ J → I ≤ K →
      Ideal.Quotient.mk I (g J) = Ideal.Quotient.mk I (g K) → J ≤ K := by
    intro J K hJ hK heq
    rw [← hg J hJ]
    refine sup_le hK ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have hd : g J - g K ∈ I := Ideal.Quotient.eq.mp heq
    have hk : g K ∈ K := by
      have h0 : g K ∈ I ⊔ Ideal.span {g K} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      rwa [hg K hK] at h0
    have : g J = (g J - g K) + g K := by ring
    rw [this]
    exact K.add_mem (hK hd) hk
  have hinj : Set.InjOn (fun J => Ideal.Quotient.mk I (g J)) (s : Set (Ideal (𝓞 F))) := by
    intro J hJ K hK heq
    exact le_antisymm (hle J K (hs J hJ) (hs K hK) heq) (hle K J (hs K hK) (hs J hJ) heq.symm)
  have h1 : s.card ≤ (Finset.univ : Finset (𝓞 F ⧸ I)).card :=
    Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at h1
  exact h1

end GlobalTheory
end

section

open NumberField

theorem _root_.GlobalTheory.T.natCard_quot_smul_le_pow_finrank : ∀ (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La], Module.Finite (𝓞 E) La → Module.Projective (𝓞 E) La → ∀ (I : Ideal (𝓞 E)) (g : ℕ), g.Prime → Ideal.absNorm I = g → Finite (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ∧ Nat.card (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ≤ g ^ Module.finrank (𝓞 E) La := by
  first | exact @GlobalTheory.natCard_quot_smul_top_le_pow_finrank | exact GlobalTheory.natCard_quot_smul_top_le_pow_finrank | (intros; apply GlobalTheory.natCard_quot_smul_top_le_pow_finrank <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.absNorm_map_ringOfIntegers_hom' : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (𝔞 : Ideal (𝓞 E)), Module.finrank ℚ E ∣ Module.finrank ℚ K ∧ Ideal.absNorm (𝔞.map τ) = Ideal.absNorm 𝔞 ^ (Module.finrank ℚ K / Module.finrank ℚ E) := by
  first | exact @GlobalTheory.absNorm_map_ringOfIntegers_hom | exact GlobalTheory.absNorm_map_ringOfIntegers_hom | (intros; apply GlobalTheory.absNorm_map_ringOfIntegers_hom <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.primaryTorsion_divisible_and_torsion_eq_ideal_torsion : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (g : ℕ) (I : Ideal (𝓞 E)), g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → (∀ x : M, ∃ y : M, g • y = x) → (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → ∃ y : M, g • y = x ∧ ∀ a ∈ I ^ (j + 1), a • y = 0) ∧ (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → g • x = 0 → ∀ a ∈ I, a • x = 0) := by
  first | exact @GlobalTheory.primaryTorsion_divisible_and_gTorsion | exact GlobalTheory.primaryTorsion_divisible_and_gTorsion | (intros; apply GlobalTheory.primaryTorsion_divisible_and_gTorsion <;> assumption)
end

section

open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory.PrimeSquareSum

theorem sum_inv_sq_le_one (t : Finset ℕ) (ht : ∀ n ∈ t, 2 ≤ n) :
    ∑ n ∈ t, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
  have hs := hasSum_zeta_two
  have h1 : (1 : ℕ) ∉ t := fun h => by
    have := ht 1 h
    omega
  have hsum : ∑ n ∈ insert 1 t, ((n : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    rw [← hs.tsum_eq]
    have e : (fun n : ℕ => 1 / (n : ℝ) ^ 2) = fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
      funext n
      rw [one_div]
    rw [e]
    exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (e ▸ hs.summable)
  rw [Finset.sum_insert h1] at hsum
  norm_num at hsum
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  linarith

theorem sum_absNorm_inv_sq_le (K : Type) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ w ∈ s, (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.exists_colouring_maximal_ideals K
  have hp : ∀ w : HeightOneSpectrum (𝓞 K), ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal ∧
      p ≤ Ideal.absNorm w.asIdeal := by
    intro w
    haveI := w.isMaximal
    obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
    exact ⟨q, hq, hqP, H ▸ Nat.le_self_pow hn.ne' q⟩
  choose p hp hpm hple using hp
  rw [← Finset.sum_fiberwise s (fun w => c w.asIdeal)]
  calc _ ≤ ∑ _i : Fin (Module.finrank ℚ K), (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hinj : Set.InjOn p (s.filter fun w => c w.asIdeal = i) := by
          intro v hv w hw h
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw
          exact HeightOneSpectrum.ext (hc (p v) (hp v) _ _ v.isMaximal w.isMaximal (hpm v)
            (h ▸ hpm w) (hv.2.trans hw.2.symm))
        calc _ ≤ ∑ w ∈ s.filter (fun w => c w.asIdeal = i), ((p w : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum fun w _ => ?_
              have h0 : (0 : ℝ) < p w := by exact_mod_cast (hp w).pos
              have h1 : (p w : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℕ) := by exact_mod_cast hple w
              gcongr
          _ = ∑ n ∈ (s.filter (fun w => c w.asIdeal = i)).image p, ((n : ℝ) ^ 2)⁻¹ :=
              (Finset.sum_image (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) hinj).symm
          _ ≤ 1 := by
              refine sum_inv_sq_le_one _ fun n hn => ?_
              obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hn
              exact (hp w).two_le
    _ = _ := by simp

theorem summable_absNorm_inv_sq : ∀ (K : Type) [Field K] [NumberField K], Summable (fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹) ∧ ∑' w : HeightOneSpectrum (𝓞 K), (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  intro K _ _
  have hnn : 0 ≤ fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ :=
    fun w => by positivity
  exact ⟨summable_of_sum_le hnn (sum_absNorm_inv_sq_le K),
    tsum_le_of_sum_le' (by positivity) (sum_absNorm_inv_sq_le K)⟩

end GlobalTheory.PrimeSquareSum
end

section

open NumberField

theorem _root_.GlobalTheory.T.prod_arg_real_unit_eq_one' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime → 2 < q →
    ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    (∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E)) →
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.prod_arg_real_unit_eq_one | exact GlobalTheory.prod_arg_real_unit_eq_one | (intros; apply GlobalTheory.prod_arg_real_unit_eq_one <;> assumption)
end
