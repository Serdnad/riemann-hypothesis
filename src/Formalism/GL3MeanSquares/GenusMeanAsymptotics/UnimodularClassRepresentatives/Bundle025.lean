module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle019
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.EndomorphismScalars

open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

abbrev Qk (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Type :=
  ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)

variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V}

private theorem exists_mul_sub_one_mem_pow_of_not_mem_maximal (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) (k : ℕ) :
    ∃ s : 𝓞 F, s * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨y * ∑ l ∈ Finset.range k, i ^ l, ?_⟩
  have h1 : y * t = 1 - i := by rw [← hyi]; ring
  have h2 : y * (∑ l ∈ Finset.range k, i ^ l) * t - 1 = -(i ^ k) := by
    rw [mul_right_comm, h1, mul_neg_geom_sum]; ring
  rw [h2]
  exact (Submodule.neg_mem_iff _).mpr (Ideal.pow_mem_pow hi k)

private theorem algebraMap_mem_extP_pow_of_mem_pow {k : ℕ} {a : 𝓞 F} (ha : a ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) a ∈ extP K 𝔭 ^ k := by
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

theorem mk_eq_smul (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (x : ↥L) :
    ∃ a : 𝓞 K, (Submodule.Quotient.mk x : Qk L 𝔭 k) = a • Submodule.Quotient.mk ⟨e, he.1⟩ := by
  obtain ⟨t, ht, a, hta⟩ := he.2.2 x x.2
  obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
  refine ⟨algebraMap (𝓞 F) (𝓞 K) s * a, ?_⟩
  have hmem : (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x ∈
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
    Submodule.smul_mem_smul (algebraMap_mem_extP_pow_of_mem_pow hs) Submodule.mem_top
  have hL : (algebraMap (𝓞 F) (𝓞 K) t) • x = a • (⟨e, he.1⟩ : ↥L) :=
    Subtype.ext (by rw [Submodule.coe_smul, Submodule.coe_smul]; exact hta)
  have hx : x = (algebraMap (𝓞 F) (𝓞 K) s * a) • (⟨e, he.1⟩ : ↥L) -
      (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x := by
    rw [map_sub, map_mul, map_one, sub_smul, one_smul, mul_smul, mul_smul, hL]
    abel
  conv_lhs => rw [hx]
  rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).mpr hmem, sub_zero,
    Submodule.Quotient.mk_smul]

theorem smul_top_spec (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) {w : ↥L}
    (hw : w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k, algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e := by
  refine Submodule.smul_induction_on
    (p := fun w : ↥L => ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k,
      algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e) hw ?_ ?_
  · intro r hr n _
    obtain ⟨t, ht, a, hta⟩ := he.2.2 n n.2
    refine ⟨t, ht, r * a, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, smul_comm, hta, smul_smul]
  · rintro x y ⟨t1, ht1, c1, hc1, h1⟩ ⟨t2, ht2, c2, hc2, h2⟩
    refine ⟨t1 * t2, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht1 ht2,
      algebraMap (𝓞 F) (𝓞 K) t2 * c1 + algebraMap (𝓞 F) (𝓞 K) t1 * c2,
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc1) (Ideal.mul_mem_left _ _ hc2), ?_⟩
    have e1 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (x : V) = algebraMap (𝓞 F) (𝓞 K) t2 • (c1 • e) := by
      rw [map_mul, mul_comm (algebraMap (𝓞 F) (𝓞 K) t1), mul_smul, h1]
    have e2 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (y : V) = algebraMap (𝓞 F) (𝓞 K) t1 • (c2 • e) := by
      rw [map_mul, mul_smul, h2]
    rw [Submodule.coe_add, smul_add, e1, e2, add_smul, mul_smul, mul_smul]

theorem smul_gen_mem_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    b • (⟨e, he.1⟩ : ↥L) ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro hb
    obtain ⟨t, ht, c, hc, htc⟩ := smul_top_spec h𝔭 he k hb
    have h1 : (algebraMap (𝓞 F) (𝓞 K) t * b) • e = c • e := by
      rw [Submodule.coe_smul] at htc
      rw [mul_smul]
      exact htc
    have h2 : algebraMap (𝓞 F) (𝓞 K) t * b = c := by
      rw [← algebraMap_smul K _ e, ← algebraMap_smul K c e] at h1
      exact IsFractionRing.injective (𝓞 K) K (smul_left_injective K he.2.1 h1)
    obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
    have hb' : b = algebraMap (𝓞 F) (𝓞 K) s * c -
        algebraMap (𝓞 F) (𝓞 K) (s * t - 1) * b := by
      rw [← h2, map_sub, map_mul, map_one]; ring
    rw [hb']
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hc) (Ideal.mul_mem_right _ _ (algebraMap_mem_extP_pow_of_mem_pow hs))
  · intro hb
    exact Submodule.smul_mem_smul hb Submodule.mem_top

theorem end_surj (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ)
    (X : Module.End (𝓞 K) (Qk L 𝔭 k)) :
    ∃ b : 𝓞 K, algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = X := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (X (Submodule.Quotient.mk ⟨e, he.1⟩))
  obtain ⟨a, ha⟩ := mk_eq_smul h𝔭 he k y
  refine ⟨a, LinearMap.ext fun z => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨ax, hax⟩ := mk_eq_smul h𝔭 he k x
  rw [Module.algebraMap_end_apply, hax, map_smul, ← hy, ha, smul_comm]

theorem end_eq_zero_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = 0 ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro h0
    have := LinearMap.congr_fun h0 (Submodule.Quotient.mk ⟨e, he.1⟩)
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at this
    exact (smul_gen_mem_iff h𝔭 he k b).mp this
  · intro hb
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hb Submodule.mem_top

def endHom (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ k) →+* Module.End (𝓞 K) (Qk L 𝔭 k) :=
  Ideal.Quotient.lift _ (algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)))
    fun b hb => (end_eq_zero_iff h𝔭 he k b).2 hb

theorem endHom_mk (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    endHom h𝔭 he k (Ideal.Quotient.mk _ b) =
      algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b := Ideal.Quotient.lift_mk _ _ _

theorem endHom_bijective (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    Function.Bijective (endHom h𝔭 he k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [endHom_mk, end_eq_zero_iff h𝔭 he k] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  · intro X
    obtain ⟨b, hb⟩ := end_surj h𝔭 he k X
    exact ⟨Ideal.Quotient.mk _ b, by rw [endHom_mk, hb]⟩

end Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def InP (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : K) : Prop :=
  ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z ∈ extP K 𝔭 ^ k, jK z = jK (ι t) * a

theorem congrP_iff_inP (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a b : K) : CongrP 𝔭 k a b ↔ InP 𝔭 k (a - b) := by
  have e : ∀ t : 𝓞 F, jK (ι t) = algebraMap F K (t : F) := fun t => rfl
  simp only [CongrP, InP, e]

theorem jK_inj : Function.Injective (jK) := fun a b hab => RingOfIntegers.ext hab

theorem InP.add {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 k b) : InP 𝔭 k (a + b) := by
  obtain ⟨t₁, ht₁, z₁, hz₁, e₁⟩ := ha
  obtain ⟨t₂, ht₂, z₂, hz₂, e₂⟩ := hb
  refine ⟨t₁ * t₂, fun hm => (h𝔭.mem_or_mem hm).elim ht₁ ht₂, ι t₂ * z₁ + ι t₁ * z₂,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hz₁) (Ideal.mul_mem_left _ _ hz₂), ?_⟩
  simp only [map_add (f := _), map_mul, e₁, e₂]
  ring

theorem InP.neg {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : K} (ha : InP 𝔭 k a) : InP 𝔭 k (-a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  exact ⟨t, ht, -z, neg_mem hz, by rw [map_neg, e, mul_neg]⟩

theorem InP.mul {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k l : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 l b) : InP 𝔭 (k + l) (a * b) := by
  obtain ⟨t₁, ht₁, z₁, hz₁, e₁⟩ := ha
  obtain ⟨t₂, ht₂, z₂, hz₂, e₂⟩ := hb
  refine ⟨t₁ * t₂, fun hm => (h𝔭.mem_or_mem hm).elim ht₁ ht₂, z₁ * z₂, ?_, ?_⟩
  · rw [pow_add]
    exact Ideal.mul_mem_mul hz₁ hz₂
  · simp only [map_mul, e₁, e₂]
    ring

theorem InP.mono {𝔭 : Ideal (𝓞 F)} {k l : ℕ} (hkl : l ≤ k) {a : K} (ha : InP 𝔭 k a) : InP 𝔭 l a := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  exact ⟨t, ht, z, Ideal.pow_le_pow_right hkl hz, e⟩

theorem inP_jK {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k : ℕ} {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    InP 𝔭 k (jK z) := ⟨1, (Ideal.ne_top_iff_one _).mp h𝔭.ne_top, z, hz, by rw [map_one, map_one, one_mul]⟩

def SP (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Subring K where
  carrier := {a | InP 𝔭 0 a}
  mul_mem' := fun ha hb => ha.mul hb
  one_mem' := by
    have := inP_jK (K := K) (𝔭 := 𝔭) (k := 0) (z := 1) (by simp)
    rwa [map_one] at this
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := by
    have := inP_jK (K := K) (𝔭 := 𝔭) (k := 0) (z := 0) (by simp)
    rwa [map_zero] at this
  neg_mem' := fun ha => ha.neg

theorem mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K} :
    a ∈ SP K 𝔭 ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z : 𝓞 K, jK z = jK (ι t) * a := by
  show InP 𝔭 0 a ↔ _
  constructor
  · rintro ⟨t, ht, z, -, e⟩
    exact ⟨t, ht, z, e⟩
  · rintro ⟨t, ht, z, e⟩
    exact ⟨t, ht, z, by simp, e⟩

theorem mem_SP_iff_locF {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K} :
    a ∈ SP K 𝔭 ↔ a ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have hp : 𝔭.IsPrime := inferInstance
  have key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s},
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, (Ideal.ne_top_iff_one _).mp hp.ne_top, map_one _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨t₁, ht₁, rfl⟩ := hx
      obtain ⟨t₂, ht₂, rfl⟩ := hy
      exact ⟨t₁ * t₂, fun hm => (hp.mem_or_mem hm).elim ht₁ ht₂, map_mul _ _ _⟩
  change a ∈ SP K 𝔭 ↔ ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s},
    s • a ∈ (1 : Submodule (𝓞 K) K)
  rw [mem_SP]
  constructor
  · rintro ⟨t, ht, z, e⟩
    refine ⟨ι t, Submonoid.subset_closure ⟨t, ht, rfl⟩, ?_⟩
    rw [Submodule.mem_one]
    exact ⟨z, by rw [e, Algebra.smul_def]⟩
  · rintro ⟨s, hs, hsa⟩
    obtain ⟨t, ht, rfl⟩ := key s hs
    rw [Submodule.mem_one] at hsa
    obtain ⟨z, hz⟩ := hsa
    exact ⟨t, ht, z, by rw [hz, Algebra.smul_def]⟩

theorem jK_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (z : 𝓞 K) : jK z ∈ SP K 𝔭 := mem_SP.mpr ⟨1, (Ideal.ne_top_iff_one _).mp (Ideal.IsPrime.ne_top inferInstance), z,
  by rw [map_one, map_one, one_mul]⟩

theorem InP.mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {a : K} (ha : InP 𝔭 k a) : a ∈ SP K 𝔭 := ha.mono (Nat.zero_le _)

theorem InP.conj (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : K} (ha : InP 𝔭 k a) :
    InP 𝔭 k (star a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  have hι : ∀ c : 𝓞 F, conjO K (ι c) = ι c := by
    intro c
    apply RingOfIntegers.ext
    show star (algebraMap F K (c : F)) = algebraMap F K (c : F)
    exact (hF _).mpr ⟨_, rfl⟩
  have hι' : (conjO K).comp (algebraMap (𝓞 F) (𝓞 K)) = algebraMap (𝓞 F) (𝓞 K) := RingHom.ext hι
  refine ⟨t, ht, conjO K z, ?_, ?_⟩
  · have h1 : conjO K z ∈ (extP K 𝔭 ^ k).map (conjO K) := Ideal.mem_map_of_mem _ hz
    rwa [Ideal.map_pow, extP, Ideal.map_map, hι'] at h1
  · have s1 : jK (conjO K z) = star (jK z) := rfl
    have s2 : star (jK (ι t)) = jK (ι t) := (hF _).mpr ⟨_, rfl⟩
    rw [s1, e, star_mul, s2, mul_comm]

theorem exists_unif0 {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ π₀ ∈ 𝔭, π₀ ∉ 𝔭 ^ 2 ∧ ∃ s₀ : 𝓞 F, s₀ ∉ 𝔭 ∧ Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀} := by
  have hne : 𝔭 ≠ ⊥ := fun h0 =>
    RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h0 ▸ h𝔭))
  obtain ⟨π₀, hπ1, hπ2⟩ : ∃ x ∈ 𝔭 ^ 1, x ∉ 𝔭 ^ (1 + 1) := by
    have hlt : 𝔭 ^ (1 + 1) < 𝔭 ^ 1 := Ideal.pow_succ_lt_pow hne 1
    obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx1, hx2⟩
  rw [pow_one] at hπ1
  have hπ2' : π₀ ∉ 𝔭 ^ 2 := hπ2
  obtain ⟨J, hJ⟩ : 𝔭 ∣ Ideal.span {π₀} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ1)
  have hJ𝔭 : ¬ J ≤ 𝔭 := by
    intro hle
    apply hπ2'
    have h3 : Ideal.span {π₀} ≤ 𝔭 ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right hle
    exact h3 (Ideal.subset_span rfl)
  obtain ⟨s₀, hsJ, hs𝔭⟩ := SetLike.not_le_iff_exists.mp hJ𝔭
  refine ⟨π₀, hπ1, hπ2', s₀, hs𝔭, ?_⟩
  rw [hJ, mul_comm 𝔭 J]
  exact Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hsJ)

theorem span_pow_mul_le {𝔭 : Ideal (𝓞 F)} {π₀ s₀ : 𝓞 F}
    (h : Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀}) (k : ℕ) :
    Ideal.span {ι (s₀ ^ k)} * extP K 𝔭 ^ k ≤ Ideal.span {ι (π₀ ^ k)} := by
  have h1 : (Ideal.span {s₀} * 𝔭) ^ k ≤ Ideal.span {π₀} ^ k := Ideal.pow_right_mono h k
  rw [mul_pow, Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h1
  have h2 := Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 K)) h1
  rw [Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.map_pow] at h2
  exact h2

end Formalism.HermitianLattices.Ext.L3.HU
end
end
