module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.Valuation.Basic
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem GlobalTheory.QNorm.exists_ringHom_adicCompletion_under :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (w : HeightOneSpectrum (𝓞 E)),
      ∃ φ : (w.under (𝓞 F)).adicCompletion F →+* w.adicCompletion E,
        ∀ x : F, φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
          algebraMap E (w.adicCompletion E) (algebraMap F E x) := by
  intro K L _ _ _ _ _ w
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L (w.under (𝓞 K))
    w).continuous
  refine ⟨((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((w.under (𝓞 K)).valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K (w.under (𝓞 K))).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_sub_sq_mem_of_two_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (a : 𝓞 F) :
    ∃ b : 𝓞 F, a - b ^ 2 ∈ v.asIdeal := by
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI := v.isPrime
  have h0 : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 h2
    rwa [map_ofNat] at this
  have hinj : Function.Injective (fun t : 𝓞 F ⧸ v.asIdeal => t ^ 2) := by
    intro s t hst
    have hst' : s ^ 2 = t ^ 2 := hst
    have : (s - t) ^ 2 = 0 := by
      linear_combination hst' + (t ^ 2 - s * t) * h0
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj (Ideal.Quotient.mk v.asIdeal a)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨b, Ideal.Quotient.eq.1 ?_⟩
  rw [map_pow]
  exact ht.symm

theorem exists_sub_sq_lt_one_of_two_lt_one :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      Valued.v (2 : v.adicCompletion F) < 1 → ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
        ∃ y : v.adicCompletion F, Valued.v y ≤ 1 ∧ Valued.v (x - y ^ 2) < 1 := by
  intro F _ _ v h2 x hx
  set φ := algebraMap F (v.adicCompletion F) with hφ
  have hval : ∀ k : F, Valued.v (φ k) = v.valuation F k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have hmem : ∀ r : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F r) < 1 ↔ r ∈ v.asIdeal :=
    fun r => HeightOneSpectrum.valuation_lt_one_iff_mem v r

  have h2' : (2 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hmem, ← hval, map_ofNat, map_ofNat]
    exact h2

  obtain ⟨k, hk⟩ : ∃ k : F, Valued.v (φ k - x) < 1 := by
    have hU : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x := by
      rw [Valued.mem_nhds]
      refine ⟨1, fun y hy => ?_⟩
      have hy' : Valued.v.restrict (y - x) < Valued.v.restrict 1 := by simpa using hy
      simpa using Valued.v.restrict_lt_iff.mp hy'
    exact (HeightOneSpectrum.denseRange_algebraMap F v).mem_nhds hU
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← hval]
    have e : φ k = (φ k - x) + x := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le hk.le hx)

  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) < 1 := by
    obtain ⟨s, m, hs, hsm⟩ : ∃ s m : 𝓞 F, s ∉ v.asIdeal ∧
        k * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F m := by
      obtain ⟨n, d, h | h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := F) v k
      · exact ⟨d, n, d.2, h⟩
      · refine ⟨n, d, fun hn => d.2 ?_, h⟩
        show (d : 𝓞 F) ∈ v.asIdeal
        rw [← hmem, ← h, map_mul]
        exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem n).2 hn)
    obtain ⟨t, i, hi, hti⟩ := (Ideal.IsPrime.isMaximal v.isPrime v.ne_bot).exists_inv hs
    refine ⟨t * m, ?_⟩
    have hi' : i = 1 - t * s := by rw [← hti]; ring
    have e : k - algebraMap (𝓞 F) F (t * m) = k * algebraMap (𝓞 F) F i := by
      rw [hi', map_mul, ← hsm, map_sub, map_one, map_mul]; ring
    rw [e, map_mul]
    exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem i).2 hi)

  obtain ⟨b, hb⟩ := exists_sub_sq_mem_of_two_mem F v h2' r
  refine ⟨φ (algebraMap (𝓞 F) F b), ?_, ?_⟩
  · rw [hval]
    exact HeightOneSpectrum.valuation_le_one v b
  · have e : x - φ (algebraMap (𝓞 F) F b) ^ 2 =
        -(φ k - x) + (φ (k - algebraMap (𝓞 F) F r) + φ (algebraMap (𝓞 F) F (r - b ^ 2))) := by
      simp only [map_sub, map_pow]; ring
    rw [e]
    refine Valuation.map_add_lt _ (by rwa [Valuation.map_neg]) (Valuation.map_add_lt _ ?_ ?_)
    · rw [hval]; exact hr
    · rw [hval]; exact (hmem _).2 hb

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CoordDiv

variable (F : Type) [Field F] [NumberField F]

def intAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {c | ∀ v, c v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' := fun {a b} ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' := fun {a b} ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' := fun {a} ha v => neg_mem (ha v)

theorem algebraMap_mem (a : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ intAdeles F := by
  intro v
  rw [FiniteAdeleRing.algebraMap_apply, RingOfIntegers.coe_eq_algebraMap]
  exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a

theorem exists_of_mem (k : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ intAdeles F) :
    ∃ a : 𝓞 F, (a : F) = k := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => by
    have hv := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  exact ⟨a, ha⟩

theorem dvd_of_eq (x : 𝓞 F) (N : ℕ) (hN : 0 < N) (e : FiniteAdeleRing (𝓞 F) F)
    (he : e ∈ intAdeles F)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) = (N : FiniteAdeleRing (𝓞 F) F) * e) :
    ∃ a : 𝓞 F, x = (N : 𝓞 F) * a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((x : F) / N) = e := by
    rw [div_eq_mul_inv, map_mul, h, mul_comm, ← mul_assoc,
      ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, inv_mul_cancel₀ hN',
      map_one, one_mul]
  obtain ⟨a, ha⟩ := exists_of_mem F _ (hk ▸ he)
  have hx : (x : F) = N * (a : F) := by
    rw [ha]
    field_simp
  exact ⟨a, by exact_mod_cast hx⟩

theorem int_dvd (z : ℤ) (N : ℕ) (a : 𝓞 F) (h : (z : 𝓞 F) = (N : 𝓞 F) * a) : (N : ℤ) ∣ z := by

  have h2 := congrArg (Algebra.norm ℤ) h
  rw [map_mul, ← eq_intCast (algebraMap ℤ (𝓞 F)) z,
    show (N : 𝓞 F) = algebraMap ℤ (𝓞 F) (N : ℤ) by simp, Algebra.norm_algebraMap,
    Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').mp ⟨_, h2⟩

theorem coord_divisible : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (r : β → FiniteAdeleRing (𝓞 F) F) (N : ℕ), 0 < N → (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) → (∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v, (e : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) = (N : FiniteAdeleRing (𝓞 F) F) * e) → ∀ i, ∃ s : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ s = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c) ∧ r i = (N : FiniteAdeleRing (𝓞 F) F) * s := by
  intro F _ _ β _ ω r N hN hr hsum i
  obtain ⟨e, he, hsum⟩ := hsum
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F) := by
    have := (isUnit_iff_ne_zero.mpr hN').map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
    rwa [map_natCast] at this
  have hω : ∀ j, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω j : 𝓞 F) : F) ∈ intAdeles F :=
    fun j => algebraMap_mem F (ω j)
  have hint : ∀ z : ℤ, (z : FiniteAdeleRing (𝓞 F) F) ∈ intAdeles F := fun z => intCast_mem _ z

  choose z c hc hrc using fun j => hr j N hN
  have hc' : ∀ j, c j ∈ intAdeles F := hc

  have hL : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∑ j, z j • ω j : 𝓞 F)) : F) =
      ∑ j, (z j : FiniteAdeleRing (𝓞 F) F) * algebraMap F _ ((ω j : 𝓞 F) : F) := by

    rw [RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, zsmul_eq_mul, RingOfIntegers.coe_eq_algebraMap]
  obtain ⟨a, ha⟩ := dvd_of_eq F (∑ j, z j • ω j) N hN
    (e - ∑ j, c j * algebraMap F _ ((ω j : 𝓞 F) : F))
    (sub_mem he (sum_mem fun j _ => mul_mem (hc' j) (hω j))) (by
      rw [hL, mul_sub, Finset.mul_sum, ← hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrc j]
      ring)

  have hm : ∀ j, z j = N * ω.repr a j := by
    intro j
    have h1 := congrArg (fun y => ω.repr y j) ha
    have h2 : (N : 𝓞 F) * a = (N : ℤ) • a := by rw [zsmul_eq_mul]; push_cast; rfl
    simp only [ω.repr_sum_self, h2, map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h1
    simpa using h1
  have key : ∀ j, r j = N * ((ω.repr a j : FiniteAdeleRing (𝓞 F) F) + c j) := by
    intro j
    rw [hrc j, hm j]
    push_cast
    ring
  refine ⟨(ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i, ?_, key i⟩
  intro M hM

  obtain ⟨z', c', hc'', hr'⟩ := hr i (M * N) (Nat.mul_pos hM hN)
  have hs : (ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i - M * c' ∈ intAdeles F :=
    sub_mem (add_mem (hint _) (hc' i)) (mul_mem (natCast_mem _ M) hc'')
  obtain ⟨a', ha'⟩ := dvd_of_eq F (z' : 𝓞 F) N hN _ hs (by
    have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((z' : 𝓞 F)) : F) =
        (z' : FiniteAdeleRing (𝓞 F) F) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_intCast, map_intCast]
    have e2 : (z' : FiniteAdeleRing (𝓞 F) F) = r i - ((M * N : ℕ) : FiniteAdeleRing (𝓞 F) F) * c' := by
      rw [hr']
      ring
    rw [e1, e2, key i]
    push_cast
    ring)
  obtain ⟨t, ht⟩ := int_dvd F z' N a' ha'
  refine ⟨t, c', hc'', hu.mul_left_cancel ?_⟩
  rw [← key i, hr', ht]
  push_cast
  ring

end GlobalTheory.CoordDiv
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_unit_mul_sq_sub_one_lt :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (δ π : K) (k : ℕ), w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1) → w δ = 1 → w 4 < w (δ - 1) → w (δ - 1) = WithZero.exp (-(2 * (k : ℤ))) → ∃ c : K, w c = 1 ∧ w (δ * c ^ 2 - 1) < w (δ - 1) := by
  intro K _ w δ π k hπ hres hδ h4 hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  ·
    have hδ0 : δ ≠ 0 := by
      intro h
      rw [h, map_zero] at hδ
      exact zero_ne_one hδ
    have hinv : w δ⁻¹ = 1 := by rw [map_inv₀, hδ, inv_one]
    obtain ⟨y, hy1, hy⟩ := hres δ⁻¹ hinv.le
    have hy2 : w (y ^ 2) = 1 := by
      have e : y ^ 2 = δ⁻¹ - (δ⁻¹ - y ^ 2) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rwa [hinv]), hinv]
    refine ⟨y, le_antisymm hy1 (not_lt.mp fun hlt => ?_), ?_⟩
    · rw [map_pow] at hy2
      exact (pow_lt_one₀ zero_le' hlt two_ne_zero).ne hy2
    · have e : δ * y ^ 2 - 1 = -(δ * (δ⁻¹ - y ^ 2)) := by
        rw [mul_sub, mul_inv_cancel₀ hδ0]
        ring
      rw [e, Valuation.map_neg, map_mul, hδ, one_mul, hk]
      simpa using hy
  ·

    set t := π ^ k with ht
    set g := w (δ - 1) with hg
    have hgpos : 0 < g := lt_of_le_of_lt zero_le' h4
    have htt : w t * w t = g := by
      show w t * w t = g
      rw [hk, ht, map_pow, hπ, ← pow_add, ← WithZero.exp_nsmul]
      congr 1
      rw [nsmul_eq_mul]
      push_cast
      ring
    have hwt0 : w t ≠ 0 := fun h => hgpos.ne (by simpa [h] using htt)
    have hwtpos : 0 < w t := zero_lt_iff.mpr hwt0
    have ht0 : t ≠ 0 := fun h => hwt0 (by rw [h, map_zero])
    have ht1 : w t < 1 := by
      rw [ht, map_pow, hπ]
      refine pow_lt_one₀ zero_le' ?_ hkpos.ne'
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    have hg1 : g < 1 := by
      rw [← htt]
      calc w t * w t ≤ w t * 1 := mul_le_mul' le_rfl ht1.le
        _ = w t := mul_one _
        _ < 1 := ht1
    have h2t : w 2 < w t := by
      refine lt_of_not_ge fun h => ?_
      have hle : g ≤ w 4 := by
        rw [← htt, show (4 : K) = 2 * 2 by norm_num, map_mul]
        exact mul_le_mul' h h
      exact absurd h4 (not_lt.mpr hle)
    set x := (δ - 1) * (t ^ 2)⁻¹ with hxdef
    have hx : t ^ 2 * x = δ - 1 := by
      rw [hxdef, mul_comm, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 ht0), mul_one]
    have hwx : w (-x) = 1 := by
      rw [Valuation.map_neg, hxdef, map_mul, map_inv₀, map_pow, ← hg, ← htt, sq,
        mul_inv_cancel₀ (mul_ne_zero hwt0 hwt0)]
    obtain ⟨y, hy1, hy⟩ := hres (-x) hwx.le
    refine ⟨1 + t * y, ?_, ?_⟩
    · apply Valuation.map_one_add_of_lt
      rw [map_mul]
      calc w t * w y ≤ w t * 1 := mul_le_mul' le_rfl hy1
        _ = w t := mul_one _
        _ < 1 := ht1
    · have e : δ * (1 + t * y) ^ 2 - 1
          = -(t ^ 2 * (-x - y ^ 2)) + 2 * t * y + (δ - 1) * (2 * t * y + t ^ 2 * y ^ 2) := by
        linear_combination (-1 : K) * hx
      rw [e]
      have hA : w (-(t ^ 2 * (-x - y ^ 2))) < g := by
        rw [Valuation.map_neg, map_mul, map_pow, sq, htt]
        calc g * w (-x - y ^ 2) < g * 1 := mul_lt_mul_of_pos_left hy hgpos
          _ = g := mul_one g
      have hB : w (2 * t * y) < g := by
        rw [map_mul, map_mul, ← htt]
        calc w 2 * w t * w y ≤ w 2 * w t * 1 := mul_le_mul' le_rfl hy1
          _ = w 2 * w t := mul_one _
          _ < w t * w t := mul_lt_mul_of_pos_right h2t hwtpos
      have hC : w ((δ - 1) * (2 * t * y + t ^ 2 * y ^ 2)) < g := by
        have hD : w (2 * t * y + t ^ 2 * y ^ 2) < 1 := by
          apply Valuation.map_add_lt
          · exact hB.trans hg1
          · rw [map_mul, map_pow w t, map_pow w y, sq (w t), htt]
            calc g * w y ^ 2 ≤ g * 1 := mul_le_mul' le_rfl (pow_le_one₀ zero_le' hy1)
              _ = g := mul_one g
              _ < 1 := hg1
        rw [map_mul, ← hg]
        calc g * w (2 * t * y + t ^ 2 * y ^ 2) < g * 1 := mul_lt_mul_of_pos_left hD hgpos
          _ = g := mul_one g
      exact Valuation.map_add_lt _ (Valuation.map_add_lt _ hA hB) hC

end GlobalTheory.QNorm
end
