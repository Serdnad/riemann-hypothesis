module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

theorem unitP : UnitP := by
  intro F E _ _ _ _ _ sig p A d hd
  have hv1 : p.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) p).2 hd
  have h1 : A.ιF (algebraMap (𝓞 F) F d) ≤ᵥ A.ιF 1 := (A.val _ _).2 (by rw [hv1, map_one])
  have h2 : A.ιF 1 ≤ᵥ A.ιF (algebraMap (𝓞 F) F d) := (A.val _ _).2 (by rw [hv1, map_one])
  rw [map_one] at h1 h2
  have hcv : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F d)) = 1 :=
    le_antisymm ((Valuation.vle_one_iff _).1 h1) ((Valuation.one_vle_iff _).1 h2)
  have hc0 : A.ιF (algebraMap (𝓞 F) F d) ≠ 0 := by
    intro h
    rw [h, map_zero] at hcv
    exact zero_ne_one hcv
  have hinv : (A.ιF (algebraMap (𝓞 F) F d))⁻¹ ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, hcv, inv_one]
  refine ⟨algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹, ?_, ?_⟩
  · rw [A.O_def]
    have hu : algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹ =
        algebraMap 𝒪[A.Fp] A.Ep ⟨_, hinv⟩ := rfl
    rw [hu]
    exact isIntegral_algebraMap
  · have hd' : A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) =
        algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d)) := by
      rw [← A.compat]
      rfl
    rw [hd', ← map_mul, inv_mul_cancel₀ hc0, map_one]

theorem avoidP : AvoidP := by
  intro F E _ _ _ _ _ p I hI
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hle : I.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ p.asIdeal := by
    intro d hd
    by_contra hdp
    exact hne d hdp hd
  obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal I hle
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := by
    intro a b hab
    have hE : algebraMap F E (a : F) = algebraMap F E (b : F) := congrArg (fun x : 𝓞 E => (x : E)) hab
    exact Subtype.ext ((algebraMap F E).injective hE)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply p.ne_bot
    rw [← hQp, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
  exact hI ⟨Q, hQ, hQ0⟩ hQp hIQ

end PI.LocLatEq.W
end
end

section

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem core_gen_ideal (hA : AvoidP) (p : HeightOneSpectrum (𝓞 F)) (𝔞 : Ideal (𝓞 E)) :
    ∃ a ∈ 𝔞, ∀ b ∈ 𝔞, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ r : 𝓞 E,
      algebraMap (𝓞 F) (𝓞 E) d * b = r * a := by
  classical
  by_cases h𝔞 : 𝔞 = ⊥
  · refine ⟨0, 𝔞.zero_mem, fun b hb => ⟨1, ?_, 0, ?_⟩⟩
    · exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    · rw [h𝔞, Ideal.mem_bot] at hb
      simp [hb]
  have h𝔞0 : 𝔞 ≠ 0 := h𝔞
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hpE0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hinj]
    exact p.ne_bot
  have hle : 𝔞 * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ 𝔞 :=
    Ideal.mul_le_inf.trans inf_le_left
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle (mul_ne_zero h𝔞0 hpE0)
  have haa : a ∈ 𝔞 := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨𝔠, h𝔠⟩ : 𝔞 ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haa)
  have hav : ∀ P : HeightOneSpectrum (𝓞 E),
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ¬ 𝔠 ≤ P.asIdeal := by
    intro P hP hcP
    have h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ P.asIdeal :=
      Ideal.map_le_iff_le_comap.mpr hP.ge
    have h2 : 𝔞 ≤ 𝔞 * P.asIdeal := by
      conv_lhs => rw [← ha]
      refine sup_le (Ideal.mul_mono_right h1) ?_
      rw [h𝔠]
      exact Ideal.mul_mono_right hcP
    have h3 : 𝔞 * P.asIdeal ∣ 𝔞 * 1 := by
      rw [mul_one]
      exact Ideal.dvd_iff_le.mpr h2
    have h4 := (mul_dvd_mul_iff_left h𝔞0).mp h3
    exact P.isPrime.ne_top (Ideal.isUnit_iff.mp (isUnit_of_dvd_one h4))
  obtain ⟨d, hdp, hd⟩ := hA F E p 𝔠 hav
  refine ⟨a, haa, fun b hb => ⟨d, hdp, ?_⟩⟩
  have hmem : algebraMap (𝓞 F) (𝓞 E) d * b ∈ Ideal.span {a} := by
    rw [h𝔠, mul_comm (algebraMap (𝓞 F) (𝓞 E) d) b]
    exact Ideal.mul_mem_mul hb hd
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨r, hr.symm⟩

theorem core_gen (hA : AvoidP) (p : HeightOneSpectrum (𝓞 F)) (I : Submodule (𝓞 E) E)
    (hI : I.FG) : ∃ a ∈ I, ∀ b ∈ I, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ r : 𝓞 E,
      algebraMap (𝓞 F) (𝓞 E) d • b = r • a := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) S
  have hc0 : algebraMap (𝓞 E) E (c : 𝓞 E) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr (nonZeroDivisors.coe_ne_zero c)
  have hint : ∀ x ∈ Submodule.span (𝓞 E) (S : Set E),
      ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (c : 𝓞 E) • x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy⟩ := hc x hx
      exact ⟨y, hy⟩
    | zero => exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨y1, h1⟩ := hx
      obtain ⟨y2, h2⟩ := hz
      exact ⟨y1 + y2, by rw [map_add (f := _), h1, h2, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨y, h⟩ := hx
      refine ⟨r * y, ?_⟩
      rw [map_mul, h]
      simp only [Algebra.smul_def]
      ring
  obtain ⟨a0, ha0, hgen⟩ := core_gen_ideal (F := F) hA p
    ((Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹))
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply] at ha0
  refine ⟨a0 • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹, ha0, fun b hb => ?_⟩
  obtain ⟨y, hy⟩ := hint b hb
  have hyb : y • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹ = b := by
    rw [Algebra.smul_def, hy, Algebra.smul_def, mul_comm, ← mul_assoc, inv_mul_cancel₀ hc0,
      one_mul]
  have hy𝔞 : y ∈ (Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹) := by
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, hyb]
    exact hb
  obtain ⟨d, hd, r, hr⟩ := hgen y hy𝔞
  refine ⟨d, hd, r, ?_⟩
  rw [← hyb, smul_smul, smul_smul, hr]

end PI.LocLatEq.W
end
end
