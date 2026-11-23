module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalB
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.DedekindDomain.Factorization
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial

theorem eventually_natCast_notMem (E : Type) [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : (Ideal.span {((l : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simpa [Ideal.dvd_span_singleton] using hw

end GlobalTheory.HeightCounting

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem valuation_algebraMap_int_le_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (x : 𝓞 E) : A.valuation (algebraMap E Ω (x : E)) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A (RingOfIntegers.isIntegral_coe x).algebraMap)

theorem valuation_uniformiser_le {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hP : IsPlaceOver A P) {ϖ ϖ' : 𝓞 E}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal) :
    A.valuation (algebraMap E Ω (ϖ' : E)) ≤ A.valuation (algebraMap E Ω (ϖ : E)) := by
  have hdvd : P.asIdeal ∣ Ideal.span {ϖ} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ (J : Set (𝓞 E)) ⊆ P.asIdeal := by
    intro hle
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  have hmem : ϖ' * s ∈ Ideal.span {ϖ} := by
    rw [hJ]; exact Ideal.mul_mem_mul h1' hsJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have hs1 : A.valuation (algebraMap E Ω (s : E)) = 1 :=
    le_antisymm (valuation_algebraMap_int_le_one A s) (not_lt.1 fun h => hsP ((hP s).1 h))
  have e : algebraMap E Ω (a : E) * algebraMap E Ω (ϖ : E) = algebraMap E Ω (ϖ' : E) * algebraMap E Ω (s : E) := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact_mod_cast ha
  have hv := congrArg A.valuation e
  rw [map_mul, map_mul, hs1, mul_one] at hv
  rw [← hv]
  calc A.valuation (algebraMap E Ω (a : E)) * A.valuation (algebraMap E Ω (ϖ : E))
      ≤ 1 * A.valuation (algebraMap E Ω (ϖ : E)) := by
        gcongr; exact valuation_algebraMap_int_le_one A a
    _ = A.valuation (algebraMap E Ω (ϖ : E)) := one_mul _

theorem tame_quot_indep : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → ∀ (ϖ ϖ' : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ (π π' : Ω), π ^ m = algebraMap E Ω (ϖ : E) → π' ^ m = algebraMap E Ω (ϖ' : E) → ∀ σ ∈ Ine (F := E) A, σ π / π = σ π' / π' := by
  intro E Ω _ _ _ _ _ A P hP m hm0 hmP ϖ ϖ' h1 h2 h1' h2' π π' hπ hπ' σ hσ
  have hne : ∀ x : 𝓞 E, x ∉ P.asIdeal ^ 2 → algebraMap E Ω (x : E) ≠ 0 := by
    intro x hx h0
    apply hx
    have hx0 : (x : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).1 h0
    have : x = 0 := by exact_mod_cast hx0
    rw [this]; exact zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hne ϖ h2 (by rw [← hπ, zero_pow hm0.ne'])
  have hπ0' : π' ≠ 0 := by
    rintro rfl; exact hne ϖ' h2' (by rw [← hπ', zero_pow hm0.ne'])
  have hv : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ' : E)) :=
    le_antisymm (valuation_uniformiser_le hP h1' h2' h1) (valuation_uniformiser_le hP h1 h2 h1')
  set ρ := π' / π with hρ
  have hρ0 : ρ ≠ 0 := div_ne_zero hπ0' hπ0
  have hρm : ρ ^ m = algebraMap E Ω ((ϖ' : E) / (ϖ : E)) := by
    rw [hρ, div_pow, hπ, hπ', map_div₀]
  have hvρm : A.valuation ρ ^ m = 1 := by
    rw [← Valuation.map_pow, hρm, map_div₀, map_div₀, hv, div_self]
    simpa using hne ϖ' h2'
  have hvρ : A.valuation ρ = 1 := by
    rcases lt_trichotomy (A.valuation ρ) 1 with h | h | h
    · exact absurd hvρm (pow_lt_one₀ zero_le h hm0.ne').ne
    · exact h
    · exact absurd hvρm (one_lt_pow₀ h hm0.ne').ne'
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    apply (hP _).1
    simpa using h
  have hσρm : (σ ρ / ρ) ^ m = 1 := by
    rw [div_pow, ← map_pow, hρm, AlgEquiv.commutes, ← hρm]
    exact div_self (pow_ne_zero _ hρ0)
  have hclose : A.valuation (σ ρ / ρ - 1) < 1 := by
    have e : σ ρ / ρ - 1 = (σ ρ - ρ) / ρ := by field_simp
    rw [e, map_div₀, hvρ, div_one]
    exact hσ.2 ρ hvρ.le
  have hfix : σ ρ / ρ = 1 := root_eq_of_close A m hσρm (one_pow m) hmv hclose
  have hfix' : σ ρ = ρ := (div_eq_one_iff_eq hρ0).1 hfix
  have eπ' : π' = ρ * π := by rw [hρ]; field_simp
  rw [eπ', map_mul, hfix', mul_div_mul_left _ _ hρ0]

end GlobalTheory.TameTau
end

section

set_option autoImplicit false

namespace GlobalTheory.SquareNorm

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem exists_eq_mul_map {R : Type} [CommRing R] [IsDedekindDomain R] (e : R ≃+* R) (he : ∀ x, e (e x) = x)
    (𝔡 : Ideal R) : 𝔡 ≠ ⊥ → 𝔡.map (e : R →+* R) = 𝔡 →
      (∀ P : Ideal R, P.IsPrime → 𝔡 ≤ P → P.map (e : R →+* R) ≠ P) →
      ∃ 𝔞 : Ideal R, 𝔡 = 𝔞 * 𝔞.map (e : R →+* R) := by
  have hee : ∀ I : Ideal R, (I.map (e : R →+* R)).map (e : R →+* R) = I := fun I => by
    rw [Ideal.map_map]
    have : (e : R →+* R).comp (e : R →+* R) = RingHom.id R := RingHom.ext he
    rw [this, Ideal.map_id]
  induction 𝔡 using WellFoundedGT.induction with
  | ind 𝔡 ih =>
  intro h0 hinv hmv
  by_cases ht : 𝔡 = ⊤
  · exact ⟨⊤, by rw [ht, Ideal.map_top, Ideal.top_mul]⟩
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal 𝔡 ht
  have hQ : (P.map (e : R →+* R)).IsMaximal := Ideal.IsMaximal.map_bijective (e : R →+* R) e.bijective hP
  have hne := hmv P hP.isPrime hle
  have hle' : 𝔡 ≤ P.map (e : R →+* R) := by
    have := Ideal.map_mono (f := (e : R →+* R)) hle
    rwa [hinv] at this
  have hcop : IsCoprime P (P.map (e : R →+* R)) :=
    Ideal.isCoprime_iff_sup_eq.2 (hP.coprime_of_ne hQ hne.symm)
  obtain ⟨𝔟, hb⟩ := hcop.mul_dvd (Ideal.dvd_iff_le.2 hle) (Ideal.dvd_iff_le.2 hle')
  have hPQ : P * P.map (e : R →+* R) ≠ 0 := fun h => h0 (by rw [hb, h, zero_mul]; rfl)
  have hb0 : 𝔟 ≠ ⊥ := fun h => h0 (by rw [hb, h, Ideal.mul_bot])
  have hdb : 𝔡 ≤ 𝔟 := Ideal.le_of_dvd ⟨P * P.map (e : R →+* R), by rw [mul_comm]; exact hb⟩
  have hlt : 𝔡 < 𝔟 := by
    refine lt_of_le_of_ne hdb fun h => ?_
    have h1 : P * P.map (e : R →+* R) * 𝔟 = 1 * 𝔟 := by rw [← hb, one_mul, h]
    have h2 := mul_right_cancel₀ hb0 h1
    have h3 : (1 : Ideal R) ≤ P := Ideal.le_of_dvd ⟨_, h2.symm⟩
    rw [Ideal.one_eq_top] at h3
    exact hP.ne_top (top_le_iff.1 h3)
  have hbinv : 𝔟.map (e : R →+* R) = 𝔟 := by
    apply mul_left_cancel₀ hPQ
    rw [← hb]
    conv_rhs => rw [← hinv, hb]
    rw [Ideal.map_mul, Ideal.map_mul, hee, mul_comm P]
  obtain ⟨𝔞, ha⟩ := ih 𝔟 hlt hb0 hbinv fun Q hQ' h => hmv Q hQ' (hdb.trans h)
  refine ⟨P * 𝔞, ?_⟩
  rw [hb, Ideal.map_mul]
  conv_lhs => rw [ha]
  ring

theorem isSquare_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (𝔡 : Ideal (𝓞 E)), 𝔡 ≠ ⊥ → 𝔡.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔡 → (∀ P : Ideal (𝓞 E), P.IsPrime → 𝔡 ≤ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P) → IsSquare (Ideal.absNorm 𝔡) := by
  intro E _ _ _ H 𝔡 h0 hinv hmv
  have he : ∀ x, H.bar (H.bar x) = x := fun x => RingOfIntegers.ext (by
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])
  obtain ⟨𝔞, ha⟩ := exists_eq_mul_map H.bar he 𝔡 h0 hinv hmv
  have hN : Ideal.absNorm (𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm 𝔞 := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv 𝔞 _ H.bar rfl).toEquiv).symm
  exact ⟨Ideal.absNorm 𝔞, by rw [ha, map_mul, hN]⟩

end GlobalTheory.SquareNorm
end
