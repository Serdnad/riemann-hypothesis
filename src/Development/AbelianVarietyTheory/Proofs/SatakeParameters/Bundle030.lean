module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle022
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPolynomialSubringMaximalIntegral
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle003
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle023
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.NeutralLocalFields.Bundle001
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic

@[expose] public section

section


theorem _root_.GlobalTheory.T.exists_norm_eq_fixed_unit_henselian : ∀ (R : Type) [CommRing R] (I : Ideal R) [HenselianRing R I] [Finite (R ⧸ I)] (c : R →+* R), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  first | exact @GlobalTheory.HenselianNorm.exists_norm_eq | exact GlobalTheory.HenselianNorm.exists_norm_eq | (intros; apply GlobalTheory.HenselianNorm.exists_norm_eq <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.isNoetherianRing_of_directed_pure_union' : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R → (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) → (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) → (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S := by
  first | (exact @GlobalTheory.isNoetherianRing_of_directed_pure_union) | (exact GlobalTheory.isNoetherianRing_of_directed_pure_union) | (intros; apply GlobalTheory.isNoetherianRing_of_directed_pure_union  <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_polynomialSubring_maximal_integral : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ (D : Subring K) (m₀ : Ideal D), φ.range ≤ D ∧ m₀.IsMaximal ∧
    (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) ∧ ∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x) := by
  first | exact @GlobalTheory.exists_polySubring_maximal_integral | exact GlobalTheory.exists_polySubring_maximal_integral | (intros; apply GlobalTheory.exists_polySubring_maximal_integral <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.HilbertClassField

namespace GlobalTheory

theorem inertiaEl_eq_one_or_liesAbove : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω),
    ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → g = 1 ∨ ∃ v : HeightOneSpectrum (𝓞 E), LiesAbove A v := by
  intro E Ω _ _ _ _ _ A g hg
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x =>
    ReciprocityTheory.ChartRestriction.L1.mem_of_isIntegral A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let φ : 𝓞 E →+* A := RingHom.codRestrict ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)) A hint
  let I : Ideal (𝓞 E) := Ideal.comap φ (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A.nonunits ↔ x ∈ I := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal, Ideal.mem_comap]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hint x, h⟩
  by_cases hbot : I = ⊥
  · left
    have hE : ∀ y : E, algebraMap E Ω y ∈ A := by
      intro y
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbn : algebraMap E Ω (algebraMap (𝓞 E) E b) ∉ A.nonunits := by
        rw [show algebraMap (𝓞 E) E b = (b : E) from rfl, hI, hbot, Ideal.mem_bot]; exact hb0
      have hbinv : (algebraMap E Ω (algebraMap (𝓞 E) E b))⁻¹ ∈ A := by
        rw [ValuationSubring.mem_nonunits_iff_or] at hbn
        push_neg at hbn; exact hbn.2
      rw [map_div₀, div_eq_mul_inv]
      exact mul_mem (hint a) hbinv
    have hall : ∀ x : Ω, x ∈ A := by
      intro x
      have hx : IsIntegral E x := ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic x).isIntegral
      obtain ⟨p, hpm, hp⟩ := hx
      let ψ : E →+* A := RingHom.codRestrict (algebraMap E Ω) A hE
      have hcomp : (algebraMap A Ω).comp ψ = algebraMap E Ω := by ext; rfl
      have h1 : IsIntegral A x := ⟨p.map ψ, hpm.map ψ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
      rw [← hy]; exact y.2
    ext x
    have h := hg.2 x (hall x)
    rw [ValuationSubring.mem_nonunits_iff_or] at h
    rcases h with h | h
    · simpa [sub_eq_zero] using h
    · exact absurd (hall _) h
  · right
    exact ⟨⟨I, Ideal.IsPrime.comap φ, hbot⟩, fun x => hI x⟩

end GlobalTheory
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.HilbertClassField

theorem _root_.GlobalTheory.T.inertiaElement_eq_one_or_liesAbove_finitePlace : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → g = 1 ∨ ∃ v : HeightOneSpectrum (𝓞 E), LiesAbove A v := by
  first | exact @GlobalTheory.inertiaEl_eq_one_or_liesAbove | exact GlobalTheory.inertiaEl_eq_one_or_liesAbove | (intros; apply GlobalTheory.inertiaEl_eq_one_or_liesAbove <;> assumption)

end
end
