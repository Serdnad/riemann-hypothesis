module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle002
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Formalism.GaloisCohomology.Statement
public import Mathlib.Algebra.Algebra.ZMod

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.decActRoots :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (m : ℕ), m.Coprime l → ∀ g ∈ Dec (F := F) A, ∃ k : ℕ, ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l ^ k := by
  intro F Ω _ _ _ _ _ l _ A hA m hm g hg
  have hl : l.Prime := Fact.out
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hm
    exact hl.one_lt.ne' hm
  haveI : NeZero m := ⟨hm0⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hmemA : ∀ ξ : Ω, ξ ^ m = 1 → ξ ∈ A := by
    intro ξ hξ
    rw [← ValuationSubring.valuation_le_one_iff]
    exact (pow_le_one_iff hm0).mp (by rw [← map_pow, hξ, map_one])
  have hgm : (g ζ0) ^ m = 1 := by rw [← map_pow, hζ0.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ0.eq_pow_of_pow_eq_one hgm
  let g' : A.decompositionSubgroup F := ⟨g, hg⟩
  have hlm : ((l : A)) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using hA
  haveI : CharP (IsLocalRing.ResidueField A) l := by
    rw [CharP.charP_iff_prime_eq_zero hl]
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  let z0 : A := ⟨ζ0, hmemA ζ0 hζ0.pow_eq_one⟩
  let ω : IsLocalRing.ResidueField A := IsLocalRing.residue A z0
  have hσω : g' • ω = ω ^ a := by
    have hz : g' • z0 = z0 ^ a := Subtype.ext (by
      change g ζ0 = ζ0 ^ a
      exact ha.symm)
    simp only [ω]
    rw [← IsLocalRing.ResidueField.residue_smul, hz, map_pow]
  let σ : IsLocalRing.ResidueField A →ₐ[ZMod l] IsLocalRing.ResidueField A :=
    { MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g' with
      commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod
        ((MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g').comp
          (algebraMap (ZMod l) (IsLocalRing.ResidueField A)))
        (algebraMap (ZMod l) (IsLocalRing.ResidueField A))) r }
  have hσ : ∀ x, σ x = g' • x := fun x => rfl
  let E := IntermediateField.adjoin (ZMod l) ({ω} : Set (IsLocalRing.ResidueField A))
  have hωE : ω ∈ E := IntermediateField.mem_adjoin_simple_self _ _
  have hint : IsIntegral (ZMod l) ω := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) ?_
    have h1 : ω ^ m = 1 := by
      simp only [ω]
      rw [← map_pow]
      have : z0 ^ m = 1 := Subtype.ext (by
        change ζ0 ^ m = 1
        exact hζ0.pow_eq_one)
      rw [this, map_one]
    rw [h1]
    exact isIntegral_one
  haveI : FiniteDimensional (ZMod l) E := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite E := Module.finite_of_finite (ZMod l)
  have hEle : E ≤ IntermediateField.comap σ E := by
    rw [IntermediateField.adjoin_simple_le_iff]
    show σ ω ∈ E
    rw [hσ, hσω]
    exact pow_mem hωE a
  have hmapE : ∀ x ∈ E, σ x ∈ E := fun x hx => hEle hx
  let τ : E →ₐ[ZMod l] E :=
    { toFun := fun x => ⟨σ x, hmapE x.1 x.2⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1)
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1)
      commutes' := fun r => Subtype.ext (σ.commutes r) }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) E).2 τ
  have hτω : τ ⟨ω, hωE⟩ = ⟨ω, hωE⟩ ^ (l ^ (n : ℕ)) := by
    rw [← hn]
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hres : ω ^ a = ω ^ (l ^ (n : ℕ)) := by
    have h2 : ((τ ⟨ω, hωE⟩ : E) : IsLocalRing.ResidueField A) = σ ω := rfl
    have := congrArg Subtype.val hτω
    rw [h2] at this
    rw [← hσω, ← hσ]
    simpa using this
  have hfin : g ζ0 = ζ0 ^ (l ^ (n : ℕ)) := by
    rw [← ha]
    have hroot : (ζ0 ^ (l ^ (n : ℕ))) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    have hroota : (ζ0 ^ a) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    refine (UpperTheory.V.LDataCardLeFinrank.ineFixRoots F Ω l A hA m hm _ hroot).1 _ hroota ?_
    have hsub : (z0 ^ a - z0 ^ (l ^ (n : ℕ))) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_pow, sub_eq_zero]
      exact hres
    rw [ValuationSubring.valuation_lt_one_iff] at hsub
    simpa using hsub
  refine ⟨n, fun ζ hζ => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, hfin, ← pow_mul, ← pow_mul, mul_comm]
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

namespace UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact Nat.prime_iff_prime_int.mp hl.out

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

private theorem normV_vQ : normV (vQ l) = l := by
  show Nat.card (𝓞 ℚ ⧸ Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr ((Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)).toEquiv, Nat.card_zmod]

variable {l} {Ω : Type} [Field Ω]

private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show _ ∈ Ideal.span _ ↔ _
  rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv]
  simp

private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  exact intCast_mem A n

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hn
    have hirr : Irreducible ((l : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hl.out).irreducible
    obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hn
    have h1 : A.valuation (((a * ((l : ℕ) : ℤ) + b * n : ℤ)) : Ω) < 1 := by
      push_cast
      apply Valuation.map_add_lt
      · rw [Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) (by exact_mod_cast hA)
      · rw [Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
    rw [hab] at h1
    simp at h1
  · rintro ⟨k, rfl⟩
    push_cast
    rw [Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) (by exact_mod_cast hA)

private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by simp)⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA n]
  simp

end UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius

open UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius in
theorem UpperTheory.V.LDataCardLeFinrank.decFrob :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := ℚ) A, ∀ m : ℕ, m.Coprime l → ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l := by
  intro Ω _ _ _ l _ A hA
  have hP : IsPlaceOver (F := ℚ) A (vQ l) := isPlaceOver_vQ A (by exact_mod_cast hA)
  obtain ⟨σ, hσD, hσ⟩ := exists_isFrob hP
  rw [normV_vQ] at hσ
  refine ⟨σ, hσD, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : l.Prime).one_lt.ne' (by simpa using hm)
  have hζv : A.valuation ζ ≤ 1 := by
    by_contra h
    have h2 := one_lt_pow' (not_le.mp h) hm0
    rw [← map_pow, hζ, map_one] at h2
    exact lt_irrefl _ h2
  have key := (ineFixRoots ℚ Ω l A hA m hm (ζ ^ l) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])).1
  apply key (σ ζ)
  · rw [← map_pow, hζ, map_one]
  · exact hσ ζ hζv
end
