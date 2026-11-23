module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle012
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

local instance (priority := 2000) ratFieldIsTorsionFreeForUnitaryThreeGroups (Ω : Type) [Field Ω] [CharZero Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

theorem UpperTheory.global_euler_characteristic_odd :
    GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω), ContainsAbove S l → (∀ v, IsPlaceOver (A v) v.1) →
                   ∀ ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M, ContAction ρ → (∃ g : G ℚ Ω, cycMod ℚ Ω l 1 g = -1 ∧ ρ (toGS Ω _ g) = 1) →
                   ∀ x : ∀ v : S, H2 (ρ.comp ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).comp (Dec (F := ℚ) (A v)).subtype) : Representation k _ M), ∃ z : H2 ρ,
                     ∀ v, resH2 ρ ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).comp (Dec (F := ℚ) (A v)).subtype) ((continuous_toGS Ω _).comp continuous_subtype_val) z = x v := by
  intro hPT Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ _ _ hl S A hS hA ρ hρ hg x
  obtain ⟨g, hg1, hg2⟩ := hg
  haveI : Finite M := Module.finite_of_finite k
  have hp : l.Prime := Fact.out
  choose κ hκ using fun v => Submodule.Quotient.mk_surjective _ (x v)
  have hn : ((l - 1 : ℕ) : ZMod (l ^ 1)) = (cycMod ℚ Ω l 1 g : (ZMod (l ^ 1))ˣ) := by
    have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, pow_one]
    rw [hg1, Nat.cast_sub hp.one_le, h0]
    simp
  have hne : (1 : k) ≠ ((l - 1 : ℕ) : k) := by
    rw [Nat.cast_sub hp.one_le, CharP.cast_eq_zero k l, Nat.cast_one]
    intro h
    have h2 : ((2 : ℕ) : k) = 0 := by
      push_cast
      linear_combination h
    rw [CharP.cast_eq_zero_iff k l] at h2
    exact hl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  obtain ⟨z, hz⟩ := UpperTheory.global_cohomology_finite_set hPT Ω l hl k M S A ρ hS hA hρ
    ⟨g, 1, l - 1, fun m => by rw [one_smul]; exact (congrArg (fun f : Module.End k M => f m) hg2), hn, hne⟩ κ
  refine ⟨Submodule.Quotient.mk z, fun v => ?_⟩
  rw [← hκ v]
  exact (Submodule.Quotient.eq _).2 (hz v)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem valuation_natCast_lt_one_iff_mem_asIdeal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (hA : IsPlaceOver A v) :
    A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have hcast : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
  rw [← hcast]
  exact hA ((l : ℕ) : 𝓞 ℚ)

theorem UpperTheory.inertia_le_normal_iff_ker_le_and_inertia_le :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S), ContainsAbove S l → (∀ v, IsPlaceOver (A v) v.1) →
          (∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) → ∀ (H : Subgroup (G ℚ Ω)) [H.Normal], (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ H →
          ∀ (M : Subgroup (G ℚ Ω)) [M.Normal], IsClosed (M : Set (G ℚ Ω)) →
          ((∀ g, (∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A' ∧ g ∈ H) → g ∈ M) ↔
            ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ M ∧ ∀ v : S, v ≠ v₀ → Ine (F := ℚ) (A v) ⊓ H ≤ M)) := by
  intro Ω _ _ _ l _ S A v₀ hS hA hv₀ H _ hH M _ hM
  have hker : (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker = NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    simp [toGS, QuotientGroup.ker_mk']
  have hin : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 ℚ)), w ∉ (S : Set (HeightOneSpectrum (𝓞 ℚ))) →
      IsPlaceOver B w → (Ine (F := ℚ) B : Set (G ℚ Ω)) ⊆ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro B w hw hB g hg
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion]
    exact ⟨w, hw, B, hB, hg⟩
  constructor
  · intro h
    constructor
    · rw [hker]
      apply Subgroup.topologicalClosure_minimal _ _ hM
      apply Subgroup.normalClosure_le_normal
      intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨w, hw, B, hB, hgB⟩ := hg
      have hgI : g ∈ Ine (F := ℚ) B := hgB
      apply h g
      refine ⟨B, ?_, hgI, ?_⟩
      · rw [valuation_natCast_lt_one_iff_mem_asIdeal l B w hB]
        intro hl
        exact hw (by simpa using hS w hl)
      · apply hH
        rw [hker]
        exact hin B w hw hB hgI
    · intro v hv g hg
      rw [Subgroup.mem_inf] at hg
      apply h g
      refine ⟨A v, ?_, hg.1, hg.2⟩
      rw [valuation_natCast_lt_one_iff_mem_asIdeal l (A v) v.1 (hA v), hv₀]
      exact hv
  · rintro ⟨h1, h2⟩ g ⟨B, hBl, hgB, hgH⟩
    by_cases hBt : B = ⊤
    · subst hBt
      rw [(Kum.placeDict ℚ Ω).1] at hgB
      rw [Subgroup.mem_bot] at hgB
      subst hgB
      exact M.one_mem
    obtain ⟨w, hw⟩ := (Kum.placeDict ℚ Ω).2.1 B hBt
    by_cases hwS : w ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    · let u : S := ⟨w, hwS⟩
      have hu0 : u ≠ v₀ := by
        intro hu
        rw [← hv₀ u] at hu
        exact hBl ((valuation_natCast_lt_one_iff_mem_asIdeal l B w hw).2 hu)
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hA u) hw
      rw [← hσ] at hgB
      have hc : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (A u) := ((ML.placeBasic Ω).2.2.2.2.2.2.2.2.2 (A u) σ).2.1 g |>.1 hgB
      have hcH : σ⁻¹ * g * σ ∈ H := by
        have := ‹H.Normal›.conj_mem g hgH σ⁻¹
        simpa [mul_assoc] using this
      have hcM := h2 u hu0 (Subgroup.mem_inf.2 ⟨hc, hcH⟩)
      have := ‹M.Normal›.conj_mem _ hcM σ
      simpa [mul_assoc] using this
    · apply h1
      rw [hker]
      exact hin B w hwS hw hgB
end
