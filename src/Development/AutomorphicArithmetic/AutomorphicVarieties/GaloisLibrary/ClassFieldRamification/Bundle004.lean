module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.PGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle001
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineFixQ :
    ∀ (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsGalois ℚ K] [IsGalois ℚ H] (p : ℕ), p.Prime → (UnramAt K p ↔ ∀ w : HeightOneSpectrum (𝓞 H), (p : 𝓞 H) ∈ w.asIdeal → w.asIdeal.inertia Gal(H/ℚ) ≤ (resTo ℚ K H).ker) := by
  intro K H _ _ _ _ _ _ _ p hp
  rw [UpperTheory.V.CF.unramIff.1 K p hp]
  constructor
  · intro h w hw
    have hv : (p : 𝓞 K) ∈ w.asIdeal.under (𝓞 K) := by
      simpa [Ideal.under, Ideal.mem_comap, map_natCast] using hw
    let v : HeightOneSpectrum (𝓞 K) := ⟨w.asIdeal.under (𝓞 K), inferInstance, fun hb => by
      rw [hb] at hv
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hv)⟩
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w]
    exact h v hv
  · intro h v hv
    have hle : Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) ⊥ ≤ v.asIdeal := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 H) (by rw [hx, map_zero])
      rw [hx0]
      exact v.asIdeal.zero_mem
    obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal ⊥ hle
    have hpQ : (p : 𝓞 H) ∈ Q := by
      have hc : (p : 𝓞 K) ∈ Q.comap (algebraMap (𝓞 K) (𝓞 H)) := by
        change (p : 𝓞 K) ∈ Ideal.under (𝓞 K) Q
        rw [hQv]
        exact hv
      simpa [Ideal.mem_comap, map_natCast] using hc
    let w : HeightOneSpectrum (𝓞 H) := ⟨Q, hQ, fun hb => by
      rw [hb] at hpQ
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hpQ)⟩
    have h1 := h w hpQ
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w] at h1
    have hw : Ideal.under (𝓞 K) w.asIdeal = v.asIdeal := hQv
    rwa [hw] at h1
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.grLocal :
    ∀ (p : ℕ) [Fact p.Prime] (R G : Type) [CommRing R] [IsLocalRing R] [CommGroup G] [Finite G], (p : R) ∈ IsLocalRing.maximalIdeal R → IsPGroup p G → ∃ _ : IsLocalRing (MonoidAlgebra R G), IsLocalRing.maximalIdeal (MonoidAlgebra R G) = (IsLocalRing.maximalIdeal R).comap (aug R G) ∧ IsLocalRing.maximalIdeal (MonoidAlgebra R G) = (IsLocalRing.maximalIdeal R).map (algebraMap R (MonoidAlgebra R G)) ⊔ augIdeal R G ∧ ∀ x, IsUnit x ↔ IsUnit (aug R G x) := by
  intro p _ R G _ _ _ _ hpm hG
  set J : Ideal (MonoidAlgebra R G) := (IsLocalRing.maximalIdeal R).comap (aug R G) with hJdef
  have hJ : J.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (aug R G) (UpperTheory.V.CF.augKer R G).2
  have huniq : ∃! I : Ideal (MonoidAlgebra R G), I.IsMaximal :=
    ⟨J, hJ, fun M hM => UpperTheory.V.CF.grMaxOf p R G hpm hG M hM⟩
  letI hloc : IsLocalRing (MonoidAlgebra R G) := IsLocalRing.of_unique_max_ideal huniq
  have hmax : IsLocalRing.maximalIdeal (MonoidAlgebra R G) = J :=
    (IsLocalRing.eq_maximalIdeal hJ).symm
  have hsec : ∀ r : R, aug R G (algebraMap R (MonoidAlgebra R G) r) = r := fun r => (aug R G).commutes r
  refine ⟨hloc, hmax, ?_, ?_⟩
  · rw [hmax]
    apply le_antisymm
    · intro x hx
      have hax : aug R G x ∈ IsLocalRing.maximalIdeal R := hx
      have h1 : algebraMap R (MonoidAlgebra R G) (aug R G x) ∈
          (IsLocalRing.maximalIdeal R).map (algebraMap R (MonoidAlgebra R G)) :=
        Ideal.mem_map_of_mem _ hax
      have h2 : x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G := by
        rw [← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker]
        show aug R G (x - algebraMap R (MonoidAlgebra R G) (aug R G x)) = 0
        rw [map_sub, hsec, sub_self]
      have : x = algebraMap R (MonoidAlgebra R G) (aug R G x) +
          (x - algebraMap R (MonoidAlgebra R G) (aug R G x)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    · apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        show aug R G (algebraMap R (MonoidAlgebra R G) r) ∈ IsLocalRing.maximalIdeal R
        rw [hsec]
        exact hr
      · intro x hx
        rw [← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker] at hx
        show aug R G x ∈ IsLocalRing.maximalIdeal R
        rw [show aug R G x = 0 from hx]
        exact zero_mem _
  · intro x
    constructor
    · intro hx
      exact hx.map (aug R G)
    · intro hx
      by_contra hnx
      have hxm : x ∈ IsLocalRing.maximalIdeal (MonoidAlgebra R G) := hnx
      rw [hmax] at hxm
      exact hxm hx
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.burnsideHom :
    ∀ (p : ℕ) [Fact p.Prime] (P : Type) [Group P] [Finite P], IsPGroup p P → ∀ K : Subgroup P, (∀ f : P →* Multiplicative (ZMod p), K ≤ f.ker → f = 1) → K = ⊤ := by
  intro p _ P _ _ hP K hK
  rcases IsCoatomic.eq_top_or_exists_le_coatom K with h | ⟨M, hM, hKM⟩
  · exact h
  exfalso
  obtain ⟨hMn, hMi, -⟩ := UpperTheory.V.CF.phiLe p P hP M hM
  have hcardQ : Nat.card (P ⧸ M) = p := by rw [← Subgroup.index_eq_card, hMi]
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by simp
  let e : (P ⧸ M) ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcardQ hcardZ
  let f : P →* Multiplicative (ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' M)
  have hKf : K ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have : (QuotientGroup.mk' M x) = 1 := (QuotientGroup.eq_one_iff x).mpr (hKM hx)
    show e (QuotientGroup.mk' M x) = 1
    rw [this, map_one]
  have hf1 := hK f hKf
  apply hM.1
  rw [eq_top_iff]
  intro x _
  have hx : f x = 1 := by rw [hf1]; rfl
  have : QuotientGroup.mk' M x = 1 := e.injective (by simpa [f] using hx)
  exact (QuotientGroup.eq_one_iff x).mp this
end
