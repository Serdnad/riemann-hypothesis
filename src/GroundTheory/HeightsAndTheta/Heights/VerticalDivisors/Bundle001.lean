module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.RingHom.Flat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

def DerivSpanTrdeg.Statement : Prop :=
  ∀ (k L : Type) [Field k] [PerfectField k] [Field L] [Algebra k L] (ι : Type) [Fintype ι]
    (z : ι → L) (e : ℕ),
    Algebra.trdeg k (Algebra.adjoin k (Set.range z)) ≤ (e : Cardinal) →
    ∃ r ≤ e, ∃ b : Fin r → ι → IntermediateField.adjoin k (Set.range z),
      ∀ D : Derivation k L L, ∃ c : Fin r → L, ∀ j, D (z j) = ∑ m, c m * (b m j : L)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def GenericFormsKer.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] [Algebra F L] (ι : Type) [Fintype ι] (e r : ℕ), r ≤ e →
    ∀ (u : Fin e × ι → L), AlgebraicIndependent F u →
    ∀ (b : Fin r → ι → F) (c : Fin r → L),
      (∀ i : Fin e, ∑ j, u (i, j) * ∑ m, c m * algebraMap F L (b m j) = 0) →
      ∀ j, ∑ m, c m * algebraMap F L (b m j) = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

def FibreCompDim.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)) (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        ringKrullDim (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸
            W.map (MvPolynomial.map (algebraMap O v.asIdeal.ResidueField))) =
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F)))

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

def FibreClosedComponent.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)) (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        W.IsMaximal →
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) = 0

def FibreCut.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O))
    (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        ¬ W.IsMaximal →
          ∃ (P' W' : Ideal (MvPolynomial (Fin n) O)) (f : MvPolynomial (Fin n) O),
            f ∉ P ∧ P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧
            P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ ∧
            W' ∈ (P' ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes ∧
            ringKrullDim (MvPolynomial (Fin n) O ⧸ W') + 1 = ringKrullDim (MvPolynomial (Fin n) O ⧸ W)

def GenericFibreDrop.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P P' : Ideal (MvPolynomial (Fin n) O))
    (f : MvPolynomial (Fin n) O),
    P.IsPrime → P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ → f ∉ P →
      P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes →
        ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) =
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P'.map (MvPolynomial.map (algebraMap O F))) + 1

def CodimOnePrimeAvoid.Statement : Prop :=
  ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (h : B),
    h ≠ 0 → 1 ≤ ringKrullDim B →
      ∃ N : Ideal B, N.IsPrime ∧ h ∉ N ∧ ringKrullDim (B ⧸ N) + 1 = ringKrullDim B

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

def FiniteOrd.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (b : B), Function.Injective (fun x : B => b * x) →
      ∀ 𝔫 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔫.asIdeal) (algebraMap B (Localization.AtPrime 𝔫.asIdeal) b) ≠ ⊤

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

namespace SpecChart

variable {A : Type*} [CommRing A] (W : Ideal A) [W.IsPrime] (P : Ideal A)

theorem isLocalization_quot :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P))
      (Localization.AtPrime W ⧸ P.map (algebraMap A (Localization.AtPrime W))) := by
  rw [_root_.isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, s, hs, rfl⟩
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact (IsLocalization.map_units (Localization.AtPrime W) (⟨s, hs⟩ : W.primeCompl)).map _
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk P a, ⟨_, s.1, s.2, rfl⟩⟩, ?_⟩
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, ← map_mul, IsLocalization.mk'_spec]
  · intro x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.eq, ← map_sub, IsLocalization.mem_map_algebraMap_iff W.primeCompl] at h
    obtain ⟨⟨⟨p, hp⟩, ⟨t, ht⟩⟩, h⟩ := h
    simp only at h
    rw [← map_mul, IsLocalization.eq_iff_exists W.primeCompl] at h
    obtain ⟨⟨u, hu⟩, h⟩ := h
    refine ⟨⟨Ideal.Quotient.mk P (u * t), ⟨u * t, W.primeCompl.mul_mem hu ht, rfl⟩⟩, ?_⟩
    simp only
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
    have h' : u * ((a - b) * t) = u * p := h
    rw [show u * t * (a - b) = u * ((a - b) * t) by ring, h']
    exact P.mul_mem_left _ hp

theorem flat_of_isLocalization_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (g : S →+* T) (hg : (g.comp (algebraMap R S)).Flat) :
    g.Flat := by
  letI := g.toAlgebra
  letI : Algebra R T := (g.comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.flat_iff_of_isLocalization S M T).mpr hg

end SpecChart

end

end GroundTheory.Heights₂.Heights.Vertical
end
