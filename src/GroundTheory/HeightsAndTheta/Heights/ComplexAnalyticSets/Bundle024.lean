module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Height
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle009
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Kaehler.JacobiZariski

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalBoundedQuotient.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (F G : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ F N → DifferentiableOn ℂ G N →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    Bornology.IsBounded ((fun z => F z / G z) '' ((zeroSetIn I ∩ N) \ {z | G z = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ ∃ H : (σ → ℂ) → ℂ, DifferentiableOn ℂ H V ∧
      ∀ z ∈ zeroSetIn I ∩ V, F z = G z * H z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalGermIntegrallyClosed.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (F G : (σ → ℂ) → ℂ) (d : ℕ) (a : Fin d → (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ F N → DifferentiableOn ℂ G N → (∀ j, DifferentiableOn ℂ (a j) N) →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    (∀ z ∈ (zeroSetIn I ∩ N) \ {z | G z = 0},
      F z ^ d + ∑ j, a j z * F z ^ (j : ℕ) * G z ^ (d - (j : ℕ)) = 0) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ ∃ H : (σ → ℂ) → ℂ, DifferentiableOn ℂ H V ∧
      ∀ z ∈ zeroSetIn I ∩ V, F z = G z * H z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalZerosNowhereDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (G : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ G N → ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    ∃ U : Set (σ → ℂ), IsOpen U ∧ w ∈ U ∧ U ⊆ N ∧
      ∀ z ∈ zeroSetIn I ∩ U, ∀ V ∈ 𝓝 z, ∃ x ∈ zeroSetIn I ∩ V, G x ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def BranchFillDimension.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (k : ℕ) (r : ℝ) (φ : (Fin k → ℂ) → σ → ℂ) (B : Set (σ → ℂ)),
    I.IsPrime → h ∉ I → w ∈ zeroSetIn I →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (zeroSetIn I) → B ∈ 𝓝 w →
    (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.ball 0 r →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

def BranchOffHypersurface.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (b : MvPolynomial (Fin n) ℂ) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) → b ∉ J →
    IsOpen U → U.Nonempty → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn J) →
    ∃ t ∈ U, eval (φ t) b ≠ 0

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalModelDisc.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ r : ℝ, 0 < r ∧ ∃ φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ,
        DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧
          Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧ φ 0 = w

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def NormalModelOpenMapping.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : NormalModel J) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) →
    IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn M.ideal) →
    ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ φ '' U = zeroSetIn M.ideal ∩ O

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def NormalOpenMapping.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn I) →
    ∃ O : Set (σ → ℂ), IsOpen O ∧ φ '' U = zeroSetIn I ∩ O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def NormalModelProjectionLocallyInjective.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ U ∈ 𝓝 w, Set.InjOn IndefiniteRowSideFullHecke.ComplexSets.firstCoords (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def ProjectionInjectiveOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ),
    I.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧ ∀ z ∈ zeroSetIn I, eval z h ≠ 0 →
      ∃ W : Set (σ → ℂ), IsOpen W ∧ z ∈ W ∧
        ∃ A : (σ → ℂ) →L[ℂ] (Fin k → ℂ), Set.InjOn A (zeroSetIn I ∩ W)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

noncomputable section

theorem isDiscreteValuationRing_localization_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hbot : q ≠ ⊥ := by
    intro h
    rw [← Ideal.height_eq_zero_iff_eq_bot] at h
    rw [h] at hq
    exact zero_ne_one hq
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  have : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff, hdim]
    rfl
  have hnf : ¬ IsField (Localization.AtPrime q) := IsLocalization.AtPrime.not_isField A hbot _
  have huniq : ∃! P : Ideal (Localization.AtPrime q), P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨maximalIdeal (Localization.AtPrime q), ?_, fun P hP => ?_⟩
    · exact And.intro (isField_iff_maximalIdeal_eq.not.mp hnf) inferInstance
    have : P.IsPrime := hP.2
    exact IsLocalRing.eq_maximalIdeal (this.isMaximal_of_ne_bot hP.1)
  have h3 : IsIntegrallyClosed (Localization.AtPrime q) ∧
      ∃! P : Ideal (Localization.AtPrime q), P ≠ ⊥ ∧ P.IsPrime := And.intro inferInstance huniq
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 1 4).mpr h3

theorem NormalCodimOneUniformiser.proof : NormalCodimOneUniformiser.Statement := by
  intro σ _ P Q e x hP hQ hPQ hnorm hdimP hdimQ hxQ hxP
  let π : MvPolynomial σ ℂ →+* MvPolynomial σ ℂ ⧸ P := Ideal.Quotient.mk P
  have : IsDomain (MvPolynomial σ ℂ ⧸ P) := Ideal.Quotient.isDomain P
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  have : IsNoetherianRing (MvPolynomial σ ℂ ⧸ P) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial σ ℂ ⧸ P) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by rw [hdimP]; exact WithBot.natCast_ne_bot _, by
      rw [hdimP]
      rw [← WithBot.coe_natCast, Ne, WithBot.coe_eq_top]
      exact ENat.natCast_ne_top _⟩
  set q : Ideal (MvPolynomial σ ℂ ⧸ P) := Q.map π with hqdef
  have : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have hmem : ∀ r, π r ∈ q ↔ r ∈ Q := fun r => by
    rw [← Ideal.mem_comap, hqdef, Ideal.comap_map_mk hPQ]

  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial σ ℂ ⧸ P)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial σ ℂ ⧸ P)
    (fun M N hM hN => (hs M hM).trans (hs N hN).symm) q
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ), hdimQ, hdimP] at key
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q.height = n :=
    ⟨q.height.toNat, (ENat.natCast_toNat (Ideal.height_ne_top Ideal.IsPrime.ne_top')).symm⟩
  rw [hn] at key
  have hn1 : n = 1 := by
    have : ((e + n : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast key
    have : e + n = e + 1 := by exact_mod_cast this
    omega
  have hht : q.height = 1 := by rw [hn, hn1]; rfl

  have : IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) := hnorm
  have : IsDiscreteValuationRing (Localization.AtPrime q) :=
    isDiscreteValuationRing_localization_of_height_eq_one q hht
  have hinj : Function.Injective (algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q)) :=
    IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
  have hmax : ∀ y, algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) y ∈ maximalIdeal (Localization.AtPrime q) ↔ y ∈ q := fun y =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q y

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨a₀, s₀⟩, hs₀⟩ := IsLocalization.mk'_surjective q.primeCompl ϖ
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a₀
  have hgirr : Irreducible (algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π g)) := by
    have h1 : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π g) = ϖ * algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) s₀ := by
      rw [← hs₀]; exact (IsLocalization.mk'_spec (Localization.AtPrime q) (Ideal.Quotient.mk P g) s₀).symm
    rw [h1]
    exact (irreducible_mul_isUnit (IsLocalization.map_units (Localization.AtPrime q) s₀)).mpr hϖ
  have hgQ : g ∈ Q := by
    rw [← hmem, ← hmax, IsLocalRing.mem_maximalIdeal]
    exact hgirr.not_isUnit

  have hx0 : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π x) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q)), hinj.eq_iff]
    intro h
    exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := Localization.AtPrime q) hx0 hgirr
  have hxmax : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π x) ∈ maximalIdeal (Localization.AtPrime q) := (hmax _).mpr ((hmem x).mpr hxQ)
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero, mul_one] at hu
      rw [IsLocalRing.mem_maximalIdeal, hu] at hxmax
      exact absurd u.isUnit hxmax
    · exact h
  obtain ⟨⟨c, d⟩, hcd⟩ := IsLocalization.mk'_surjective q.primeCompl (u : (Localization.AtPrime q))
  have hcu : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) c = (u : (Localization.AtPrime q)) * algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) d := by
    rw [← hcd]; exact (IsLocalization.mk'_spec (Localization.AtPrime q) c d).symm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (d : MvPolynomial σ ℂ ⧸ P)
  have haQ : a ∉ Q := by
    rw [← hmem, ← hmax, IsLocalRing.mem_maximalIdeal, hcu]
    exact fun h => h ((u.isUnit).mul (IsLocalization.map_units (Localization.AtPrime q) d))
  have hbQ : b ∉ Q := by
    rw [← hmem]
    change Ideal.Quotient.mk P b ∈ q → False
    rw [hb]
    exact d.2
  have hrel : b * x - a * g ^ k ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change π (b * x - a * g ^ k) = 0
    apply hinj
    simp only [map_zero, map_sub, map_mul, map_pow]
    change algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (Ideal.Quotient.mk P b) * _ - algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (Ideal.Quotient.mk P a) * _ = 0
    rw [hb, hcu, hu]
    ring

  have hunif := (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := Localization.AtPrime q) _).mp hgirr
  have hgen : ∀ p ∈ Q, ∃ t : MvPolynomial σ ℂ, t ∉ Q ∧ t * p ∈ P ⊔ Ideal.span {g} := by
    intro p hp
    have hpm : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π p) ∈ maximalIdeal (Localization.AtPrime q) := (hmax _).mpr ((hmem p).mpr hp)
    rw [hunif] at hpm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hpm
    obtain ⟨⟨c', d'⟩, hcd'⟩ := IsLocalization.mk'_surjective q.primeCompl y
    obtain ⟨c₁, rfl⟩ := Ideal.Quotient.mk_surjective c'
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (d' : MvPolynomial σ ℂ ⧸ P)
    refine ⟨t, ?_, ?_⟩
    · rw [← hmem]
      change Ideal.Quotient.mk P t ∈ q → False
      rw [ht]
      exact d'.2
    · have hrel' : t * p - c₁ * g ∈ P := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change π (t * p - c₁ * g) = 0
        apply hinj
        simp only [map_zero, map_sub, map_mul]
        change algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (Ideal.Quotient.mk P t) * _ - _ = 0
        have hspec : IsLocalization.mk' (Localization.AtPrime q) (Ideal.Quotient.mk P c₁) d' *
            algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) d' =
            algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π c₁) :=
          IsLocalization.mk'_spec _ _ _
        dsimp only at hcd'
        rw [ht, ← hy, ← hcd', ← hspec]
        ring
      have : t * p = (t * p - c₁ * g) + c₁ * g := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left hrel')
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian Q : Q.FG)
  have hgenS : ∀ y ∈ S, ∃ t : MvPolynomial σ ℂ, t ∉ Q ∧ t * y ∈ P ⊔ Ideal.span {g} := fun y hy =>
    hgen y (hS ▸ Submodule.subset_span hy)
  choose! T hTQ hT using hgenS
  refine ⟨g, a, b, ∏ y ∈ S, T y, k, hgQ, hk, haQ, hbQ, ?_, hrel, fun p hp => ⟨1, ?_⟩⟩
  · rw [hQ.prod_mem_iff]
    rintro ⟨y, hy, h⟩
    exact hTQ y hy h
  · rw [pow_one]
    rw [← hS] at hp
    induction hp using Submodule.span_induction with
    | mem y hy =>
      rw [← Finset.prod_erase_mul S T hy, mul_assoc]
      exact Ideal.mul_mem_left _ _ (hT y hy)
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ r hy

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open KaehlerDifferential TensorProduct

theorem PolyKaehlerFree.proof : PolyKaehlerFree.Statement := by
  intro R k _ _ _ n
  set B := MvPolynomial (Fin n) k

  have hinj : Function.Injective (mapBaseChange R k B) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R k B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hex := exact_mapBaseChange_map R k B

  obtain ⟨l, hl⟩ := Module.projective_lifting_property ((map R k B B).restrictScalars B)
    LinearMap.id (map_surjective R k B)
  let e := ((hex.splitSurjectiveEquiv hinj) ⟨l, hl⟩).1
  have : Module.Free B Ω[B⁄k] := Module.Free.of_basis (mvPolynomialBasis k (Fin n))
  exact Module.Free.of_equiv e.symm
end ComplexSets
end IndefiniteRowSideFullHecke
end Heights
end Heights₂
end GroundTheory
end
