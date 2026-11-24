module

public import Formalism.ConjugateSelfDual.Statement
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.MainNotions.V.Pf.ShaCmp

variable {K Ω' : Type*} [Field K] [NumberField K] [Field Ω'] [Algebra K Ω'] (A : ValuationSubring Ω')

theorem val_le_one (x : 𝓞 K) : A.valuation (algebraMap K Ω' (x : K)) ≤ 1 := by
  have hx : IsIntegral ℤ (algebraMap K Ω' (x : K)) :=
    (x.2.map (IsScalarTower.toAlgHom ℤ K Ω'))
  have hA : IsIntegral A (algebraMap K Ω' (x : K)) := hx.tower_top
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hA
  rw [← ha]
  exact (A.valuation_le_one_iff _).mpr a.2

def ltIdeal : Ideal (𝓞 K) :=
  (IsLocalRing.maximalIdeal A).comap
    (((algebraMap K Ω').comp (algebraMap (𝓞 K) K)).codRestrict A
      fun x => A.mem_of_valuation_le_one _ (val_le_one A x))

theorem mem_ltIdeal (x : 𝓞 K) : x ∈ ltIdeal (K := K) A ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 :=
  A.valuation_lt_one_iff _

theorem exists_over_iff : (∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v) ↔
    ∃ n : ℕ, 0 < n ∧ A.valuation (n : Ω') < 1 := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩
    have h1 := (hv (Ideal.absNorm v.asIdeal : 𝓞 K)).mpr (Ideal.absNorm_mem v.asIdeal)
    simpa using h1
  · rintro ⟨n, hn, hv⟩
    have hP : (ltIdeal (K := K) A).IsPrime := Ideal.comap_isPrime _ _
    have hne : ltIdeal (K := K) A ≠ ⊥ := by
      intro h
      have h1 : ((n : ℕ) : 𝓞 K) ∈ ltIdeal (K := K) A := by
        rw [mem_ltIdeal]; simpa using hv
      rw [h, Ideal.mem_bot] at h1
      exact (Nat.cast_ne_zero.mpr hn.ne') h1
    exact ⟨⟨ltIdeal A, hP, hne⟩, fun x => (mem_ltIdeal A x).symm⟩

end Formalism.MainNotions.V.Pf.ShaCmp
