module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Commutator.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle456
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.GaloisStatementWeakOfFull
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

namespace UpperTheory.GalS

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (E →+* Qbar l) → Multiset ℤ} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

omit [IsCMField E] in
theorem Aw.eq_unr {h : IsPlaceOver A w} {x y : WD h} (k : Aw x y) (hy : y.unr) : x = y := k.unr hy


end UpperTheory.GalS
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial
open GlobalTheory.TypeAbove

noncomputable section

namespace UpperTheory.GalS

open UpperTheory.Lit.Car (IneAb comm_le_ine)

theorem comm_triv {G : Type} [Group G] (I : Subgroup G) (φ : G → ℂ) (h1 : φ 1 = 1)
    (hm : ∀ a ∈ I, ∀ b ∈ I, φ (a * b) = φ a * φ b) : ∀ σ ∈ ⁅I, I⁆, φ σ = 1 := by
  have hinv : ∀ a ∈ I, φ a * φ a⁻¹ = 1 := fun a ha => by
    rw [← hm a ha a⁻¹ (I.inv_mem ha), mul_inv_cancel, h1]
  let K : Subgroup G :=
    { carrier := {x | x ∈ I ∧ φ x = 1}
      mul_mem' := fun {x y} hx hy => ⟨I.mul_mem hx.1 hy.1, by rw [hm x hx.1 y hy.1, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨I.one_mem, h1⟩
      inv_mem' := fun {x} hx => ⟨I.inv_mem hx.1, by simpa [hx.2] using hinv x hx.1⟩ }
  have hle : ⁅I, I⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨I.mul_mem (I.mul_mem (I.mul_mem ha hb) (I.inv_mem ha)) (I.inv_mem hb), ?_⟩
    rw [commutatorElement_def, hm _ (I.mul_mem (I.mul_mem ha hb) (I.inv_mem ha)) _ (I.inv_mem hb),
      hm _ (I.mul_mem ha hb) _ (I.inv_mem ha), hm a ha b hb]
    linear_combination φ b * φ b⁻¹ * hinv a ha + hinv b hb
  exact fun σ hσ => (hle hσ).2

end UpperTheory.GalS

end
end
