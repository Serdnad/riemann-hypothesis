module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.AbW
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BcPolar

theorem exists_sign_twist {K : Type} [Field K] [NumberField K] [IsCMField K] (χ : HChar (maximalRealSubfield K))
    (h : ∀ v v' : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = χ.locInf v' (-1)) (b : ℤ) :
    ∃ k : ℕ, ∀ v, (χ * quadChar K ^ k).locInf v (-1) = (-1) ^ b := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have hval : ∀ (k : ℕ) v, (χ * quadChar K ^ k).locInf v (-1) = χ.locInf v₀ (-1) * (-1) ^ k := fun k v => by
    change χ.locInf v (-1) * (quadChar K ^ k).locInf v (-1) = _
    rw [locInf_pow, quadChar_locInf, h v v₀]
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  simp only [hval, Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_neg,
    Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e <;> rcases Int.even_or_odd b with hb' | hb' <;> rw [e, hb'.neg_one_zpow]
  · exact ⟨0, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨0, fun _ => by simp⟩

end GlobalTheory.BcPolar
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealGal

theorem exists_hodgeTate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (hπ : π.IsRegAlg) (v : InfinitePlace F) :
    ∃ H : Multiset ℤ, ∃ m, π.HasInfChar v m ∧
      H.map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z := by
  obtain ⟨m, hm, -, hz⟩ := hπ v
  refine ⟨m.attach.map fun z => -(hz z.1 z.2).choose, m, hm, ?_⟩
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.attach_map_val m, Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  have h := (hz z.1 z.2).choose_spec
  simp only [Function.comp_apply, Int.cast_neg]
  linear_combination h

theorem complexConj_algebraMap {F K : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
    [IsCMField K] [Algebra F K] (x : F) :
    IsCMField.complexConj K (algebraMap F K x) = algebraMap F K x := by
  rw [IsCMField.complexConj_eq_self_iff, mem_maximalRealSubfield_iff]
  intro φ
  have h := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp
    (IsTotallyReal.isReal (InfinitePlace.mk (φ.comp (algebraMap F K)))))
  rw [RCLike.star_def, ← ComplexEmbedding.conjugate_coe_eq]
  exact RingHom.congr_fun h x

end GlobalTheory.RealGal

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeMultOne

theorem main : ∀ (F : Type) [Field F] [NumberField F] (η η' : HChar F), (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧ η'.UnrAt v ∧ η.val v = η'.val v) → η = η' := by
  intro F _ _ η η' h
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.mp h).toFinset with hS
  have key : η * η'⁻¹ = 1 := by
    refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away (η * η'⁻¹).1 (η * η'⁻¹).2.1 (η * η'⁻¹).2.2 S fun v hv => ?_)
    have hv' : η.UnrAt v ∧ η'.UnrAt v ∧ η.val v = η'.val v := by
      by_contra hc
      exact hv (by rw [hS, Set.Finite.mem_toFinset]; exact hc)
    obtain ⟨h1, h2, h3⟩ := hv'
    intro x
    refine GlobalTheory.FrobDense.eq_one_of_unif ((η * η'⁻¹).loc v) (fun y hy => ?_) x
    change η.loc v y * (η'.loc v y)⁻¹ = 1
    rw [η.val_eq h1 y hy, η'.val_eq h2 y hy, h3, mul_inv_cancel]
  exact mul_inv_eq_one.mp key

end GlobalTheory.HeckeMultOne
end
