module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.CBC.STwSat_holds : UpperTheory.CBC.STwSat := by
  intro F _ _ n π η
  filter_upwards [(GlobalTheory.Mem.UnrAe.finite_ramified η).compl_mem_cofinite] with v hv
  have hu : η.UnrAt v := not_not.mp hv
  refine ⟨hu, fun B hB => ?_⟩
  cases π with
  | cx π => exact GlobalTheory.SphGal.hasSatGL_twist F n π η v B hu hB
  | re π => exact UpperTheory.V.TR.CuspSub.HasSat.twist hB hu
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

private theorem UpperTheory.CBC.NormPowerUnderPlace.normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (w : HeightOneSpectrum (𝓞 K')) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem UpperTheory.CBC.SNormPow_holds : UpperTheory.CBC.SNormPow := by
  intro K M _ _ _ _ _ w
  exact ⟨_, UpperTheory.CBC.NormPowerUnderPlace.normV_under (K := K) w⟩
end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.CBC

theorem SIsoSat_holds : SIsoSat := by
  intro F _ _ n π π' h w B hB
  cases π with
  | cx p =>
    cases π' with
    | cx p' =>
      exact (GlobalTheory.CuspRep.CG.hasSat_mk p' w B).2
        (GlobalTheory.CuspRep.CuspSub.Iso.hasSatGL (π := p) (π' := p') h ((GlobalTheory.CuspRep.CG.hasSat_mk p w B).1 hB))
    | re p' => exact h.elim
  | re p =>
    cases π' with
    | cx p' => exact h.elim
    | re p' => exact UpperTheory.V.TR.CuspSub.Iso.hasSat (π := p) (π' := p') h hB

end UpperTheory.CBC
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.CBC.SCuspOf_holds : UpperTheory.CBC.SCuspOf := by
  intro F _ _ n sat inf h
  rcases h with ⟨hC, π, rfl, rfl⟩ | ⟨hR, π, rfl, rfl⟩
  · exact ⟨.cx π, rfl, rfl⟩
  · exact ⟨.re π, rfl, rfl⟩

theorem UpperTheory.CBC.SIsCusp_holds : UpperTheory.CBC.SIsCusp := by
  intro F _ _ n π
  cases π with
  | cx π => exact Or.inl ⟨inferInstance, π, rfl, rfl⟩
  | re π => exact Or.inr ⟨inferInstance, π, rfl, rfl⟩

theorem UpperTheory.CBC.SSatUniq_holds : UpperTheory.CBC.SSatUniq := by
  intro F _ _ n π v B B' h h'
  cases π with
  | cx π => exact CG.HasSat.unique (π := CG.mk π) (w := v) h h'
  | re π => exact UpperTheory.V.TR.CuspSub.HasSat.unique (π := π) (w := v) h h'
end
end
