module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex

@[expose] public section

noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

variable {F : Type} [Field F] [NumberField F]

theorem psiUnr_of_not_le {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) : PsiUnr ψ v := by
  apply _root_.GlobalTheory.StdCharUnrF.psiUnr_of_not_le <;> assumption

end PositivityTheory.Mix
