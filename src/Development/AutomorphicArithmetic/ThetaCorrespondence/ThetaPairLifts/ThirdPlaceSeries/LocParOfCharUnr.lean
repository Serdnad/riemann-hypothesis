module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRecordCgTrueT
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
section CharUnr
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
theorem locPar_ofChar_unr_and_frobEig (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).unr ∧
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} :=
  _root_.GlobalTheory.HeightCounting.locParT_unr hL χ h hu
end CharUnr
section Twist
end Twist
section G
end G
end GlobalTheory.HodgeOfTrue
end
end
