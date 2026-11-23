module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle166
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle235
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle060
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.NotRealComplex
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle523
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle114
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.NormVUnderPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.LimitEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

open GlobalTheory.WeakBaseChange in
theorem UpperTheory.Gal.NearKilling.weakRes :
    WeakRes := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι a π P hL r hr
  obtain ⟨hc, hss, hatt⟩ := hr
  refine ⟨hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom E M Ω), ?_, ?_⟩
  · haveI := finiteIndex_range_res E M Ω
    set H := (UpperTheory.V.Af.Bc.res E Ω M).range with hH
    haveI : (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).FiniteIndex := finiteIndex_comap _ _
    refine isSSRep_of_finiteIndex _ (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)) ?_
    have hrange : ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype).range = H.normalCore := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        obtain ⟨y, hy⟩ := (Subgroup.normalCore_le H hx : x ∈ (UpperTheory.V.Af.Bc.res E Ω M).range)
        exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hx⟩, hy⟩
    have := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype)
      (by rw [hrange]; exact Subgroup.normalCore_normal H) hss
    rwa [MonoidHom.comp_assoc]
  · unfold UpperTheory.V.Published.WeakBC at hL
    filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E M).eventually hatt, hL] with w h hW
    obtain ⟨B, hB, hF⟩ := h
    have h2 := GlobalTheory.AttResTower.normV_under_pow (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    obtain ⟨B', hB', hP⟩ := hW f h2
    have hBB : B' = B := GlobalTheory.T.cuspRep_satakeParameters_unique E a (CG.mk π) (w.under (𝓞 E)) B' B hB' hB
    subst hBB
    refine ⟨B'.map (· ^ f), hP, ?_⟩
    have h3 := (UpperTheory.frobenius_power_compatibility E M Ω l ι w f h2).1 a r _ hF
    rw [h2, algSat_pow]
    exact h3
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

theorem UpperTheory.Gal.NearKilling.stepLift :
    UpperTheory.V.Z.Bc.CBCc → UpperTheory.Gal.UnramifiedFromSplittingCriterion.NoSelfTwist → PolBC → WeakRes → StepLift := by
  intro hC hN hP hW K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l a _ ha π χ hs A v hv hτ hsat
  obtain ⟨hreg, hpol, -⟩ := hs
  have hK : IsTotallyComplex K := inferInstance
  have hM : IsTotallyComplex M := inferInstance
  rcases (hC K M hp hK a ha).1 (.cx π) with ⟨η, hη, hi⟩ | ⟨Q, hw, hinf, hsplit⟩
  · exfalso
    obtain ⟨B, hB⟩ := hsat
    refine hN K M Ω hp A v hv hτ a ha (CG.mk π) B hB η hη ?_
    rw [CG.twist_mk]
    exact Quotient.sound hi
  · cases Q with
    | re Q => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex M inferInstance hM).elim
    | cx P =>
      have hw' : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat := hw
      obtain ⟨⟨χ', hχ'⟩, hq⟩ := hP K M a ha π P χ hpol hw'
      refine ⟨P, χ', hw, hsplit, ⟨?_, hχ', trivial⟩, hq, fun ι r hr => hW K M Ω l ι a π P hw' r hr⟩
      refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
      have h1 := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) (τ.comp (algebraMap K M))
      have h2 : P.HasInfChar τ ((CG.mk π).infChar (τ.comp (algebraMap K M))) := hinf τ _ h1
      have h3 : (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M)) :=
        CG.HasInfChar.infChar_eq h2
      rw [h3]
      exact hreg _
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G Dec IsPlaceOver
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem dec_restrict {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] {A : ValuationSubring Ω} {g : G K Ω} (hg : g ∈ Dec (F := K) A) :
    AlgEquiv.restrictScalars F g ∈ Dec (F := F) A :=
  GlobalTheory.FunExt.ConjLift.mem_Dec_of_iff fun x => apply_mem_iff_of_mem_Dec hg x

private def Carry {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ)
    [Fact l.Prime] (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E))) (X : UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fld E Ω) : Prop :=
  ∃ (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
    UpperTheory.Gal.InertialTypesAlt.Lifts (UpperTheory.Gal.InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : UpperTheory.Gal.InertialTypesAlt.Pt E Ω a) ∧ InScope .all l P χ' ∧
    (∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))) ∧
    ∀ u ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A u → (∀ g ∈ Dec (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) →
      ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → ∃ B, (CG.mk P).HasSat w' B

theorem UpperTheory.Gal.NearKilling.allLift :
    StepLift → UpperTheory.Gal.UnramifiedFromSplittingCriterion.SatSplit → AllLift := by
  intro hStep hSat E Ω _ _ _ _ _ _ l a _ ha π χ hχ S hS X hX
  suffices H : Carry l a π S X by
    obtain ⟨P, χ', h1, h2, h3, -⟩ := H
    exact ⟨P, χ', h1, h2, h3⟩
  refine UpperTheory.Gal.UnramifiedFromSplittingCriterion.Tower.induction (S := S) (P := Carry l a π S) ?_ ?_ hX
  · refine ⟨π, χ, Relation.ReflTransGen.refl, hχ, fun ι r h => ?_, fun u hu A hA _ w' hw' => ?_⟩
    · exact h
    · have e : w' = u := HeightOneSpectrum.ext (Ideal.ext fun x => (hw' x).symm.trans (hA x))
      rw [e]
      exact hS u hu
  · rintro X Y - ⟨alg, t1, t2, hG, hp, u, hu, hsp, A, hA, τ, hτ, hτn⟩ ⟨P, χ', h1, h2, h3, h4⟩
    obtain ⟨v, hv, -⟩ := GlobalTheory.AboveL.exists_isPlaceOver_of_tower E X.K Ω A u hA
    have hfix : ∀ g ∈ Dec (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g := fun g hg =>
      (hsp A hA (AlgEquiv.restrictScalars _ g) (dec_restrict hg)).2
    obtain ⟨P', χ'', hbc, hsl, hsc, -, hweak⟩ :=
      hStep X.K Y.K Ω hp l a ha P χ' h2 A v hv ⟨τ, hτ, hτn⟩ (h4 u hu A hA hfix v hv)
    refine ⟨P', χ'', Relation.ReflTransGen.tail h1 ⟨alg, t2, hG, hp, hbc⟩, hsc, fun ι r h => ?_, ?_⟩
    · exact hweak ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K)) (h3 ι r h)
    · intro u' hu' A' hA' hfix' w' hw'
      have hv' : IsPlaceOver A' (w'.under (𝓞 X.K)) := fun x => by
        rw [IsScalarTower.algebraMap_apply X.K Y.K Ω]
        exact hw' (algebraMap (𝓞 X.K) (𝓞 Y.K) x)
      have hfixX : ∀ g ∈ Dec (F := E) A', UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g := fun g hg x => by
        have := hfix' g hg (algebraMap X.K Y.K x)
        rwa [← IsScalarTower.algebraMap_apply] at this
      obtain ⟨B, hB⟩ := h4 u' hu' A' hA' hfixX _ hv'
      exact ⟨B, hSat X.K Y.K Ω A' _ w' hv' hw' (fun g hg => hfix' _ (dec_restrict hg)) a P P' hsl B hB⟩
end
