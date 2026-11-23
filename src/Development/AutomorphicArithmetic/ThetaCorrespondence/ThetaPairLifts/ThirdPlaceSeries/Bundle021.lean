module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle713
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltMore
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle096
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle126
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle020
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem unrCrysAtRangePrime_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (X : KillingConditions.HubData D), (∀ i, GoodR D.nd i (X.r i)) → SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → ∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i)) ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), C.IsGood → ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) := by
  intro hF D L X hgood ht0 ha2 ha5 hG2 hpar hmu i _ hg hR _
  obtain ⟨h23, hqd, -⟩ := hR
  have hchi := _root_.GlobalTheory.T.chiOne_of_not_mem_gset hF D ht0 ha2 ha5 hpar hmu i hg
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  refine ⟨GlobalTheory.T.hostCompletion_le_maxUnramified_padic D i (fun h => h23 (Or.inl h)) (fun h => hqd (Or.inl h)) (fun h => hqd (Or.inr h)), ?_⟩
  intro w hw C _ x
  exact _root_.GlobalTheory.T.isCrys_locC_of_chiOneE hF D i (X.r i) (hgood i) (hG2 i (X.r i) (hgood i)) hg0 hg1 hchi w hw C x
end GlobalTheory.HubX
end
end

section



section
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem unitarySphericalComponent_of_reading_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A)
      (S : Reading T), _root_.GlobalTheory.SplitRead.LawsAlt S → RowUnit S → GlobalTheory.RowSatakeBound.UnitarySphericalComponent N A := by
  intro hBZ R H what₂ N A T S hL hU i σ hσ w hw hu
  have hloc := (S i w hw).locW σ hσ
  have hsph : IsSpherical ((S i w hw).row σ).π := by
    rw [← (hL i w hw).sph _ _, ← hloc, ← T.unr]
    exact hu
  obtain ⟨α, hα⟩ := GlobalTheory.T.sphericalRepGL_exists_satakeParameters hBZ _ _ _ hsph
  have hfrob : A.frobEig (A.locW i σ w) =
      (Finset.univ.val.map fun j => (α j : ℂ)).map (·⁻¹) := by
    rw [T.frobEig w _ hu, hloc, (hL i w hw).sat _ _ α hα, Multiset.map_map]
    simp
  have h1 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w R.r (Finset.univ.val.map fun j => (α j : ℂ)) :=
    GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake H.E w R.r _ α hα (hU i w hw σ hσ)
  rw [hfrob]
  refine ⟨?_, ?_⟩
  · simpa [Multiset.map_map, Function.comp_def] using h1
  · have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.T.isUnitarySphericalSatakeMultiset_map_inv _ _ _ _ h1
end GlobalTheory.SplitRead
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.fontaine_quotient_degrees_of_ptFam : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → AdmissibleParameterJ.ConclusionJa D → ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ := by
  first | exact @_root_.GlobalTheory.HubFon.main_alt_alt | exact _root_.GlobalTheory.HubFon.main_alt_alt | (intros; apply _root_.GlobalTheory.HubFon.main_alt_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory
theorem pointInputAwayFromTypePrimes_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.PtCore.PtFam D X.r X.ρ → _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, GlobalTheory.HTW.RecS.PtIn i (X.r i) (X.ρ i) π := by
  intro hF D X hX hG i hl π hπ
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π := by
    obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  have h0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have h1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  exact ⟨hX.good i, fun x => (hX.good i x).1, hZ, hd, hX.cont i π, fun w hw C x =>
    ((_root_.GlobalTheory.T.semisimple_decomposition_of_good_galois_local hF D i _ _ π (hX.good i) (hG i _ (hX.good i)) h0 h1 hd w hw C).2 x).2⟩
end GlobalTheory
end
end
