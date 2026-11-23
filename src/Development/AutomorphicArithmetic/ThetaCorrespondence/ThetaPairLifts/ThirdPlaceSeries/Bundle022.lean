module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle412
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle444
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle697
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle004
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle740
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle457
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle018
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011

@[expose] public section

section



section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
end Formalism.MainNotions.N
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open GlobalTheory.RestPtAssembly in
theorem GlobalTheory.restPt_of_ptFam_aux41_oSplit : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, RestPt i (r i) (ρ i) π := by
  intro hF D r ρ hP h41 hO i hl π hπ
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hZ : π ∈ D.nd.Z i := by
    have hx := hπ
    rw [D.Z_tie]
    rw [D.Zgood_tie] at hx
    exact hx.1
  obtain ⟨hrho, hss, hblock, hdec⟩ := GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D r ρ hP i π hZ
  obtain ⟨hshape, heps⟩ := GlobalTheory.T.admissible_shape_and_epsilon_at_every_localisation D i
  have hG2 := ((h41 i).2.2 _ (hP.good i)).2.1
  have hX := _root_.GlobalTheory.T.semisimple_decomposition_of_good_galois_local hF D i (r i) (ρ i) π (hP.good i) hG2 hg0 hg1 hdec
  exact
    { ng0 := hg0
      ng1 := hg1
      good := hP.good i
      chi1 := fun w hw C => (hX w hw C).1
      block := hblock
      chi := fun w hw C c h1 h2 => chiRat_isCrys D i w hw C c h1 h2
      g3 := UpperTheory.GalS.jointCondition_of_constituentCondition_split D i _ (hP.good i) ((_root_.UpperTheory.GalS.g3' ((h41 i).2.2 _ (hP.good i)).2.2.1).1 (Or.inl ⟨hg0, hg1⟩)) (hO i)
      cont := hP.cont i π
      rho := hrho
      ss := hss
      eps := heps
      shape := hshape }
end
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
noncomputable section
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.GTwoTheta
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
end GlobalTheory.GTwoTheta
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
end GlobalTheory.GTwoTheta
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
end GlobalTheory.GTwoTheta
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π := by
  intro hF D L hG2 hJa hJc i r ρ π hr h0 h1 hπ hD w hw C
  obtain ⟨ep, hJ⟩ := hJa
  have hcrys := _root_.GlobalTheory.CrysFromGTwo.main_alt_alt hF D i r ρ π hr (hG2 i r hr) h0 h1 hD w hw C
  have hamb := GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i r ρ π hD hπ h0 h1 w hw C
  have hH := twistedRep_no_invariants_purity D L ep hJ hJc i r ρ π hr hπ w hw C hD (hcrys.2 π).2
  refine ⟨⟨fun x => (hcrys.2 x).1, fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).1,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.1,
    fun c hc1 hct τ a => chi_jump D i r ρ π w hw C (fun τ => (hamb τ).2) c hc1 hct τ a,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.2, hH.1, hH.2⟩, fun x => ?_⟩
  rw [← locC_rTwO]
  exact (hcrys.2 x).2
end GlobalTheory.GTwoTheta
end
end
end
