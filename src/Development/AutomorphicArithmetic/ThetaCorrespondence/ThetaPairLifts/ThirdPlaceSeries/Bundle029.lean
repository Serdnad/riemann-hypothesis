module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcAll
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle405
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFMonoLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle244
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle723
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle014
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle028
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle006
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PotentialCrystallinity.ModularityOfHyps
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.EigTie
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.MainNotions.IntegralHeckeForms (HkIdx V0 Fm0 eG Eigsp)
open Formalism.MainNotions.BlochKatoReduction.Gen (goodE Tmat eps0 chiS)
open Formalism.L2.Host (HChar CharFrame embLL0)
open GlobalTheory.Triple (Reading embSide muBase heckeVal IsParam IsResidual FbAt jIdx)
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
open scoped TensorProduct
variable {D : D7}
section Sys
variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)
variable {Y} {i : X.Tw} {j : ℕ} {b : Bool}
end Sys
section Read
variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)
variable {X} {i : X.Tw} {b : Bool}
end Read
section Par
variable (C : CharFrame D) (Rw : RowSide D) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X)
variable {C Rw Y} {i : X.Tw} {b : Bool}
end Par
section Res
variable (Rw : RowSide D)
def ReductionConditionAtPlace {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  IsoInduces ι w ∧ TeichAt ι w red ∧
    ∀ σ π (r : GalE D →* GL (Fin D.R.r) (Qbar l)), D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      _root_.UpperTheory.GalS.IsGaloisRepOfN D π l ι r → IsResidual ι r σ w red
end Res
def ResTiedAlt (D : D7) (Rw : RowSide D) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ (l : ℕ) [Fact l.Prime], D.what₂.places.resChar w = l →
    ∃ (ι : Qbar l ≃+* ℂ) (red : Zbar l →+* FbAt D w), _root_.GlobalTheory.EigTie.ReductionConditionAtPlace Rw ι w red
section Bridge
variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}
theorem ResTiedAlt.exists_reading {Rw : RowSide D} (h : _root_.GlobalTheory.EigTie.ResTiedAlt D Rw) (hs : ∀ x : ↥D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hi : X.NonzeroIndexPlace i) (b : Bool) :
    ∃ (ρ : Reading X i b) (w : D.what₂.places.Pl) (red : Zbar (X.l i) →+* FbAt D w), ρ.Induces w ∧ _root_.GlobalTheory.EigTie.ReductionConditionAtPlace Rw ρ.ι w red := by
  obtain ⟨w, hw, H⟩ := hi
  obtain ⟨ρ⟩ := Reading.nonempty (X := X) i true
  have hl : 0 < D.what₂.places.val w ((X.l i : ℕ) : D.what₂.LL) := by
    have := (H ((X.l i : ℕ) : 𝓞 ↥D.LL0)).1 ((norm_lt_iff ρ _).2 (by
      rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast, map_natCast,
        ← map_natCast (algebraMap ℚ_[X.l i] (Qbar (X.l i))), norm_algebraMap']
      exact Padic.norm_p_lt_one))
    simpa using this
  obtain ⟨ι, red, hι⟩ := h w hw (X.l i) (resChar_eq (X.lPrime i).out hl)
  have key : ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w x ↔ ‖ρ.κ (X.emb0 i x)‖ ≤ 1 := fun x =>
    (hι.1 x).trans (ball_of_int (ι.symm.toRingHom.comp (embLL0 D)) (ρ.κ.comp (X.emb0 i))
      (fun y => ((hι.1.lt_iff _).symm.trans (H y).symm).trans (norm_lt_iff ρ _)) x)
  cases b
  · obtain ⟨ι', red', hι'⟩ := h (D.what₂.places.conj w) (by rwa [D.what₂.muAt_conj]) (X.l i)
      (resChar_eq (X.lPrime i).out (by rwa [D.conj_val, star_natCast]))
    obtain ⟨ρ', rfl⟩ := exists_reading_of_induces (b := false) ρ hι'.1 fun x => by
      rw [D.conj_val]
      exact (key ⟨_, hs x⟩).trans (by rw [← X.restX_coefficientEmbedding_conj i x ⟨_, hs x⟩ rfl]; rfl)
    exact ⟨ρ', _, red', hι'.1, hι'⟩
  · obtain ⟨ρ', rfl⟩ := exists_reading_of_induces (b := true) ρ hι.1 key
    exact ⟨ρ', _, red, hι.1, hι⟩
end Bridge
namespace Model
end Model
end GlobalTheory.EigTie
end
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem _root_.GlobalTheory.T.admBC_of_serLoc : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  first | exact @_root_.GlobalTheory.CutAtGood.main_alt_alt | exact _root_.GlobalTheory.CutAtGood.main_alt_alt | (intros; apply _root_.GlobalTheory.CutAtGood.main_alt_alt <;> assumption)
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.Pass
theorem stepsNoCut_of_artin_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.NoCutStatement := fun hA =>
  ⟨GlobalTheory.CentralIdem.centralIdemCoeff, GlobalTheory.T.central_elements_from_idempotent_coeffs, GlobalTheory.T.typePrimeCompletionDegreeOneCount_proof, _root_.UpperTheory.GalS.stepType_alt, GlobalTheory.T.typeFamily_potentiallyCrystalline_common_tame_extension,
    GlobalTheory.PotDual.stepPotDual, GlobalTheory.T.jump_range_positive_sign_place, GlobalTheory.T.dualJumpRangeNegativeSignPlace_proof, GlobalTheory.StepLiftPf.main, GlobalTheory.T.twisted_galois_rep_character_blocks, GlobalTheory.T.twisted_dual_families_continuous,
    GlobalTheory.T.localCountDirectLifting_proof, GlobalTheory.T.localCountDualLifting_proof, GlobalTheory.T.blochKatoCharactersTypePrime_proof, _root_.GlobalTheory.Pass.ResidualSpan.main_alt_alt, _root_.GlobalTheory.T.globalPass_of_globalArtinReciprocity hA⟩
end GlobalTheory.Pass
end
end

section



section
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct
variable (D : D7)
def GaloisRepsAlt : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r, _root_.UpperTheory.GalS.IsGaloisRepOfN D π l ι r
end GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting
end
end
end

section



section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.Published.CharCrysModel
theorem of_hypotheses_m_alt (hD : HeckeLAdicCharacterDeRham) (hB : DeRhamPotSemistable) (hW : AlgebraicCharacterWD)
    (_hL : _root_.UpperTheory.Zero.LLC.RecTExists) : HeckeLAdicCharacterCrystalline := of_three hD hB hW
end GlobalTheory.Published.CharCrysModel
end
end
end

section

noncomputable abbrev Formalism.L2.NG.AutRep.SphericalAtPlace : type_of% (@UpperTheory.One.M.SphAtG) := @UpperTheory.One.M.SphAtG
end

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.centred_string_decomposition : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt := by
  first | exact @_root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt | exact _root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt | (intros; apply _root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt <;> assumption)
end
end

end

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem _root_.GlobalTheory.T.no_cut_passes_of_artin_reciprocity : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.NoCutStatement := by
  first | exact @_root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt | exact _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt | (intros; apply _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt <;> assumption)
end

end
end
