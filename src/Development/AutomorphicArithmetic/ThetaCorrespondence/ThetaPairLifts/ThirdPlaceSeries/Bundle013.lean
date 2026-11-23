module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.FrobDualOfTripleAttN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle364
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle319
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle532
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthQuotEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle405
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.TripleGal
theorem noInv_all_places_alt (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hT : ∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) (h2 : ValuationStabilityAtRing D.ntw i s)
    (hA : _root_.GlobalTheory.TripleGal.TripleAttN D.naut bkP i s) (hJ : NoJump bkP i s) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  by_cases hl : v ∈ placesOver D.host.E (D.ntw.l i)
  · exact ⟨GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump D bkP i s hJ v hl, GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump D bkP i s hT (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s hA) hJ v hl⟩
  by_cases hS : v ∈ Spl (X := D.ntw) i
  · rcases hS.1 with hg | hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hg
      exact GlobalTheory.T.noInv_at_type_primes D i s h2 k (fun e => hl (e ▸ hk)) v hk
    · exact GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s hA) v (Finset.mem_coe.1 hp)
  · obtain ⟨ι, hι⟩ := _root_.GlobalTheory.TripleGal.pure_of_tripleAtt_n D bkP i s hA
    exact _root_.GlobalTheory.PurityInvariants.noInv_of_pure_n D i s ι hι v hl hS
theorem adm1_adm8_selfDual_noJump_of_tripleAttN : ∀ (D : D7) (bkP : BlochKatoReduction.BK D), GlobalTheory.TypeLeaf.FrobDense D → (∀ i, D.ntw.NonzeroIndexPlace i → (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI))) → BlochKatoReduction.adm2 D → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, _root_.GlobalTheory.TripleGal.TripleAttN D.naut bkP i s) → BlochKatoReduction.adm1 bkP ∧ BlochKatoReduction.adm8 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump bkP i s := by
  intro D bkP hF hT h2 hA
  have hJ : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, NoJump bkP i s := fun i hi s => by
    obtain ⟨ι, J, h, h'⟩ := _root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)
    exact GlobalTheory.T.noHodgeJump_of_goodJumpMultiset D bkP i s ι J (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) h h'
  refine ⟨fun i hi s => ?_, fun i hi s => ?_, fun i hi => ⟨trivial, fun s => ⟨?_, hJ i hi s⟩⟩⟩
  · obtain ⟨ι, J, h, h'⟩ := _root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)
    exact GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount D bkP i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s))
      (_root_.GlobalTheory.TripleGal.noInv_all_places_alt D bkP i s (hT i hi) (h2 i hi s) (hA i hi s) (hJ i hi s))
      (GlobalTheory.T.conjugateNegativeJumpCount_of_goodHodgeJumps D bkP i s ι J (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) h h')
  · exact GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt_n D bkP i s (hA i hi s))
  · exact GlobalTheory.T.selfDual_lattice_of_conjDualCharpoly D i s (h2 i hi s) (GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense D hF i s (_root_.GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt_n D bkP i s (hA i hi s)))
end GlobalTheory.TripleGal
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
namespace GlobalTheory.StepGlobalPf
variable {D : D7} (i : D.nd.Loc)
variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)


theorem main_alt_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.GlobalStatement := by
  intro hA D i r ρ π Xs eρ eχ hr _ _ hG4 hG5 hG5x hG6 hDec _ hS hZ hπ hl hsel hsha
  obtain ⟨S, hS⟩ := hS
  rw [GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal]
  exact GlobalTheory.CutCore.main hA D i r ρ π Xs eρ eχ S hr hS hZ hπ (noChiOff i r Xs hG6) (unrOut i r ρ π Xs hG4 hDec)
    (atS i r π Xs hG5 hG5x) (atQ i r Xs hG5 hG5x)
    (fun w hw => ⟨(hl w hw).1, (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eρ).1 (hl w hw).2.1,
      fun c hc => (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eχ).1 ((hl w hw).2.2 c hc)⟩) hsel hsha
end GlobalTheory.StepGlobalPf
end
end
