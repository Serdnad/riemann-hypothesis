module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle570
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle553
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle401
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle469
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.lattice_half_representatives_mod_reductions : ∀ (D : D7) (S T : HSp D) {m k : ℕ} (Λ Λ' : AddSubgroup (WO S T)) (e : AE D) (Q : Finset (Pl D.host.E)) (fm : WO S T → Matrix (Fin m) (Fin k) (EAf D)), (∀ w w', fm (w - w') = fm w - fm w') → (∀ w, IsHalf e w → (w ∈ Λ ↔ IsIntM (fm w))) → (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf e w → IsHalf e w' → (w - w' ∈ Λ' ↔ ∀ PP ∈ Q, redM PP (fm w) = redM PP (fm w'))) → (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃ w, IsHalf e w ∧ IsIntM (fm w) ∧ ∀ PP ∈ Q, redM PP (fm w) = Y PP) → ∃ X : Finset (WO S T), (∀ x ∈ X, x ∈ Λ ∧ IsHalf e x) ∧ (∀ w ∈ Λ, IsHalf e w → ∃! x, x ∈ X ∧ w - x ∈ Λ') ∧ X.card = (∏ PP ∈ Q, Nat.card (kP PP)) ^ (m * k) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃! x, x ∈ X ∧ ∀ PP ∈ Q, redM PP (fm x) = Y PP) := by
  first | exact @GlobalTheory.ZRepBlock.zrep_block | exact GlobalTheory.ZRepBlock.zrep_block | (intros; apply GlobalTheory.ZRepBlock.zrep_block <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ w : WO S T, IsHalf e w → (w ∈ latO S T ΛS ΛT (fun _ => True) ↔ IsIntM (frMapO S T βS βT w)) := by
  first | exact @GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int | exact GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int | (intros; apply GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_H1_dual_pair : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  first | exact @GlobalTheory.EulerCharH1.finite_and_finrank_H1V | exact GlobalTheory.EulerCharH1.finite_and_finrank_H1V | (intros; apply GlobalTheory.EulerCharH1.finite_and_finrank_H1V <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.LocInputs


open TensorProduct in
theorem _root_.GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler :
    _root_.Formalism.GaloisCohomology.LocalTateDualityK → _root_.Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : _root_.Formalism.BasicNotions.D7) (HW : _root_.Formalism.BasicNotions.HWOf D.loc) (F : _root_.Formalism.BasicNotions.FonOf D.loc D.locA HW),
        ∃ _J : _root_.Formalism.MainNotions.LocalSituation.Ties D.loc D.locA HW F, _root_.Formalism.MainNotions.LocalSituation.admitted D HW F := by
  intro hduality heuler D HW F
  refine ⟨⟨fun l _ => (_root_.GlobalTheory.ThetaTie.nonempty_thetaL D l).some⟩, ?_⟩
  refine ⟨?_, hduality, _root_.GlobalTheory.TateTop.tate_h2_of_local_duality hduality D, heuler,
    _root_.GlobalTheory.TateFilQuot.tate_fil_quot D, _root_.GlobalTheory.FundCont.fundamentalExactSequence_continuity_all_theories D,
    _root_.GlobalTheory.Per.FontaineAll.fontaine_bounds D, _root_.GlobalTheory.TateDualFil.main D, ?_⟩
  · refine _root_.GlobalTheory.FundSeq.surjective_half_of_onto (fun l _ => ?_) D
    obtain ⟨C⟩ := _root_.GlobalTheory.MemLoc.nonempty_core l
    exact _root_.GlobalTheory.FundSeq.ontoAt_of_core C
      (_root_.GlobalTheory.MemLoc.one_sub_phi_onto l C) (_root_.GlobalTheory.MemLoc.FundOnto.fundOnto l C)
  · intro l _ K s LL h
    exact ⟨_root_.GlobalTheory.Cyc.FontW.main D HW F l K s LL h,
      _root_.GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

end GlobalTheory.LocInputs
end
