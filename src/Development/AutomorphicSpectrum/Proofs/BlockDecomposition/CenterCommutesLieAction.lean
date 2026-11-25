module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.ZalgCentral

theorem Zalg_mul_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)),
    z ∈ Zalg E a → ∀ X, z * lie E a X = lie E a X * z := by
  intros
  apply _root_.GlobalTheory.CuspRep.Zalg_mul_lie <;> assumption

end GlobalTheory.CompanionTheory.ZalgCentral
