module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle477
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle474
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle010
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
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

@[expose] public section

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace UpperTheory.GalS
theorem noLgc_alt : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → NoCondition D := fun _ _ _ _ _ => trivial
theorem hubX_typePrime_conditions_alt : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ParameterChoice' D L → AdmissibleParameterJ.JumpConditions L → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → SumRepresentations.ConclusionG5 D → _root_.UpperTheory.GalS.NoCondition D → GlobalTheory.HubX.DepthZeroG D → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (∀ (i : D.nd.Loc) (k : Fin 2), TwistedPlaces.TwLoc D i → D.nd.l i = D.host.g k → HG D.nd D.naut i → GoodR D.nd i (X.r i) ∧ (∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (X.ρ i π) ∧ IsSSRep (rhoChiK D i (X.ρ i π))) ∧ ∃ (s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), X.eta + D.R.t + 1 < s ∧ CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k ∧ PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i (X.r i) X.eta s S sg U) ∧ (X.eta : ℝ) ≤ 2 * L.etaSz := by
  intro D L HW R X hX P hJ hadm hG5 hLgc hDZ CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hadm' : L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := hadm
  have hb : 1 ≤ L.sc.b := by linarith
  have ht : (D.R.t : ℝ) ≤ L.sc.b := by linarith
  obtain ⟨hnum1, hnum2, hnum3⟩ := GlobalTheory.typePrime_exceeds_constant D L P (by linarith) hb CT hCT
  obtain ⟨hJa, hJb, hJc, -, hJe, -, -⟩ := hJ
  have hJaAt : AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D (GlobalTheory.HubX.epJ D) := by
    rw [GlobalTheory.HubX.epJ_eq hJa]; exact hJa.choose_spec
  have hgood : ∀ i, GoodR D.nd i (X.r i) := hX.fam.good
  have hpt := GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hX.fam
  rw [hX.eta]
  refine ⟨fun i k _ hk hHG => ⟨hgood i, fun π hπ => ⟨(hpt i π hπ).1, (hpt i π hπ).2.1⟩, ?_⟩, hnum2⟩
  obtain ⟨sg, U, hsg, hU⟩ := GlobalTheory.T.signs_and_jump_sets_at_type_prime D L (GlobalTheory.HubX.epJ D) hJaAt hJb hJc hJe ht i k (X.r i) hk (hgood i)
  refine ⟨⌊3 * L.sc.b⌋₊ + 2, 0, sg, U, hnum1, hnum3 k, hsg, hU⟩
end UpperTheory.GalS
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
namespace GlobalTheory.BridgeAdmDict
theorem main_alt_alt : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  intro hC D hA hW hB
  have hAC := _root_.GlobalTheory.T.algebraicCharacter_of_adm2 D hA
  refine ⟨false, ?_⟩
  rintro i τ₀ g ρ ⟨hτ, hP⟩
  obtain ⟨b, hb, hU⟩ : ∃ b : Bool, (D.naut.iotaQC i).toRingHom.comp τ₀ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ b ∧
      (AdmissibleParameterJ.TypeU D false g ↔ b = true) := by
    rcases hP with h | h
    · refine ⟨false, ?_, ?_⟩
      · rw [hτ, ← h]; rfl
      · subst h
        simp [AdmissibleParameterJ.TypeU, (D.eTau ρ).2]
    · refine ⟨true, ?_, ?_⟩
      · rw [hτ, ← h, Formalism.L2.Geo.emb_mul_cc_comp]; rfl
      · subst h
        have := (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau ρ).2
        simp [AdmissibleParameterJ.TypeU, this]
  obtain ⟨cτ, h1, h2⟩ := GlobalTheory.T.jumps_dictionary_at_embedding_over_realPlace D hW hB hAC hC i τ₀ ρ b hb
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.sgnOf true b, cτ, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [hU.1 h]; rfl
  · intro h
    cases b
    · rfl
    · exact absurd (hU.2 rfl) h
  · rw [PPm_eq]; exact h1
  · intro w hw
    obtain ⟨h3, h4⟩ := h2 w (mem_placesOver D i τ₀ w hw)
    refine ⟨h3, ?_⟩
    rw [show AdmissibleParameterJ.rankOneCharacterQbar D i = mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.chiGL D i 1) from rfl, h4, sz_eq]
    rfl
end GlobalTheory.BridgeAdmDict
end
end

end

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

theorem _root_.GlobalTheory.T.admDict_of_weight_blockChar : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  first | exact @_root_.GlobalTheory.BridgeAdmDict.main_alt_alt | exact _root_.GlobalTheory.BridgeAdmDict.main_alt_alt | (intros; apply _root_.GlobalTheory.BridgeAdmDict.main_alt_alt <;> assumption)
end

end
end
