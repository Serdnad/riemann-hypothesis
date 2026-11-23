module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle494
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle608
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarUnitModulus
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle023
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle026
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle022
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleGoodFormValuesBoundedByClassSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGoodFormValuesMemScaledDualWeylLattice
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly.Transport
end GlobalTheory.TripleAssembly.Transport
open GlobalTheory.TripleAssembly.Transport in
theorem GlobalTheory.TripleAssembly.triple_twist_transport_eq : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ true A B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ = Φ) ∧
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ false A₁ B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ = Φ) := by
  intro hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h htA htB R Rf hM
  have hgood : Γ.M.IsGood ψ := h.ψ ▸ hM.triple.geo.hM
  have hgood' : Γ.M'.IsGood ψ := h.ψ ▸ hM.triple.geo.hM'
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := h.ψ ▸ hM.triple.base.std
  have hZ : Γ.W.J.det ≠ 0 := by
    rw [h.JX, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit X).ne_zero
  have hY : Γ.V.J.det ≠ 0 := by
    rw [h.JW, one_smul]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
  have hY' : Γ.V'.J.det ≠ 0 := by
    rw [h.JW₁, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₁).ne_zero
  obtain ⟨T₁, hT₁, hi₁⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M ψ (sgn true W).gram e hgood hstd hY hZ
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn true W)).ne_zero
  obtain ⟨T₂, hT₂, hi₂⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M' ψ (sgn false W₁).gram e hgood' hstd hY' hZ
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn false W₁)).ne_zero
  have hle := GlobalTheory.TripleAssembly.darbAlg_le_schA _ _ _ Γ.M Bs.ψ Bs.emb hM.triple.geo.hM
  have hle' := GlobalTheory.TripleAssembly.darbAlg_le_schA _ _ _ Γ.M' Bs.ψ Bs.emb hM.triple.geo.hM'
  obtain ⟨hI, hI'⟩ := _root_.GlobalTheory.T.theta_image_eq_span_darboux hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h htA htB R Rf hM
  have ex1 := exists_factor T₁ _ (fun Φ hΦ => hi₁ Φ (hle hΦ))
    (GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf))
  have ex2 := exists_factor T₂ _ (fun Φ hΦ => hi₂ Φ (hle' hΦ))
    (GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf))
  refine ⟨⟨fun Ψ hΨ => ?_, fun Φ hΦ => ?_⟩, ⟨fun Ψ hΨ => ?_, fun Φ hΦ => ?_⟩⟩
  · have H : ∃ q : (Matrix (Fin X.rank) (Fin W.rank) (AE D) → ℂ) →ₗ[ℂ] _, ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
        q (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      obtain ⟨q, hq⟩ := ex1
      exact ⟨q, fun Ψ hΨ => by rw [← hT₁ Ψ (hle hΨ)]; exact hq Ψ hΨ⟩
    unfold GlobalTheory.TripleAssembly.mapA GlobalTheory.TripleAssembly.thetaLift
    rw [dite_eq_left H]
    exact H.choose_spec Ψ hΨ
  · rw [← hI T₁ hT₁] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    exact ⟨Ψ, hΨ, (hT₁ Ψ (hle hΨ)).symm⟩
  · have H : ∃ q : (Matrix (Fin X.rank) (Fin W₁.rank) (AE D) → ℂ) →ₗ[ℂ] _, ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
        q (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      obtain ⟨q, hq⟩ := ex2
      exact ⟨q, fun Ψ hΨ => by rw [← hT₂ Ψ (hle' hΨ)]; exact hq Ψ hΨ⟩
    unfold GlobalTheory.TripleAssembly.mapB GlobalTheory.TripleAssembly.thetaLift
    rw [dite_eq_left H]
    exact H.choose_spec Ψ hΨ
  · rw [← hI' T₂ hT₂] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    exact ⟨Ψ, hΨ, (hT₂ Ψ (hle' hΨ)).symm⟩
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.triple_twist_transport : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ true A B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ = Φ) ∧
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ false A₁ B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ = Φ) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.triple_twist_transport_eq | exact _root_.GlobalTheory.TripleAssembly.triple_twist_transport_eq | (intros; apply _root_.GlobalTheory.TripleAssembly.triple_twist_transport_eq <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly.Onto
theorem tripleProductAlgebra_weilRep_range_eq_top : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) = ⊤ ∧ (algF ψ θ false A₁ B).map (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf) = ⊤ := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm
  obtain ⟨iA, iB⟩ := _root_.GlobalTheory.T.theta_image_eq_span_darboux hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ' ▸ hm.triple.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have dV : Γ.V.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV.sig w)
  have dV' : Γ.V'.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV'.sig w)
  have dW : Γ.W.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 Complex.I (hg.hW.sig w)
  have gA : (sgn true W).gram.det ≠ 0 := by
    have e1 : (sgn true W).gram = -W.gram := rfl
    rw [h.JW, one_smul] at dV
    rw [e1, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) dV
  have gB : (sgn false W₁).gram.det ≠ 0 := by
    have e1 : (sgn false W₁).gram = W₁.gram := rfl
    rw [h.JW₁, Matrix.det_smul] at dV'
    rw [e1]
    exact right_ne_zero_of_mul dV'
  constructor
  · obtain ⟨T, hT, hinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Γ.M ψ (sgn true W).gram e (hψ' ▸ hg.hM) hstd dV dW gA
    rw [← iA T hT]
    refine (map_thetaLift Γ.M ψ _ e _ _ (GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Γ.M Bs.ψ Bs.emb hg.hM) T hT hinj).trans ?_
    exact map_darbAlg_eq_top Γ.M Bs.ψ Bs.emb hg.hM R.p Rf.p _ (Filter.Eventually.of_forall fun _ => rfl)
      hm.real.quot.onto hm.fin.onto
  · obtain ⟨T, hT, hinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Γ.M' ψ (sgn false W₁).gram e (hψ' ▸ hg.hM') hstd dV' dW gB
    rw [← iB T hT]
    refine (map_thetaLift Γ.M' ψ _ e _ _ (GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Γ.M' Bs.ψ Bs.emb hg.hM') T hT hinj).trans ?_
    refine map_darbAlg_eq_top Γ.M' Bs.ψ Bs.emb hg.hM' R.p' Rf.p' _ ?_ hm.real.quot'.onto hm.fin.onto'
    filter_upwards [Xc.T.eventually_cofinite_notMem] with v hv using (hm.fin.sph v hv).1.symm
end GlobalTheory.TripleAssembly.Onto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.triple_algebra_map_surjective : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) = ⊤ ∧ (algF ψ θ false A₁ B).map (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf) = ⊤ := by
  first | exact @_root_.GlobalTheory.TripleAssembly.Onto.tripleProductAlgebra_weilRep_range_eq_top | exact _root_.GlobalTheory.TripleAssembly.Onto.tripleProductAlgebra_weilRep_range_eq_top | (intros; apply _root_.GlobalTheory.TripleAssembly.Onto.tripleProductAlgebra_weilRep_range_eq_top <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedKappa
theorem fock_jets_of_moved_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y
  have hC := ch.S.Z.crv
  have hδ : ch.S.Z.δ ≠ 0 := GlobalTheory.InertSign.delta_ne_zero hC
  have he0 := ch.S.Z.e0_is p hp
  have hsd := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp x y
  have hvac := _root_.GlobalTheory.T.twisted_moved_vacuum_integral hP hI ch hch p hp x y
  have hc0 : (ch.S.Z.c0 p : ℂ) ≠ 0 := Units.ne_zero _
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have hconj := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac
    obtain ⟨Θ, hΘ, hΘ0, hjet⟩ := fock_jets_moved ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.fr (.grid (i + 1) D.R.m)) (ch.S.N.fr (.grid i D.R.m))
      (ch.S.N.fr_on _ ⟨hi, rfl⟩) (ch.S.N.fr_on _ ⟨by omega, rfl⟩)
      (ch.W.cart_is _ ⟨hi, le_rfl⟩) (ch.W.cart_is _ ⟨by omega, le_rfl⟩) ch.S.Z.δ hC hδ _ _ hsd.1 hsd.2 _ hconj
    obtain ⟨κ, hκ, hd⟩ := intertwining_mem_ne_zero hC ch.S.Z.pt0 he0 hsd.1 hsd.2 hΘ hΘ0
    refine ⟨κ / starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ), fun k => ?_⟩
    have h2 := fun f => GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.frC (.grid (i + 1) D.R.m))
      (ch.S.N.frC (.grid i D.R.m)) f ch.W.ψ_std ch.W.θ_is k 0
    show pureTensorO _ _ _ _ _ _ _ _ _ _ 0 = _
    rw [h2]
    have hj := hjet k
    erw [hj]
    rw [hκ, applyAt0_const_mul D _ hd, applyAt0_const_mul D _ hd]
    show starRingEnd ℂ _ = _ * starRingEnd ℂ _
    simp only [map_mul, map_div₀, Complex.conj_conj]
    have hc0' : starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ) ≠ 0 := (map_ne_zero _).2 hc0
    field_simp
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have hj1 : j + 1 ≤ D.R.m := hp
    obtain ⟨Θ, hΘ, hΘ0, hjet⟩ := fock_jets_moved ch.W.ψ ch.W.θ (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))
      (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) (ch.S.N.fr (.top j)) (ch.S.N.fr (.top (j + 1)))
      (ch.S.N.fr_on (.top j) (by show j ≤ D.R.m; omega)) (ch.S.N.fr_on (.top (j + 1)) hj1)
      (ch.W.cart_is (.top j) (by show j ≤ D.R.m; omega)) (ch.W.cart_is (.top (j + 1)) hj1) ch.S.Z.δ hC hδ _ _ hsd.1 hsd.2 _ hvac
    obtain ⟨κ, hκ, hd⟩ := intertwining_mem_ne_zero hC ch.S.Z.pt0 he0 hsd.1 hsd.2 hΘ hΘ0
    refine ⟨κ / (ch.S.Z.c0 (.top t j) : ℂ), fun k => ?_⟩
    show pureTensorO _ _ _ _ _ _ _ _ _ _ 0 = _
    erw [hjet k]
    rw [hκ, applyAt0_const_mul D _ hd, applyAt0_const_mul D _ hd]
    show _ = _ * RingHom.id ℂ _
    rw [RingHom.id_apply]
    field_simp
end GlobalTheory.MovedKappa
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

theorem _root_.GlobalTheory.T.movedKappa_fock_jets_span : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @_root_.GlobalTheory.MovedKappa.fock_jets_of_moved_vacuum | exact _root_.GlobalTheory.MovedKappa.fock_jets_of_moved_vacuum | (intros; apply _root_.GlobalTheory.MovedKappa.fock_jets_of_moved_vacuum <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedKappaNorm
section Mean
open MeasureTheory
open scoped Pointwise
end Mean
theorem norm_kappa_of_moved_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ → ‖κ‖ = 1 := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hκ
  have hC := ch.S.Z.crv
  have he0 := ch.S.Z.e0_is p hp
  have hsd := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp x y
  have hvac := _root_.GlobalTheory.T.twisted_moved_vacuum_integral hP hI ch hch p hp x y
  have hvac0 := ch.S.Z.vac_is p hp
  have hc0 := ch.S.Z.kernelNorm_constant_spec p hp
  have hd := _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hP hI ch hch p hp x y
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have h2 := fun f k => GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.frC (.grid (i + 1) D.R.m))
      (ch.S.N.frC (.grid i D.R.m)) f ch.W.ψ_std ch.W.θ_is k 0
    have key := fun Ls Lt => @normSq_scalar D ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.fr (.grid (i + 1) D.R.m)) (ch.S.N.fr (.grid i D.R.m))
      (ch.S.N.fr_on _ ⟨hi, rfl⟩) (ch.S.N.fr_on _ ⟨by omega, rfl⟩)
      (ch.W.cart_is _ ⟨hi, le_rfl⟩) (ch.W.cart_is _ ⟨by omega, le_rfl⟩) _ _ hC ch.S.Z.pt0 _ he0 Ls Lt
    have hconj := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac
    have hconj0 := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac0
    refine norm_eq_one_of_sq (c := starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ))
      (key _ _ (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) _ (by rw [inV_stdL, inV_stdL]; exact hconj0) _
        fun k => ?_) (key _ _ hsd.1 hsd.2 _ hconj _ fun k => ?_)
    · rw [iop_self hC he0]
      have h := congrArg (starRingEnd ℂ) ((h2 _ k).symm.trans (hc0 k))
      rw [Complex.conj_conj, map_mul] at h
      refine h.trans ?_
      show _ * starRingEnd ℂ (starRingEnd ℂ _) = _
      rw [Complex.conj_conj]
    · have h := congrArg (starRingEnd ℂ) ((h2 _ k).symm.trans (hκ k))
      rw [Complex.conj_conj, map_mul, GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd] at h
      refine h.trans ?_
      show _ * starRingEnd ℂ (starRingEnd ℂ _) = _
      rw [Complex.conj_conj, mul_left_comm _ κ, mul_assoc]
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have hj1 : j + 1 ≤ D.R.m := hp
    have key := fun Ls Lt => @normSq_scalar D ch.W.ψ ch.W.θ (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))
      (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) (ch.S.N.fr (.top j)) (ch.S.N.fr (.top (j + 1)))
      (ch.S.N.fr_on (.top j) (by show j ≤ D.R.m; omega)) (ch.S.N.fr_on (.top (j + 1)) hj1)
      (ch.W.cart_is (.top j) (by show j ≤ D.R.m; omega)) (ch.W.cart_is (.top (j + 1)) hj1) _ _ hC ch.S.Z.pt0 _ he0 Ls Lt
    refine norm_eq_one_of_sq (c := (ch.S.Z.c0 (.top t j) : ℂ))
      (key _ _ (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) _ (by rw [inV_stdL, inV_stdL]; exact hvac0) _
        fun k => ?_) (key _ _ hsd.1 hsd.2 _ hvac _ fun k => ?_)
    · rw [iop_self hC he0]
      exact hc0 k
    · have h := hκ k
      rw [GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd] at h
      refine h.trans ?_
      show _ * RingHom.id ℂ _ = _
      rw [RingHom.id_apply, mul_left_comm _ κ, mul_assoc]
end GlobalTheory.MovedKappaNorm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

theorem _root_.GlobalTheory.T.twist_norm_kappa_moved_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ → ‖κ‖ = 1 := by
  first | exact @_root_.GlobalTheory.MovedKappaNorm.norm_kappa_of_moved_place | exact _root_.GlobalTheory.MovedKappaNorm.norm_kappa_of_moved_place | (intros; apply _root_.GlobalTheory.MovedKappaNorm.norm_kappa_of_moved_place <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FormVal
theorem form_value_eq_finite_mul_infinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinFormK ∧ InfFormK := fun _ =>
  form_fin_inf_of GlobalTheory.T.integralGoodForm_values_mem_scaledDualWeylLattice GlobalTheory.T.baseTupleGoodForm_values_bounded_by_classSum GlobalTheory.T.kernelLossBound_nonneg_and_level_card_le_exp
end GlobalTheory.FormVal
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.form_value_finite_infinite_factorization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinFormK ∧ InfFormK := by
  first | exact @_root_.GlobalTheory.FormVal.form_value_eq_finite_mul_infinite | exact _root_.GlobalTheory.FormVal.form_value_eq_finite_mul_infinite | (intros; apply _root_.GlobalTheory.FormVal.form_value_eq_finite_mul_infinite <;> assumption)
end
end
