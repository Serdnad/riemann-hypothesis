module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle526
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle594
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle686
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle664
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle654
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle527
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle529
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle437
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle556
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle369
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle043
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle006
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.GlobalFormAtFrameLatNc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Mathlib.Topology.Sheaves.Init

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
theorem GlobalTheory.TripleAssembly.theta_triple_maps_lie_equivariant : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        (∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ X (fun g => ωB (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have key : ∀ τ, ∀ Y ∈ lieAt X τ, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
      (∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ X (fun g => ωB (1, g)) τ Y Φ Φ' →
        GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ)) := by
    intro τ Y hY
    obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.T.exists_archimedean_one_param_line_transposeGramUnitary D θ hθ X e Γ.W h.JX τ Y hY
    obtain ⟨Ti, hTi, hTi'⟩ := GlobalTheory.T.exists_real_lie_operator_theta_quotient_line Bs Γ Xc om om' R Rf hM γ hγ
    refine ⟨LinearMap.rTensor _ Ti, ?_, ?_⟩
    · intro Φ hΦ Φ' hΦ' hD
      obtain ⟨m, f, f₁, φ, hf, hsum, rfl, rfl⟩ := _root_.GlobalTheory.T.tripleProduct_lieDeriv_left_pure_tensor hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM τ Y hY γ hγ hγt Φ hΦ Φ' hΦ' hD
      have hmem : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb :=
        Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (hf i).1, (hf i).2.1, (hf i).2.2.1, rfl⟩
      have hφ : ∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v :=
        fun i => ⟨(hf i).2.1, (hf i).2.2.1⟩

      rw [_root_.GlobalTheory.T.tripleProduct_image_thetaSum_pure hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f₁ φ hφ hsum, _root_.GlobalTheory.T.tripleProduct_image_thetaSum_pure hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f φ hφ hmem, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.rTensor_tmul, ← hTi _ (hf i).1 _ (hf i).2.2.2]
    · intro Φ hΦ Φ' hΦ' hD
      obtain ⟨m, f, f₁, φ, hf, hsum, rfl, rfl⟩ := _root_.GlobalTheory.T.tripleProduct_lieDeriv_readoff hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM τ Y hY γ hγ hγt Φ hΦ Φ' hΦ' hD
      have hmem : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb :=
        Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (hf i).1, (hf i).2.1, (hf i).2.2.1, rfl⟩
      have hφ : ∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v :=
        fun i => ⟨(hf i).2.1, (hf i).2.2.1⟩

      rw [_root_.GlobalTheory.T.tripleProduct_secondMap_theta_pure hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f₁ φ hφ hsum, _root_.GlobalTheory.T.tripleProduct_secondMap_theta_pure hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f φ hφ hmem, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.rTensor_tmul, ← hTi' _ (hf i).1 _ (hf i).2.2.2]
  have H : ∀ τ, ∀ Y ∈ lieAt X τ, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) :=
    fun τ Y hY => let ⟨T, hA, _⟩ := key τ Y hY; ⟨T, hA⟩
  have hOp : ∀ τ, ∀ (Y) (hY : Y ∈ lieAt X τ),
      GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y = (H τ Y hY).choose := by
    intro τ Y hY
    unfold GlobalTheory.TripleAssembly.opLie
    rw [dite_eq_left (H τ Y hY)]
  refine ⟨fun τ Y hY Φ hΦ Φ' hΦ' hD => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hD => ?_⟩
  · rw [hOp τ Y hY]
    exact (H τ Y hY).choose_spec Φ hΦ Φ' hΦ' hD
  · have k := key τ Y hY
    have hA := k.choose_spec.1
    have hB := k.choose_spec.2
    have hst : ∀ Φ ∈ algF ψ θ true A B, ∃ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' :=
      (GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D ψ θ hψ hθ true W X A B β (β / α) ωA hWA).2.2 τ Y hY
    have hon : (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) = ⊤ := (_root_.GlobalTheory.T.triple_algebra_map_surjective hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM).1
    have hEq : (H τ Y hY).choose = k.choose := by
      apply LinearMap.ext
      intro x
      have hx : ∃ Ψ, Ψ ∈ algF ψ θ true A B ∧ GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Ψ = x :=
        (Submodule.mem_map (f := GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) (p := algF ψ θ true A B)).1
          ((Submodule.eq_top_iff'.1 hon) x)
      have hΨ := hx.choose_spec.1
      have h1 := (hst _ hΨ).choose_spec
      rw [← hx.choose_spec.2]
      exact ((H τ Y hY).choose_spec _ hΨ _ h1.1 h1.2).symm.trans (hA _ hΨ _ h1.1 h1.2)
    exact (hB Φ hΦ Φ' hΦ' hD).trans (congrArg (fun T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf) =>
      T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ)) ((hOp τ Y hY).trans hEq).symm)
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

theorem _root_.GlobalTheory.T.theta_triple_lift_lie_equivariant : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        (∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ X (fun g => ωB (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.theta_triple_maps_lie_equivariant | exact _root_.GlobalTheory.TripleAssembly.theta_triple_maps_lie_equivariant | (intros; apply _root_.GlobalTheory.TripleAssembly.theta_triple_maps_lie_equivariant <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.SquareAgree.KerPMax
theorem ker_projection_maximal_thetaSubspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) →
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → N ≤ N' → N' = N ∨ N' = algD Γ.M' Bs.ψ Bs.emb := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' Pi rf rl p p' hm N N' hN hN' hle
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by rw [← hO.psi]; exact hT'.base.std
  obtain ⟨hz, hlin⟩ := isDatum_linear Γ.M' ψ hstd cB
  have hfun : ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ → Φ₀ ∈ algF ψ θ false A₁ B := by
    intro ΦD hΦD Φ₀ hD
    obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' ΦD hΦD
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact hΦ₁
  let S : Submodule ℂ Pi :=
    { carrier := {x | ∃ ΦD ∈ N', ∃ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ ∧ p' Φ₀ = x}
      zero_mem' := ⟨0, N'.zero_mem, 0, hz, map_zero p'⟩
      add_mem' := by
        rintro _ _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩ ⟨ΨD, hΨD, Ψ₀, hE, rfl⟩
        refine ⟨ΦD + ΨD, N'.add_mem hΦD hΨD, Φ₀ + Ψ₀, ?_, map_add p' _ _⟩
        simpa using hlin ΦD ΨD Φ₀ Ψ₀ 1 hD hE
      smul_mem' := by
        rintro c _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
        refine ⟨c • ΦD, N'.smul_mem c hΦD, c • Φ₀, ?_, map_smul p' c Φ₀⟩
        simpa using hlin 0 ΦD 0 Φ₀ c hz hD }
  have hc1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1 = 1 :=
    Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])
  have hS1 : ∀ g ∈ GfC X, ∀ x ∈ S, rf g x ∈ S := by
    rintro g hg _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
    have hΦ₀ := hfun ΦD (hN'.le hΦD) Φ₀ hD
    have hW := hO.weilB ΦD Φ₀ hD 1 g
    rw [hc1] at hW
    exact ⟨_, _root_.GlobalTheory.T.adelic_stabilizer_finite_of_theta_subgroup hP D X W.rank W₁.rank e Bs Γ Xc om om' hT' hO.JX N' hN' g hg ΦD hΦD, _, hW,
      hm.mapB.eqf g hg Φ₀ hΦ₀⟩
  have hS2 : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, rl τ Y x ∈ S := by
    rintro τ Y hY _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
    obtain ⟨ΨD, hΨD, Φ₁, hΦ₁, hE, hder⟩ := _root_.GlobalTheory.T.adelic_stabilizer_lie_ker_polarization hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB
      hθ hT hO hT' Pi rf rl p p' hm N' hN' τ Y hY ΦD hΦD Φ₀ hD
    exact ⟨ΨD, hΨD, Φ₁, hE, hm.mapB.eql τ Y hY Φ₀ (hfun _ (hN'.le hΦD) _ hD) Φ₁ hΦ₁ hder⟩
  rcases hm.irred.2 S hS1 hS2 with h0 | h1
  · left
    refine le_antisymm (fun ΦD hΦD => ?_) hle
    obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' ΦD (hN'.le hΦD)
    have hx : p' Φ₁ ∈ S := ⟨ΦD, hΦD, Φ₁, hD₁, rfl⟩
    rw [h0, Submodule.mem_bot] at hx
    exact (hN ΦD).2 ⟨hN'.le hΦD, Φ₁, hΦ₁, hD₁, hx⟩
  · right
    refine le_antisymm hN'.le (fun ΨD hΨD => ?_)
    obtain ⟨Ψ₀, hΨ₀, hE⟩ := hO.algB' ΨD hΨD
    have hx : p' Ψ₀ ∈ S := h1 ▸ Submodule.mem_top
    obtain ⟨ΦD, hΦD, Φ₀, hD, hpe⟩ := hx
    have hdiff : ΨD - ΦD ∈ N := by
      refine (hN _).2 ⟨(algD _ _ _).sub_mem hΨD (hN'.le hΦD), Ψ₀ - Φ₀,
        (algF ψ θ false A₁ B).sub_mem hΨ₀ (hfun _ (hN'.le hΦD) _ hD), ?_, ?_⟩
      · simpa [sub_eq_add_neg] using hlin ΨD ΦD Ψ₀ Φ₀ (-1) hE hD
      · rw [map_sub, hpe, sub_self]
    simpa using N'.add_mem (hle hdiff) hΦD
end GlobalTheory.SquareAgree.KerPMax
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.thetaKernel_projection_isMax : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) →
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → N ≤ N' → N' = N ∨ N' = algD Γ.M' Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace | exact _root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace | (intros; apply _root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace <;> assumption)
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
namespace GlobalTheory.MovedDict
theorem moved_vacuum_kappa_eval : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, Mod1All κ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  obtain ⟨κ, hj⟩ := _root_.GlobalTheory.T.movedKappa_fock_jets_span hPr hInp ch hIs p hp x y
  obtain ⟨hm, hu⟩ := _root_.GlobalTheory.T.movedKappa_rational_of_arithmetic hPr hInp ch hIs p hp x y κ hj
  exact ⟨κ, hm, hu, hj⟩
end GlobalTheory.MovedDict
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

theorem _root_.GlobalTheory.T.twisted_moved_vacuum_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, Mod1All κ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_vacuum_kappa_eval | exact _root_.GlobalTheory.MovedDict.moved_vacuum_kappa_eval | (intros; apply _root_.GlobalTheory.MovedDict.moved_vacuum_kappa_eval <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipStart
theorem flipStart_highestVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 = D.R.m → HEq g (R.vX t) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j g hj hg
  refine ⟨1, one_mem _, fun e he Φ => ?_⟩
  rw [Units.val_one, one_smul]
  obtain ⟨e', he', hθ⟩ := GlobalTheory.T.rowChain_last_step_vector_eq_theta_of_datum s ch hch t j g hj hg
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hS : IsSelfDualC (ch.G.pS (.mu t 0 j)) (ch.G.latS (.mu t 0 j)) :=
    (colY_isV D T R.toLevCh A.μ0 hL j j.2.le).sd
  have hT : IsSelfDualC (ch.G.pT (.mu t 0 j)) (ch.G.latT (.mu t 0 j)) :=
    (colY_isV D T R.toLevCh A.μ0 hL (j + 1) j.2).sd
  have hv := ch.rm.vT_is t 0 j (Nat.zero_le _) j.2
  have hsub : GlobalTheory.FlipTop.topPl R.toLevCh t ⊆ locPl ch.G t := by
    classical
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces ch.G hL t h)
    · exact Finset.mem_union_right _ h
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isThetaAt_enlarge_placeIdempotent_latticeIndicator hS hT hv he he' hsub (GlobalTheory.T.gridFirstColumnStep_isSchwartzBruhat_half ch.G ch.S.B hL t he' j j.2) hθ
  have hAA : ∀ w ∈ locPl ch.G t, w ∉ GlobalTheory.FlipTop.topPl R.toLevCh t →
      ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
        ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw _
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  rw [GlobalTheory.T.first_column_type_twist_datum_eq_given_function ch.G ch.S.B hL t he he' hAA Φ j j.2] at h1 h2
  exact ⟨h1, h2⟩
end GlobalTheory.FlipStart
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_flipStart_highestVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 = D.R.m → HEq g (R.vX t) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  first | exact @_root_.GlobalTheory.FlipStart.flipStart_highestVector | exact _root_.GlobalTheory.FlipStart.flipStart_highestVector | (intros; apply _root_.GlobalTheory.FlipStart.flipStart_highestVector <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
namespace GlobalTheory.RowTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem twist_linear_independence_test (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal) : GlobalTheory.RowClaim.LinK := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc a u => ?_⟩⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.twisted_theta_lift_automorphic hP hL large₂ hS ch hch CF hsc a u
  exact ⟨h1, GlobalTheory.T.besselPeriodCorank_converges_column ch.W ch.M hch.vol ch.ξ _ (col_mem ch a) _ h2⟩
end GlobalTheory.RowTest
end
end

section

theorem _root_.GlobalTheory.T.twisted_characters_linearly_independent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.LinK := by
  first | exact @_root_.GlobalTheory.RowTest.twist_linear_independence_test | exact _root_.GlobalTheory.RowTest.twist_linear_independence_test | (intros; apply _root_.GlobalTheory.RowTest.twist_linear_independence_test <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.LieEq
theorem polarization_match_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀' ∈ algF ψ θ false A₁ B, IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' → IsDer θ X (fun h => ωB (1, h)) τ Y Φ₀ Φ₀' → ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ'D ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₀'D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Φ'D Φ' → IsDatum Γ.M' ψ cB Φ₀D Φ₀ → IsDatum Γ.M' ψ cB Φ₀'D Φ₀' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf Φ'D Φ₀'D := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hTr R Rf hM Pi rf rl p p' _ τ Y hY
    Φ _ Φ' _ Φ₀ _ Φ₀' _ hD hD₀ ΦD _ Φ'D _ Φ₀D _ Φ₀'D _ hd1 hd2 hd3 hd4 hPM
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.T.exists_oneParamSubgroup_transposeGram_lieAt D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw Bs Γ Xc om om' hTr γ hγ
  obtain ⟨δ', hδ'⟩ := _root_.GlobalTheory.T.twist_lie_derivative_model hP Bs Γ Xc om om' hTr γ hγ
  obtain ⟨Aop, hA, hA'⟩ := exists_op (Γ.M.Pol Bs.ψ Bs.emb) (Γ.M'.Pol Bs.ψ Bs.emb) R.p R.p' δ δ'
    (fun f hf f' hf' hpp => hM.real.lie γ hγ f hf f' hf' _ _ (hδ f hf).2 (hδ' f' hf').2 hpp)
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', hs⟩ := hPM
  have e1 := _root_.GlobalTheory.T.twist_polarization_datum_lie_derivative hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTr τ Y γ hγt hγ Φ Φ' hD T m f
    (fun i => δ (f i)) φ hf (fun i => (hδ _ (hf i).1).2) (hΦ ▸ hd1) Φ'D hd2
  have e2 := _root_.GlobalTheory.T.twist_polarization_datum_derivative_second hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTr τ Y γ hγt hγ Φ₀ Φ₀' hD₀ T m' f'
    (fun j => δ' (f' j)) φ' hf' (fun j => (hδ' _ (hf' j).1).2) (hΦ' ▸ hd3) Φ₀'D hd4
  refine ⟨T, hT, m, m', fun i => δ (f i), φ, fun j => δ' (f' j), φ', fun i => ⟨(hδ _ (hf i).1).1, (hf i).2⟩,
    fun j => ⟨(hδ' _ (hf' j).1).1, (hf' j).2⟩, e1, e2, ?_⟩
  have := congrArg (TensorProduct.map Aop LinearMap.id) hs

  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply] at this
  simpa only [hA _ (hf _).1, hA' _ (hf' _).1] using this
end GlobalTheory.SquareAgree.LieEq
end
end
end

section

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

theorem _root_.GlobalTheory.T.globalFormAt_frameLat_of_siegelWeil : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → ∀ D : D7, SiegelWeilFock D → ∀ A : HSp D, GlobalFormAt A (frameLat A) := by
  first | exact @_root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc | exact _root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc | (intros; apply _root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc <;> assumption)
end
end
