module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle491
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle494
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle363
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

abbrev _root_.GlobalTheory.T.TwistedThetaJetCondition : Prop :=  GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N →
      N ≠ algD Γ.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ
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
namespace GlobalTheory.TripleAssembly
theorem secondFactorMap_theta_pure_tensor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
      ∀ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v) →
        (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb →
        GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))) =
          ∑ i, R.p' (f i) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p' v (φ i v)) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm m f φ hφ hmem
  classical
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ' ▸ hm.triple.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have dV' : Γ.V'.J.det ≠ 0 := Onto.det_ne_of_hasSig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV'.sig w)
  have dW : Γ.W.J.det ≠ 0 := Onto.det_ne_of_hasSig_map (Bs.emb w).1 Complex.I (hg.hW.sig w)
  have gB : (sgn false W₁).gram.det ≠ 0 := by
    have e1 : (sgn false W₁).gram = W₁.gram := rfl
    rw [h.JW₁, Matrix.det_smul] at dV'
    rw [e1]
    exact right_ne_zero_of_mul dV'
  obtain ⟨T, hT, hinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Γ.M' ψ (sgn false W₁).gram e (hψ' ▸ hg.hM') hstd dV' dW gB
  have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Γ.M' Bs.ψ Bs.emb hg.hM'
  have H : ∃ q : (Matrix (Fin X.rank) (Fin W₁.rank) (AE D) → ℂ) →ₗ[ℂ] PiT R Γ Rf,
      ∀ Ψ ∈ darbAlg Γ.M' Bs.ψ Bs.emb, q (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
        liftPure Γ.M' R.p' Rf.p' (vacIm Γ Rf) Ψ := by
    obtain ⟨q, hq⟩ := Onto.exists_factor T _ (fun x hx => hinj x (hS hx)) (liftPure Γ.M' R.p' Rf.p' (vacIm Γ Rf))
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hS hΨ)]; exact hq Ψ hΨ⟩
  have h1 : mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))) =
      liftPure Γ.M' R.p' Rf.p' (vacIm Γ Rf) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) := by
    unfold mapB thetaLift
    rw [dite_eq_left H]
    exact H.choose_spec _ hmem
  have hs : ∀ᶠ v in Filter.cofinite, Rf.p' v (Γ.M'.vac v) = vacIm Γ Rf v := by
    filter_upwards [Xc.T.eventually_cofinite_notMem] with v hv using (hm.fin.sph v hv).1.symm
  have HL := GlobalTheory.T.weil_model_projection_factorisation _ _ _ Γ.M' Bs.ψ hg.hM' _ R.p' _ Rf.p' (vacIm Γ Rf) hs

  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold liftPure
  rw [dite_eq_left HL]
  exact HL.choose_spec (f i) (φ i) (hφ i).1 (hφ i).2
end GlobalTheory.TripleAssembly
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

theorem _root_.GlobalTheory.T.tripleProduct_secondMap_theta_pure : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
      ∀ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v) →
        (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb →
        GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))) =
          ∑ i, R.p' (f i) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p' v (φ i v)) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.secondFactorMap_theta_pure_tensor | exact _root_.GlobalTheory.TripleAssembly.secondFactorMap_theta_pure_tensor | (intros; apply _root_.GlobalTheory.TripleAssembly.secondFactorMap_theta_pure_tensor <;> assumption)
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
namespace GlobalTheory.SquareAgree.KerPFin
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU
theorem ker_polarizationProjection_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ), f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _hθ _hTr hO hT Pim rf rl p p' hMt v f φ hf hSB
    hvac hv
  classical
  have hψ : IsStd ψ := hO.psi ▸ hT.base.std
  have hM := hT.geo.hM'
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers D.host.F} 1 :=
    (hvac.and hM.std).mono fun w hw => hw.1.trans hw.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hk : kapX X e hO.JX 1 = 1 := by
    apply Subtype.ext
    simp [kapX]
  have halg : ∀ x ∈ SB _, tens (evFin D.host.F v) x r ∈ algD Γ.M' Bs.ψ Bs.emb := by
    intro x hx
    have hSBx : ∀ w, Function.update φ v x w ∈ SB _ := by
      intro w
      by_cases h : w = v
      · subst h; simpa using hx
      · rw [Function.update_of_ne h]; exact hSB w
    have hvacx : ∀ᶠ w in Filter.cofinite, Function.update φ v x w = Γ.M'.vac w :=
      (hvac.and (Filter.eventually_cofinite_ne v)).mono fun w hw => by rw [Function.update_of_ne hw.2]; exact hw.1
    rw [hrt]
    exact Submodule.subset_span ⟨f, _, hf, hSBx, hvacx, rfl⟩
  suffices H : ∀ x ∈ augAt om' v, tens (evFin D.host.F v) x r ∈ kerPD ψ θ A₁ B Bs Γ cB p' by
    have := H _ hv
    rwa [hrt, Function.update_eq_self] at this
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, hg, φ₀, hφ₀, φ₁, hφ₁, hact, rfl⟩ := hz
    have hsub : tens (evFin D.host.F v) (φ₁ - φ₀) r = tens (evFin D.host.F v) φ₁ r - tens (evFin D.host.F v) φ₀ r := by
      funext y; simp only [tens, Pi.sub_apply, sub_mul]
    have hRest : Rest (evFin D.host.F v) φ₀ r := by
      refine ⟨hr, ?_⟩
      have hSB0 : ∀ w, Function.update φ v φ₀ w ∈ SB _ := by
        intro w
        by_cases h : w = v
        · subst h; simpa using hφ₀
        · rw [Function.update_of_ne h]; exact hSB w
      rw [hrt]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ hSB0 (GlobalTheory.PureFactor.update_eventually φ v φ₀ hstd)
    have hmove : om' (g, 1) (tens (evFin D.host.F v) φ₀ r) = tens (evFin D.host.F v) φ₁ r := hact r hRest
    obtain ⟨Ψ, hΨ, hD0⟩ := hO.algB' _ (halg φ₀ hφ₀)
    have hgu : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ g) = g :=
      (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hO.JW₁).right_inv g
    have hg0 := GlobalTheory.SquareAgree.CoinvPass.conjUInv_mem_GfC W₁ Γ.V' (-1) hc hO.JW₁ v g hg
    have hW := hO.weilB _ Ψ hD0 (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ g) 1
    rw [hgu, hk, hmove] at hW
    have hDd := GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hW hD0
    rw [hsub, mem_kerPD hψ]
    refine ⟨Submodule.sub_mem _ (halg φ₁ hφ₁) (halg φ₀ hφ₀), _, Submodule.sub_mem _ (hMt.mapB.stabM.1 _ hg0 Ψ hΨ) hΨ, hDd, ?_⟩
    rw [map_sub, hMt.mapB.invf _ hg0 Ψ hΨ, sub_self]
  | zero =>
    have : tens (evFin D.host.F v) (0 : (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ) r = 0 := by
      funext y; simp [tens]
    rw [this]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : tens (evFin D.host.F v) (a + b) r = tens (evFin D.host.F v) a r + tens (evFin D.host.F v) b r := by
      funext y; simp only [tens, Pi.add_apply, add_mul]
    rw [this]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : tens (evFin D.host.F v) (c • a) r = c • tens (evFin D.host.F v) a r := by
      funext y; simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this]; exact Submodule.smul_mem _ c ha
end GlobalTheory.SquareAgree.KerPFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.polarization_kernel_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ), f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerPFin.ker_polarizationProjection_finiteDimensional | exact _root_.GlobalTheory.SquareAgree.KerPFin.ker_polarizationProjection_finiteDimensional | (intros; apply _root_.GlobalTheory.SquareAgree.KerPFin.ker_polarizationProjection_finiteDimensional <;> assumption)
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
namespace GlobalTheory.SquareAgree.KerStabFin
theorem stabilizer_finite_ker_polarization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v), ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, h) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro _ D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT Pi rf rl p p' hM v h hh Φ hΦ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  obtain ⟨g, hg, rfl⟩ := GlobalTheory.SquareAgree.KapOnto.kapX_onto D X e Γ.W hO.JX v h hh
  rw [mem_kerPD hstd] at hΦ ⊢
  obtain ⟨_, Φ₀, hΦ₀, hDat, hp⟩ := hΦ
  have hW := hO.weilB Φ Φ₀ hDat 1 g
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1 = 1 :=
    Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])
  rw [h1] at hW
  have hmem : ωB (1, g) Φ₀ ∈ algF ψ θ false A₁ B := hM.mapB.stabX.1 g hg Φ₀ hΦ₀
  obtain ⟨ΦD, hΦD, hD'⟩ := hO.algB _ hmem
  have heq := GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hW hD'
  refine ⟨heq ▸ hΦD, _, hmem, hW, ?_⟩
  rw [hM.mapB.eqf g hg Φ₀ hΦ₀, hp, map_zero]
end GlobalTheory.SquareAgree.KerStabFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.ker_polarizationProjection_stabilizer_finite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v), ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, h) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerStabFin.stabilizer_finite_ker_polarization | exact _root_.GlobalTheory.SquareAgree.KerStabFin.stabilizer_finite_ker_polarization | (intros; apply _root_.GlobalTheory.SquareAgree.KerStabFin.stabilizer_finite_ker_polarization <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp
namespace GlobalTheory.KFinCuspApprox
theorem isCuspForm_kFinite_average : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D)
    (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ →
    IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro D θ hθ _ N τ e he φ hφ hc
  set A : Formalism.REAL.KG (N.M.ε τ) → GA D N.V :=
    fun k => atTau θ N.V τ ((N.M.fr τ)⁻¹ * Formalism.REAL.toMK k * N.M.fr τ) with hA
  have hAc : Continuous A := (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
    GlobalTheory.SeriesToClosure.continuous_conjK fun k => GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hl : LeftInv (GQ N.V) φ := hφ.left
  have havg : ∀ x, GlobalTheory.KFinCuspApprox.avgN θ N τ e φ x = ∫ k, e k * φ (x * A k) ∂(Formalism.REAL.muK (N.M.ε τ)) :=
    fun x => rfl
  have hlA : LeftInv (GQ N.V) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := fun γ hγ g => by
    simp only [havg, mul_assoc, hl γ hγ]
  refine (isCuspFun_iff hlA).2 fun W hW => funext fun x => ?_
  have hcc := cocompact_single hW
  have h0 := congrFun ((isCuspFun_iff hl).1 hc W hW)
  set NN := NA (IsoFlag.single hW) with hNN
  have h𝓕 := isFundamentalDomain_stdDom ((GQ N.V).subgroupOf NN) (Measure.haar : Measure NN)
  have hfin := hcc.measure_ne_top h𝓕
  show constTermOn (GQ N.V) NN _ x = 0
  rw [hcc.constTermOn_eq_zero_iff h𝓕 hlA x]
  have hz : ∀ y, ∫ n in stdDom ((GQ N.V).subgroupOf NN), φ ((n : GA D N.V) * y) ∂(Measure.haar : Measure NN) = 0 :=
    fun y => (hcc.constTermOn_eq_zero_iff h𝓕 hl y).1 (h0 y)
  obtain ⟨K0, hK0, hs⟩ := hcc
  have hcont : Continuous fun p : NN × Formalism.REAL.KG (N.M.ε τ) => φ ((p.1 : GA D N.V) * x * A p.2) :=
    hφ.cont.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul (hAc.comp continuous_snd))
  obtain ⟨C, hC⟩ := (hK0.prod (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ)))).exists_bound_of_continuousOn
    hcont.continuousOn
  have hb : ∀ (n : NN) k, ‖φ ((n : GA D N.V) * x * A k)‖ ≤ C := fun n k => by
    obtain ⟨γ, hγ, hk⟩ := hs n
    have h1 := hC (γ * n, k) ⟨hk, trivial⟩
    have h2 := hl ((γ : NN) : GA D N.V) (Subgroup.mem_subgroupOf.1 hγ) ((n : GA D N.V) * x * A k)
    simp only [Subgroup.coe_mul] at h1
    have e1 : ((γ : NN) : GA D N.V) * n * x * A k = (γ : GA D N.V) * ((n : GA D N.V) * x * A k) := by
      simp only [mul_assoc]
    rwa [e1, h2] at h1
  obtain ⟨Ce, hCe⟩ := (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ))).exists_bound_of_continuousOn he.continuousOn
  haveI : IsFiniteMeasure ((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))) :=
    isFiniteMeasure_restrict.2 hfin
  have hint : Integrable (Function.uncurry fun (n : NN) (k : Formalism.REAL.KG (N.M.ε τ)) => e k * φ ((n : GA D N.V) * x * A k))
      (((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))).prod (Formalism.REAL.muK (N.M.ε τ))) := by
    refine Integrable.mono' (integrable_const (Ce * C)) ?_ (ae_of_all _ fun p => ?_)
    · exact ((he.comp continuous_snd).mul hcont).aestronglyMeasurable
    · show ‖e p.2 * φ ((p.1 : GA D N.V) * x * A p.2)‖ ≤ Ce * C
      rw [norm_mul]
      exact mul_le_mul (hCe p.2 trivial) (hb p.1 p.2) (norm_nonneg _) ((norm_nonneg _).trans (hCe p.2 trivial))
  calc ∫ n in stdDom ((GQ N.V).subgroupOf NN), GlobalTheory.KFinCuspApprox.avgN θ N τ e φ ((n : GA D N.V) * x)
        ∂(Measure.haar : Measure NN)
      = ∫ n in stdDom ((GQ N.V).subgroupOf NN), ∫ k, e k * φ ((n : GA D N.V) * x * A k) ∂(Formalism.REAL.muK (N.M.ε τ))
        ∂(Measure.haar : Measure NN) := by simp only [havg]
    _ = ∫ k, ∫ n in stdDom ((GQ N.V).subgroupOf NN), e k * φ ((n : GA D N.V) * x * A k)
        ∂(Measure.haar : Measure NN) ∂(Formalism.REAL.muK (N.M.ε τ)) := integral_integral_swap hint
    _ = ∫ k, e k * 0 ∂(Formalism.REAL.muK (N.M.ε τ)) := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only
        rw [integral_const_mul, ← hz (x * A k)]
        simp only [mul_assoc]
    _ = 0 := by simp
end GlobalTheory.KFinCuspApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kFinite_cuspForm_average_approx : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ → IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average | exact _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average | (intros; apply _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull
namespace GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem rowSum_of_hypotheses_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ t a => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.RowClaim.Test.pde_ne_q hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := GlobalTheory.RowClaim.Test.guard hS t
  obtain ⟨h1, h2, h3, h4, h5⟩ := GridChoice.sumOK_classes ch.W ch.S.toGridChoice t (ch.Phi a) hL
  obtain ⟨f1, f2, -⟩ := GridChoice.sumOK_flat_fin_ex hL ch.S.toGridChoice t (ch.Phi a) hde hc
  obtain ⟨v1, v2⟩ := GlobalTheory.T.gridKernelPairing_independent_of_expansion D T R.toLevCh ch.sc ch.G ch.W Set.univ ch.S.toGridChoice A.μ0 hL t trivial (ch.Phi a)
  exact
    { flat := f1
      flatA := fun w _ => flatIntegrable_aaVac_of_conductor ch.W w (hasConductor_psiAt_AA ch.W w)
      fin := f2
      ex := GridChoice.sumOK_ex hL ch.S.toGridChoice t (ch.Phi a) hde hc
      vec := v1
      indep := v2
      cls := h1
      gam := h2
      wts := h3
      br := h4
      read := h5 }
end GlobalTheory.RowClaim
end
end

section

theorem _root_.GlobalTheory.T.sumOKK_of_theta_local_inputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.SumOKK := by
  first | exact @_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt | exact _root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt <;> assumption)
end
end
