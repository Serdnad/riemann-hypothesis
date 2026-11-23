module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle452
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle050
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle040
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle079
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle078
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaPairingExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelIntegrableOnFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle599
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle349
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle351
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle459
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle080
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle018
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped TensorProduct
theorem GlobalTheory.StageLift.theta_stage_lift_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank), (∀ t, lam t ≠ 0) ∧
        ∀ t P', (∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') → X.I W.ψ W.θ t (s P') = lam t • X.I' W.ψ W.θ t P' := by
  intro hP hK hL
  have hM := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hL
  have hWe := _root_.GlobalTheory.T.triple_weil_transfer_matching hP.howeDualityReal hP hK hL
  have hAg := _root_.GlobalTheory.T.thetaIntegrals_agree_of_convergence hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_tripleConditions (_root_.GlobalTheory.T.theta_finiteData_match_each_stage hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL' G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨h1, h3⟩ := h C hC D large₂ a b r T Lc μ hL' G
  obtain ⟨FA, FA', FW, ea, eb, hd⟩ := h1 W i j p q A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, qm, qm', hq, hq', hLM⟩ := hM D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW ea eb
  obtain ⟨g, hg⟩ := qm.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have key : ∀ t, ∃ l : ℂ, l ≠ 0 ∧ ∀ P', (∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') →
      X.I W.ψ W.θ t (g (qm' P')) = l • X.I' W.ψ W.θ t P' := by
    intro t
    obtain ⟨hT, hE, hf, hf', hk, hk'⟩ := hd t
    obtain ⟨hex, hall⟩ := hLM _ _ hT hE
    obtain ⟨Pim, rf, rl, pm, pm', hm⟩ := hWe D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hT hex (X.ω t) (X.ω' t)
      (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, r, r', e, -, -, hr, hr'⟩ := hall _ _ _ _ _ _ _ hm
    obtain ⟨κ, hκ, hrk⟩ := h3 W i j p q A A' WW X hX FA FA' FW t hf hf' Pim rf rl pm pm' hm Pr Pf qm qm' r r' e hq hq' hr hr'
    obtain ⟨c, hc0, hcI⟩ := hAg D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hT X.m X.fd X.m' X.fd' hIs.meas hIs.meas' _ _ _ _ _ _ _ hm
    refine ⟨c * κ, mul_ne_zero hc0 hκ, fun P' hP' => ?_⟩
    have hΦ : GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) (g (qm' P')) ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true FA FW :=
      Submodule.subset_span ⟨X.f t, g (qm' P'), hf, rfl⟩
    have hΦ0 : GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
      Submodule.subset_span ⟨X.f' t, P', hf', rfl⟩
    have hΦ' := Submodule.smul_mem _ κ hΦ0
    have hsm : ∀ x h, thetaKO (X.ω' t) x h (κ • GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') =
        κ * X.ker' W.ψ W.θ t P' h x := by
      intro x h
      rw [← hk' P' x h]
      simp [thetaKO, map_smul]
    have hint : ∀ h, MeasureTheory.IntegrableOn
        (fun x => thetaKO (X.ω' t) x h (κ • GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P')) X.fd' X.m' := by
      intro h
      simp_rw [hsm]
      exact (hP' h).const_mul κ
    have hqg : qm (g (qm' P')) = qm' P' := LinearMap.congr_fun hg _
    have hp : pm (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) (g (qm' P'))) =
        pm' (κ • GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') := by
      rw [hr _ hf, map_smul, hr' _ hf', hqg, hrk, TensorProduct.tmul_smul, map_smul]
    have h1 := hcI _ hΦ _ hΦ' hint hp
    funext h
    have h2 := congrFun h1 h
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.smul_apply, smul_eq_mul] at h2
    simp only [Tri.I, Tri.I', Pi.smul_apply, smul_eq_mul]
    simp_rw [← hk]
    rw [h2]
    simp_rw [hsm]
    rw [MeasureTheory.integral_const_mul]
    ring
  choose lam hlam using key
  exact ⟨lam, g ∘ₗ qm', fun t => (hlam t).1, fun t P' hP' => (hlam t).2 P' hP'⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_stage_liftable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank), (∀ t, lam t ≠ 0) ∧
        ∀ t P', (∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') → X.I W.ψ W.θ t (s P') = lam t • X.I' W.ψ W.θ t P' := by
  first | exact @_root_.GlobalTheory.StageLift.theta_stage_lift_exists | exact _root_.GlobalTheory.StageLift.theta_stage_lift_exists | (intros; apply _root_.GlobalTheory.StageLift.theta_stage_lift_exists <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.RowEx.BotField
theorem sums_mem_bottomField (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) {D : D7} {T : Type} [Finite T] {L : LevCh D T}
    {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (hL : L.Is μ₀) (hX : IsBottomTri W i j X) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ SumsIn W (algebraMap M ℂ) X := by
  obtain ⟨M₁, h₁, Ω, hΩ, e₁⟩ := field_of_gens (fun t h k => X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (_root_.GlobalTheory.T.bottom_spanned_by_classSums hP hI hL hX) (_root_.GlobalTheory.T.bottom_classSums_algebraic hP hI hL hX)
  obtain ⟨M₂, h₂, Ω', hΩ', e₂⟩ := field_of_gens (fun t h k => X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (_root_.GlobalTheory.T.bottom_spanned_by_twistedClassSums hP hI hL hX) (_root_.GlobalTheory.T.bottom_twistedClassSums_algebraic hP hI hL hX)
  refine ⟨M₁ ⊔ M₂, inferInstance, Ω, Ω', hΩ, hΩ', fun t h hh => ⟨fun k _ => ?_, fun k _ => ?_⟩⟩
  · exact ⟨⟨_, (le_sup_left : M₁ ≤ _) (e₁ t h hh k)⟩, rfl⟩
  · exact ⟨⟨_, (le_sup_right : M₂ ≤ _) (e₂ t h hh k)⟩, rfl⟩
end GlobalTheory.RowEx.BotField
theorem GlobalTheory.RowEx.bottomField_isNumberField : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → NFBot := by
  intro hP hI
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => by
    haveI : Finite T := hS.fin
    have hL : R.toLevCh.Is A.μ0 := hS.core.lev
    have hex : ∀ ij : Fin D.R.m × Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
        ∃ (A₁ A₂ WW : HSp D) (X : Tri T A₁ A₂ WW), IsBottomTri ch.W ij.1 ij.2 X ∧ SumsIn ch.W (algebraMap M ℂ) X := by
      intro ij
      obtain ⟨A₁, A₂, WW, X, hX⟩ := exists_bottomTri hL ch.G ch.W ij.1 ij.2
      obtain ⟨M, hM, hs⟩ := _root_.GlobalTheory.RowEx.BotField.sums_mem_bottomField hP hI hL hX
      exact ⟨M, hM, A₁, A₂, WW, X, hX, hs⟩
    choose M hM hB using hex
    haveI := hM
    refine ⟨⨆ ij, M ij, IntermediateField.finiteDimensional_iSup_of_finite, fun i j => ?_⟩
    obtain ⟨A₁, A₂, WW, X, hX, hs⟩ := hB (i, j)
    refine ⟨A₁, A₂, WW, X, hX, GlobalTheory.RowEx.BotField.sumsIn_mono hs ?_⟩
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨z, (le_iSup M (i, j) : M (i, j) ≤ _) z.2⟩, rfl⟩
  ⟩⟩
end
end
end

section

section
noncomputable section
namespace GlobalTheory.GoodFock
section Ring
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli Finset
variable {U : Type} [Ring U] [Algebra ℂ U] {n b : ℕ}
end Ring
section Poly
open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial
variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
end Poly
section Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.ChainFr GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.MixModel Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
end Theta
section Quot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Matrix GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.RealQuot Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {M X : HSp D}
end Quot
section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem exists_admissible_fock_polynomial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  intro hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, q, q', -, hq', hLM⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, q' P₀ = 0 → ∀ P, q' P = 0 := by
    by_cases h : ∃ P₀, q' P₀ ≠ 0
    · exact h.imp fun _ h h' => absurd h' h
    · push_neg at h
      exact ⟨0, fun _ => h⟩
  refine ⟨capelliC (quad (raiO τ (sgA A₁ τ) (B.ε τ)) (lowO τ (sgA A₁ τ) (B.ε τ)))
    ((W₁.rank : ℂ) - 1) P₀, fun α β htr hexp ωA ωB Pi rf rl p p' hm f hf => ⟨fun ν₁ 𝓕₁ hν => ?_, fun h0 P'' => ?_⟩⟩
  · obtain ⟨p₀, q₀, hsig, -, hlt⟩ := htr.sig
    have hW : IsWeilDatumO ψ (GlobalTheory.Grid.sgn false W₁) X α (α / β) (ωB.toSgn false) := hm.weilB
    have hk := killed_capelli hψ hθ (frSgn false A₁) B hf τ P₀
    refine GlobalTheory.T.thetaKernel_integrableOn_fundamentalDomain hP.siegelSetUnitary D ψ θ hθ false W₁ X _ _ ωB hm.weilB q₀ ⟨τ, (hsig τ).2.1⟩ (by omega) ν₁ 𝓕₁ hν _
      (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn false A₁) B hf.1 _) τ fun g h S₀ r d μ' 𝓕' hμ x i hx => ?_
    have := (hk.om hW hθ ((GlobalTheory.Grid.ofSgn false W₁).symm g) h).mixS_eq_zero hψ hθ d hμ x i hx
    exact this
  · have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨-, hco, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ)
      hm.weilB hexpB Pi rf rl p' hm.mapB
    have hc := LinearMap.congr_fun (comp_capelli (p' ∘ₗ fockF ψ θ false A₁ B f) _ _ ((W₁.rank : ℂ) - 1)
      (comp_quad A₁ B (fun τ => a τ - b τ) τ _ (hco f hf))) P₀
    obtain ⟨a', b', ha', hb', hgap⟩ := htr.gap τ
    rw [Formalism.L2.Fam.ThC.expU D α τ _ _ ha' (hexp τ).1, Formalism.L2.Fam.ThC.expU D β τ _ _ hb' (hexp τ).2] at hgap
    have hne : (∏ j : Fin W₁.rank, (-((X.rank : ℂ) / 2 + ((a τ - b τ : ℚ) : ℂ)) + ((W₁.rank : ℂ) - 1 - (j : ℕ)))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun j _ h => ?_
      have hj : ((j : ℕ) : ℚ) + 1 ≤ W₁.rank := by exact_mod_cast j.2
      have h' : (-((X.rank : ℚ) / 2 + (a τ - b τ)) + ((W₁.rank : ℚ) - 1 - (j : ℕ))) = 0 := by
        refine Rat.cast_injective (α := ℂ) ?_
        push_cast at h ⊢
        exact h
      linarith
    have h1 : p' (fockF ψ θ false A₁ B f P₀) = 0 := (smul_eq_zero.1 (hc.symm.trans h0)).resolve_left hne
    obtain ⟨Pf, r, r', e, -, -, -, he⟩ := (hLM α β htr hexp).2 ωA ωB Pi rf rl p p' hm
    rw [he f hf] at h1 ⊢
    by_cases hz : q' P₀ = 0
    · rw [hP₀ hz, TensorProduct.zero_tmul, map_zero]
    · have h2 : q' P₀ ⊗ₜ[ℂ] r' f = 0 := e.injective (h1.trans (map_zero e).symm)
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hz
      have h3 := congrArg (fun x => TensorProduct.lid ℂ Pf (LinearMap.rTensor Pf l x)) h2
      have h4 : r' f = 0 := by simpa [hl] using h3
      rw [h4, TensorProduct.tmul_zero, map_zero]
end Main
end GlobalTheory.GoodFock
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory

theorem _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  first | exact @_root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | exact _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | (intros; apply _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.StageGeo.geometric_stage_constant_on_pure_tensors :
    _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : Base D.host.F D.host.E) (Γ : Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → GlobalTheory.SquareAgree.IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    IsHaarFD W₁ ν₁ 𝓕₁ → IsWeil ψ false W₁ X α (α / β) ωB →
    (∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, ωB (g, 1) Φ ∈ algF ψ θ false A₁ B) →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) (c : ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ Xc om om' R Rf c →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb,
    ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ)
      (φ' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, φ' v ∈ GlobalTheory.WeilM.SB _) → (∀ v ∉ Xc.T, φ v = Γ.M.vac v) → (∀ v ∉ Xc.T, φ' v = Γ.M'.vac v) →
    R.p f = R.p' f' → (∀ v ∈ Xc.T, Rf.p v (φ v) = Rf.p' v (φ' v)) →
    ∀ (Φ : WO W X → ℂ) (Φ' : WO W₁ X → ℂ), GlobalTheory.SquareAgree.IsDatum Γ.M ψ cA (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) Φ →
      GlobalTheory.SquareAgree.IsDatum Γ.M' ψ cB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ') Φ' →
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) →
      thetaInt ωA ν 𝓕 Φ = c • thetaInt ωB ν₁ 𝓕₁ Φ' := by
  intro hP hK D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hν₁ hw hstab R Rf c hM hc f hf f' hf' φ φ'
    s s' v v' hR hfin Φ Φ' hD hD' hint
  have hT := hM.triple
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hT
  obtain ⟨-, hC⟩ := hK' R Rf hM
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by rw [← hO.psi]; exact hT.base.std
  have hstd := hT.geo.hM'.std
  obtain ⟨-, hco, hex, -⟩ := hC.1 Bs.v₁ hT.chars.good
  have hv₁ : Bs.v₁ ∉ Xc.T := hT.chars.good.1
  have hcof : ∀ᶠ w in Filter.cofinite, φ' w = Γ.M'.vac w :=
    Filter.Eventually.mono Xc.T.finite_toSet.compl_mem_cofinite fun w hw => v' w hw
  have hφstd : ∀ᶠ w in Filter.cofinite, φ' w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers D.host.F} 1 :=
    (hcof.and hstd).mono fun w h => h.1.trans h.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor Bs.v₁ f' φ' hφstd
  obtain ⟨φo, hφo, hp⟩ := hex Bs.τ₁ (Rf.p' Bs.v₁ (φ' Bs.v₁))
  have hφoSB : φo ∈ GlobalTheory.WeilM.SB _ := hφo.1
  have hδ : φ' Bs.v₁ - φo ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' Bs.v₁ :=
    (hco _ (sub_mem (s' Bs.v₁) hφoSB)).1 (by rw [map_sub, hp, sub_self])
  have hupd : ∀ w, Function.update φ' Bs.v₁ φo w ∈ GlobalTheory.WeilM.SB _ := by
    intro w
    by_cases hw : w = Bs.v₁
    · subst hw; rw [Function.update_self]; exact hφoSB
    · rw [Function.update_of_ne hw]; exact s' w
  have hcof' : ∀ᶠ w in Filter.cofinite, Function.update φ' Bs.v₁ φo w = Γ.M'.vac w := by
    filter_upwards [hcof, Filter.eventually_cofinite_ne Bs.v₁] with w h1 hne
    rw [Function.update_of_ne hne]; exact h1
  obtain ⟨Φ₀D, eD⟩ : ∃ Φ₀D, Φ₀D = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' (Function.update φ' Bs.v₁ φo) := ⟨_, rfl⟩
  have h0a : Φ₀D ∈ GlobalTheory.SquareAgree.algD Γ.M' Bs.ψ Bs.emb := Submodule.subset_span ⟨f', _, hf', hupd, hcof', eD⟩
  have h0s : Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ :=
    Submodule.subset_span ⟨f', _, hupd, hcof', by rw [Function.update_self]; exact hφo, eD⟩
  have hdiff : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' - Φ₀D ∈ GlobalTheory.SquareAgree.CoinvPass.relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁ := by
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) (φ' Bs.v₁) r := by
      rw [hrt, Function.update_eq_self]
    rw [e1, eD, ← hrt, ← GlobalTheory.SquareAgree.CoinvPass.tens_sub']
    exact GlobalTheory.SquareAgree.CoinvPass.tens_mem_relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁ hstd hf' s' hcof hr hrt _ hδ
  have hpm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) Φ₀D := by
    refine ⟨insert Bs.v₁ Xc.T, Finset.subset_insert _ _, 1, 1, fun _ => f, fun _ => φ, fun _ => f',
      fun _ => Function.update φ' Bs.v₁ φo, fun _ => ⟨hf, s, fun w hw => v w fun h => hw (Finset.mem_insert_of_mem h)⟩,
      fun _ => ⟨hf', hupd, fun w hw => ?_⟩, by simp, by simp [eD], ?_⟩
    · beta_reduce
      rw [Function.update_of_ne fun h : w = Bs.v₁ => hw (h ▸ Finset.mem_insert_self _ _)]
      exact v' w fun h => hw (Finset.mem_insert_of_mem h)
    · rw [Fin.sum_univ_one, Fin.sum_univ_one, hR]
      congr 2
      funext w
      obtain ⟨w, hw⟩ := w
      by_cases h : w = Bs.v₁
      · subst h
        show Rf.p Bs.v₁ (φ Bs.v₁) = Rf.p' Bs.v₁ (Function.update φ' Bs.v₁ φo Bs.v₁)
        rw [Function.update_self, hp, v _ hv₁, v' _ hv₁]
        exact (hM.fin.sph _ hv₁).1
      · show Rf.p w (φ w) = Rf.p' w (Function.update φ' Bs.v₁ φo w)
        rw [Function.update_of_ne h]
        exact hfin w ((Finset.mem_insert.1 hw).resolve_left h)
  have hm := GlobalTheory.SquareAgree.PolMatchConst.match_of_polMatch Bs Γ Xc om om' R Rf hT _ _ hpm h0s
  obtain ⟨Φ₀, hΦ₀, hD0⟩ := hO.algB' Φ₀D h0a
  have hc1 : (-1 : D.host.E) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hk : GlobalTheory.SquareAgree.kapX X e hO.JX 1 = 1 := by
    apply Subtype.ext
    simp [GlobalTheory.SquareAgree.kapX]
  have key : ∀ Ψ ∈ GlobalTheory.SquareAgree.CoinvPass.relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁,
      ∃ Φ ∈ finRel ωB (algF ψ θ false A₁ B), GlobalTheory.SquareAgree.IsDatum Γ.M' ψ cB Ψ Φ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, Ψ₀, hΨ₀, rfl⟩ := hz
      obtain ⟨Φ₁, hΦ₁, hD1⟩ := hO.algB' Ψ₀ hΨ₀
      have hgu : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc1 hO.JW₁ g) = g :=
        (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc1 hO.JW₁).right_inv g
      have hW := hO.weilB Ψ₀ Φ₁ hD1 (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc1 hO.JW₁ g) 1
      rw [hgu, hk] at hW
      exact ⟨_, Submodule.subset_span ⟨_, GlobalTheory.SquareAgree.CoinvPass.conjUInv_mem_GfC W₁ Γ.V' (-1) hc1 hO.JW₁ Bs.v₁ g hg, Φ₁, hΦ₁,
        rfl⟩, GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hW hD1⟩
    | zero => exact ⟨0, zero_mem _, GlobalTheory.SquareAgree.CoinvPass.isDatum_zero⟩
    | add a b _ _ ha hb =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      obtain ⟨Φb, hb, hDb⟩ := hb
      exact ⟨Φa + Φb, add_mem ha hb, GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ hDa hDb⟩
    | smul c a _ ha =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      exact ⟨c • Φa, Submodule.smul_mem _ c ha, GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c hDa⟩
  obtain ⟨Ψ, hΨ, hDΨ⟩ := key _ hdiff
  have hrel : Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B) :=
    GlobalTheory.SquareAgree.CoinvPass.isDatum_unique cB.surjective (GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hD' hD0) hDΨ ▸ hΨ
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D h0s
  obtain ⟨N, C, hmod⟩ := GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hν₁ hT Φ₀ Φ₀D hD0
    hconv (by
      obtain ⟨C, k, hC⟩ := hbd 0
      exact ⟨C, k, fun g h => by simpa using hC g h⟩)
  have hlin : ∀ g h, thetaKO ωB g h (Φ' - Φ₀) = thetaKO ωB g h Φ' - thetaKO ωB g h Φ₀ := fun g h => by
    simp only [thetaKO, map_sub, _root_.Pi.sub_apply]
  have hint' : ∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h (Φ' - Φ₀)) 𝓕₁ ν₁ := fun h => by
    simp only [hlin]; exact (hint h).sub (hmod h).1
  have h0 := _root_.GlobalTheory.ThetaAgreeConv.thetaIntegral_eq_zero_of_finiteRelation hP hK hθ hTr hν₁ hw hstab hrel hint'
  funext h
  have e0 := congrFun h0 h
  have e1 : thetaInt ωB ν₁ 𝓕₁ Φ' h = thetaInt ωB ν₁ 𝓕₁ Φ₀ h := by
    simp only [thetaInt, hlin, _root_.Pi.zero_apply] at e0 ⊢
    rw [MeasureTheory.integral_sub (hint h) (hmod h).1] at e0
    exact sub_eq_zero.1 e0
  rw [_root_.Pi.smul_apply, e1,
    GlobalTheory.SquareAgree.thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (GlobalTheory.SquareAgree.kapX X e hO.JX) _ Φ hO.measW hO.domW
      (hO.theta_eq_A hD) h,
    GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (GlobalTheory.SquareAgree.kapX X e hO.JX) Φ₀D Φ₀
      hO.measW₁ hO.domW₁ (hO.theta_eq_B hD0) h,
    hc _ _ hm (GlobalTheory.SquareAgree.kapX X e hO.JX h), smul_eq_mul]
end
end
