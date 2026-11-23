module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle351
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle425
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle067
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle054
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle056
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle028
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle029
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle014
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle068
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSubspaceKernelMaximal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGfCOfSuppAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.UpTypeLift
theorem upward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, IsTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hc τ
  have hN := hG.spaces.P (i + 1) (by omega)
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hR.inf hN.sigOK (GlobalTheory.NodePar.goodPar_of_sigOK (G.P (i + 1)) hN.sigOK τ)
    (_root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc)
    (_root_.GlobalTheory.T.theta_lift_preserves_type hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc τ)
end GlobalTheory.UpTypeLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twisted_upward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, IsTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType | exact _root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType | (intros; apply _root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType <;> assumption)
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
namespace GlobalTheory.SquareAgree
theorem theta_kernel_match_on_parabolic : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
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
    ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (p Φ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD 0) := by
  intro hR hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hRf Pi rf rl p p' hm
    Φ hΦ ΦD hΦD hD
  obtain ⟨K₁, g₁, ne₁, max₁, h₁⟩ := _root_.GlobalTheory.T.theta_subspace_kernel_maximal hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨K₂, g₂, ne₂, h₂⟩ := _root_.GlobalTheory.T.thetaSubspace_contains_polKernel hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf
  have hle : K₁ ≤ K₂ := fun x hx =>
    (h₂ x (g₁.1.1 hx)).2 (_root_.UpperTheory.Lit.HoweDuality.twisted_theta_kernel_condition hR hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf K₁ g₁ ne₁ x hx)
  rcases max₁ K₂ g₂ hle with h | h
  · rw [← h₁ Φ hΦ ΦD hΦD hD, ← h, h₂ ΦD hΦD]
  · exact absurd h ne₂
theorem theta_kernel_match_on_opposite_parabolic : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
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
    ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → (p' Φ₀ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ₀D) := by
  intro hR hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hM Pi rf rl p p' hm
    Φ₀ hΦ₀ Φ₀D hΦ₀D hD
  obtain ⟨K, hK, hKs, hKne⟩ := _root_.GlobalTheory.T.thetaSubspace_eq_ker_projDerivation_of_square hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨KD, hKD, hKDs, hKDne⟩ := _root_.GlobalTheory.T.thetaSubgroup_of_ker_derivation hP Bs Γ Xc om om' R Rf hM
  have h1 : K ≤ KD := fun Φ hΦ => (hKD Φ).2 ⟨hKs.le hΦ, _root_.UpperTheory.Lit.HoweDuality.twisted_theta_jet_condition hR hP Bs Γ Xc om om' R Rf hM K hKs hKne Φ hΦ⟩
  have h2 : KD = K := (_root_.GlobalTheory.T.thetaKernel_projection_isMax hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm K KD hK hKDs h1).resolve_right hKDne
  constructor
  · intro h0
    have hm : Φ₀D ∈ K := (hK Φ₀D).2 ⟨hΦ₀D, Φ₀, hΦ₀, hD, h0⟩
    rw [← h2] at hm
    exact ((hKD _).1 hm).2
  · intro hpm
    have hm : Φ₀D ∈ KD := (hKD _).2 ⟨hΦ₀D, hpm⟩
    rw [h2] at hm
    obtain ⟨_, Φ₁, _, hD₁, h0⟩ := (hK _).1 hm
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact h0
theorem theta_kernels_agree_up_to_scalar : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ ΦD Φ₀D,
      IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ → p Φ = p' Φ₀ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match Bs Γ Xc R Rf ΦD (s • Φ₀D) := by
  intro hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hTD.base.std
  have dA := GlobalTheory.SquareAgree.isDatum_linear Γ.M ψ hstd cA
  have dB := GlobalTheory.SquareAgree.isDatum_linear Γ.M' ψ hstd cB
  have lin := GlobalTheory.PolMatchLin.polMatch_linear Bs Γ Xc om om' R Rf hR.fin
  let G : Set (Pi × Pi) := {x | ∃ Φ ∈ algF ψ θ true A B, ∃ Φ₀ ∈ algF ψ θ false A₁ B, ∃ ΦD ∈ algD Γ.M Bs.ψ Bs.emb,
      ∃ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ ∧ IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D ∧ x = (p Φ, p' Φ₀)}
  have G0 : (0 : Pi × Pi) ∈ G :=
    ⟨0, zero_mem _, 0, zero_mem _, 0, zero_mem _, 0, zero_mem _, dA.1, dB.1, lin.1, Prod.ext (map_zero p).symm (map_zero p').symm⟩
  have Glin : ∀ x ∈ G, ∀ y ∈ G, ∀ c : ℂ, x + c • y ∈ G := by
    rintro _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩ _ ⟨Ψ, hΨ, Ψ₀, hΨ₀, ΨD, hΨD, Ψ₀D, hΨ₀D, k1, k2, k3, rfl⟩ c
    exact ⟨Φ + c • Ψ, add_mem hΦ (Submodule.smul_mem _ c hΨ), Φ₀ + c • Ψ₀, add_mem hΦ₀ (Submodule.smul_mem _ c hΨ₀),
      ΦD + c • ΨD, add_mem hΦD (Submodule.smul_mem _ c hΨD), Φ₀D + c • Ψ₀D, add_mem hΦ₀D (Submodule.smul_mem _ c hΨ₀D),
      dA.2 _ _ _ _ c h1 k1, dB.2 _ _ _ _ c h2 k2, lin.2 _ _ _ _ c h3 k3, by ext <;> simp⟩
  let S : Submodule ℂ (Pi × Pi) :=
    { carrier := G
      add_mem' := fun {x y} hx hy => by simpa using Glin x hx y hy 1
      zero_mem' := G0
      smul_mem' := fun c x hx => by simpa using Glin 0 G0 x hx c }
  have stf : ∀ g ∈ GfC X, ∀ x ∈ S, (rf g x.1, rf g x.2) ∈ S := by
    rintro g hg _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
    have a1 := hM.mapA.stabX.1 g hg Φ hΦ
    have b1 := hM.mapB.stabX.1 g hg Φ₀ hΦ₀
    obtain ⟨ΨD, hΨD, hΨ⟩ := hO.algA _ a1
    obtain ⟨Ψ₀D, hΨ₀D, hΨ₀⟩ := hO.algB _ b1
    have e1 := GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstd cA _ _ _ hΨ (hO.weilA ΦD Φ h1 1 g)
    have e2 := GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hΨ₀ (hO.weilB Φ₀D Φ₀ h2 1 g)
    refine ⟨_, a1, _, b1, ΨD, hΨD, Ψ₀D, hΨ₀D, hΨ, hΨ₀, ?_, ?_⟩
    · rw [e1, e2]
      exact _root_.GlobalTheory.SquareAgree.polarization_match_square_kappa hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM g hg ΦD hΦD Φ₀D hΦ₀D h3
    · rw [hM.mapA.eqf g hg Φ hΦ, hM.mapB.eqf g hg Φ₀ hΦ₀]
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, (rl τ Y x.1, rl τ Y x.2) ∈ S := by
    rintro τ Y hY _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
    obtain ⟨Φ', hΦ', hd⟩ := hM.mapA.stabX.2 τ Y hY Φ hΦ
    obtain ⟨Φ₀', hΦ₀', hd₀⟩ := hM.mapB.stabX.2 τ Y hY Φ₀ hΦ₀
    obtain ⟨ΨD, hΨD, hΨ⟩ := hO.algA _ hΦ'
    obtain ⟨Ψ₀D, hΨ₀D, hΨ₀⟩ := hO.algB _ hΦ₀'
    refine ⟨Φ', hΦ', Φ₀', hΦ₀', ΨD, hΨD, Ψ₀D, hΨ₀D, hΨ, hΨ₀,
      _root_.GlobalTheory.SquareAgree.LieEq.polarization_match_lie_derivative hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM τ Y hY Φ hΦ Φ' hΦ' Φ₀ hΦ₀ Φ₀' hΦ₀' hd hd₀ ΦD hΦD ΨD hΨD Φ₀D hΦ₀D Ψ₀D hΨ₀D h1 hΨ h2 hΨ₀ h3, ?_⟩
    rw [hM.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd, hM.mapB.eql τ Y hY Φ₀ hΦ₀ Φ₀' hΦ₀' hd₀]
  have k1 : ∀ x : Pi, ((x, 0) : Pi × Pi) ∈ S → x = 0 := by
    rintro x ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, hx⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, h0⟩ := hx
    have m0 := (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ₀ hΦ₀ Φ₀D hΦ₀D h2).1 h0.symm
    have m1 := lin.2 _ _ _ _ (-1) h3 m0
    rw [smul_zero, add_zero, neg_one_smul, add_neg_cancel] at m1
    exact (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ hΦ ΦD hΦD h1).2 m1
  have k2 : ∀ y : Pi, ((0, y) : Pi × Pi) ∈ S → y = 0 := by
    rintro y ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, hy⟩
    simp only [Prod.mk.injEq] at hy
    obtain ⟨h0, rfl⟩ := hy
    have m0 := (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ hΦ ΦD hΦD h1).1 h0.symm
    have m1 := lin.2 _ _ _ _ (-1) h3 m0
    rw [smul_zero, add_zero, neg_one_smul, add_neg_cancel] at m1
    exact (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ₀ hΦ₀ Φ₀D hΦ₀D h2).2 m1
  have on : ∀ x : Pi, ∃ y : Pi, ((x, y) : Pi × Pi) ∈ S := by
    intro x
    have hx : x ∈ (algF ψ θ true A B).map p := hM.mapA.onto ▸ Submodule.mem_top
    obtain ⟨Φ, hΦ, rfl⟩ := hx
    obtain ⟨ΦD, hΦD, h1⟩ := hO.algA Φ hΦ
    obtain ⟨Φ₀D, hΦ₀D, h3⟩ := GlobalTheory.SquareAgree.polMatch_onto Bs Γ Xc om om' R Rf hR ΦD hΦD
    obtain ⟨Φ₀, hΦ₀, h2⟩ := hO.algB' Φ₀D hΦ₀D
    exact ⟨p' Φ₀, Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.SquareAgree.eq_smul_of_stable_graph D X Pi rf rl hM.irred (_root_.GlobalTheory.SquareAgree.rank_polarization_pi_le_aleph0 hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM) S stf stl k1 k2 on
  refine ⟨c, hc0, ?_⟩
  intro Φ hΦ Φ₀ hΦ₀ ΦD Φ₀D hD hD₀ hSo hp
  obtain ⟨ΦD', hΦD', h1⟩ := hO.algA Φ hΦ
  have hΦD : ΦD ∈ algD Γ.M Bs.ψ Bs.emb := (GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstd cA _ _ _ hD h1) ▸ hΦD'
  obtain ⟨Φ₀D', hΦ₀D', h2⟩ := hO.algB Φ₀ hΦ₀
  have hΦ₀D : Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb := (GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hD₀ h2) ▸ hΦ₀D'
  obtain ⟨Φ₁D, hΦ₁D, m1⟩ := GlobalTheory.SquareAgree.polMatch_onto Bs Γ Xc om om' R Rf hR ΦD hΦD
  obtain ⟨Φ₁, hΦ₁, h4⟩ := hO.algB' Φ₁D hΦ₁D
  have hy := hc (p Φ) (p' Φ₁) ⟨Φ, hΦ, Φ₁, hΦ₁, ΦD, hΦD, Φ₁D, hΦ₁D, hD, h4, m1, rfl⟩
  have h5 := dB.2 _ _ _ _ (-c) h4 hD₀
  have hz : p' (Φ₁ + (-c) • Φ₀) = 0 := by rw [map_add (f := _), map_smul, hy, hp, neg_smul, add_neg_cancel]
  have m2 := (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM _ (add_mem hΦ₁ (Submodule.smul_mem _ _ hΦ₀)) _
    (add_mem hΦ₁D (Submodule.smul_mem _ _ hΦ₀D)) h5).1 hz
  have m3 := lin.2 _ _ _ _ (-1) m1 m2
  have e3 : Φ₁D + (-1 : ℂ) • (Φ₁D + (-c) • Φ₀D) = c • Φ₀D := by module
  rw [smul_zero, add_zero, e3] at m3
  exact GlobalTheory.SquareAgree.PolMatchConst.match_of_polMatch Bs Γ Xc om om' R Rf hTD _ _ m3 (Submodule.smul_mem _ c hSo)
end GlobalTheory.SquareAgree
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

theorem _root_.GlobalTheory.T.twisted_theta_kernels_agree_up_to_scalar : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ ΦD Φ₀D,
      IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ → p Φ = p' Φ₀ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match Bs Γ Xc R Rf ΦD (s • Φ₀D) := by
  first | exact @_root_.GlobalTheory.SquareAgree.theta_kernels_agree_up_to_scalar | exact _root_.GlobalTheory.SquareAgree.theta_kernels_agree_up_to_scalar | (intros; apply _root_.GlobalTheory.SquareAgree.theta_kernels_agree_up_to_scalar <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.SquareAgree
theorem derivative_eq_zero_iff_polarization_match : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
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
    ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → (p' Φ₀ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ₀D) := by
  intro hR hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hM Pi rf rl p p' hm
    Φ₀ hΦ₀ Φ₀D hΦ₀D hD
  obtain ⟨K, hK, hKs, hKne⟩ := _root_.GlobalTheory.T.thetaSubspace_eq_ker_projDerivation_of_square hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨KD, hKD, hKDs, hKDne⟩ := _root_.GlobalTheory.T.thetaSubgroup_of_ker_derivation hP Bs Γ Xc om om' R Rf hM
  have h1 : K ≤ KD := fun Φ hΦ => (hKD Φ).2 ⟨hKs.le hΦ, _root_.UpperTheory.Lit.HoweDuality.twisted_theta_jet_condition hR hP Bs Γ Xc om om' R Rf hM K hKs hKne Φ hΦ⟩
  have h2 : KD = K := (_root_.GlobalTheory.T.thetaKernel_projection_isMax hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm K KD hK hKDs h1).resolve_right hKDne
  constructor
  · intro h0
    have hm : Φ₀D ∈ K := (hK Φ₀D).2 ⟨hΦ₀D, Φ₀, hΦ₀, hD, h0⟩
    rw [← h2] at hm
    exact ((hKD _).1 hm).2
  · intro hpm
    have hm : Φ₀D ∈ KD := (hKD _).2 ⟨hΦ₀D, hpm⟩
    rw [h2] at hm
    obtain ⟨_, Φ₁, _, hD₁, h0⟩ := (hK _).1 hm
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact h0
end GlobalTheory.SquareAgree
end
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
namespace GlobalTheory.RatMovedAlg
theorem rational_moved_scalar_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ (κ : ℂ) (F : WO (GlobalTheory.Grid.neg A) WW → ℂ), GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F →
        X.ω t (γ, γ') X.vac = κ • F → IsAlgebraic ℚ κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 κ F hF e
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.T.jet_of_moved_vacuum_nonvanishing hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  obtain ⟨Ω, hΩ, hJ⟩ := _root_.GlobalTheory.T.bottom_translate_jets_algebraic hP hI hL hX (Finsupp.mapDomain Prod.fst k)
  obtain ⟨n', c', k', hc', hk', he'⟩ := _root_.GlobalTheory.T.moved_vacuum_jet_algebraic_combination hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 k
  have hψ : IsStdChar D W.ψ (-1) := (hX.is.weil t).std
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  have h0 : heisO W.ψ (GlobalTheory.Grid.neg A) WW 0 X.vac = X.vac := by
    funext w; simp [heisO, symplOH, symplO, hO]
  have alg : ∀ x : ℂ, IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := fun x => (mem_algebraicClosure_iff).symm
  have hg : IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [he', Finset.sum_div, alg]
    refine sum_mem fun p _ => ?_
    rw [mul_div_assoc]
    refine mul_mem ((alg _).1 (hc' p)) ((alg _).1 ?_)
    have := hJ 0 (by simp) (k' p) (hk' p)
    rwa [h0] at this
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  have hsum : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 =
      ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 := by
    rw [GlobalTheory.SpecFac.pureTensorO_sum hψ hθ _ _ _ _ Finset.univ c _
      (fun p _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv (w p))]
    simp [Finset.sum_apply]
  have hF' : IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [hsum, Finset.sum_div, alg]
    refine sum_mem fun p _ => ?_
    rw [mul_div_assoc]
    exact mul_mem ((alg _).1 (hc p)) ((alg _).1 (hJ (w p) (hw p) k rfl))
  have hsm : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = κ * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 := by
    rw [e, GlobalTheory.FiniteFock.pureTensorO_smul]; rfl
  have hne : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
    intro h0'; rw [h0', mul_zero] at hsm; exact hk hsm
  have hκ : κ = (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 / Ω) / (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [hsm]; field_simp
  rw [hκ, alg]
  exact div_mem ((alg _).1 hg) ((alg _).1 hF')
theorem rational_translate_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ, γ') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  obtain ⟨κ, F, hF, e⟩ := _root_.GlobalTheory.T.rational_vacuum_algebraic_combination hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  have hk := _root_.GlobalTheory.RatMovedAlg.rational_moved_scalar_algebraic hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 κ F hF e
  obtain ⟨n, c, w, hc, hw, he⟩ := hF.smul hk
  exact ⟨n, c, w, hc, hw, e.trans he⟩
end GlobalTheory.RatMovedAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.rationally_moved_vector_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ, γ') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @_root_.GlobalTheory.RatMovedAlg.rational_translate_algebraic_combination | exact _root_.GlobalTheory.RatMovedAlg.rational_translate_algebraic_combination | (intros; apply _root_.GlobalTheory.RatMovedAlg.rational_translate_algebraic_combination <;> assumption)
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
namespace GlobalTheory.SplitSourceAlg
theorem split_source_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ g ∈ GfC A, Formalism.L2.Theta.SuppAt e A g →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (g, 1) X.vac) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t N e P _ _ g hg _
  have hx : (GlobalTheory.Grid.ofSgn true A).symm g ∈ GfC (GlobalTheory.Grid.neg A) := by
    rw [GlobalTheory.SgnIdent.mem_GfC_sgn, MulEquiv.apply_symm_apply]; exact hg
  exact GlobalTheory.BotExpand.om_vac_algComb hX.is.isVac (GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1) hX.is.rigW.1
    (fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1) (fun τ => (hX.is.rigW.2.2 τ).1) (hX.is.weil t)
    hx (one_mem _)
end GlobalTheory.SplitSourceAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.split_source_vector_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ g ∈ GfC A, Formalism.L2.Theta.SuppAt e A g →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (g, 1) X.vac) := by
  first | exact @_root_.GlobalTheory.SplitSourceAlg.split_source_algebraic_combination | exact _root_.GlobalTheory.SplitSourceAlg.split_source_algebraic_combination | (intros; apply _root_.GlobalTheory.SplitSourceAlg.split_source_algebraic_combination <;> assumption)
end
end
