module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle506
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle476
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsTypeAtCentral
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimCompactStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle514
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle598
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankSelfDualUnitary
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGammaBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle527

@[expose] public section

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

namespace GlobalTheory.MovedSD
open Matrix
end GlobalTheory.MovedSD
theorem GlobalTheory.MovedSD.moved_series_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    SD D (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) ∧ SD D (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  have hn := DefPair.nodes hp
  cases p with
  | chi i j => exact ⟨GlobalTheory.MovedSD.sd_latAt _ _ hn.2 y, GlobalTheory.MovedSD.sd_latAt _ _ hn.1 x⟩
  | top t j => exact ⟨GlobalTheory.MovedSD.sd_latAt _ _ hn.1 x, GlobalTheory.MovedSD.sd_latAt _ _ hn.2 y⟩
  | _ => exact hp.elim
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

theorem _root_.GlobalTheory.T.twisted_moved_series_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    SD D (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) ∧ SD D (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y) := by
  first | exact @_root_.GlobalTheory.MovedSD.moved_series_decomposition | exact _root_.GlobalTheory.MovedSD.moved_series_decomposition | (intros; apply _root_.GlobalTheory.MovedSD.moved_series_decomposition <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGKPet
open Matrix GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate GlobalTheory.CuspGK GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
theorem exists_petersson_pairing_gelfandKirillov_generator : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) ∧
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  intro hP D θ V S M hθ ψ h1 h2 _
  obtain ⟨b, b1, b2, b3, b4⟩ := exists_form_cuspSub (V := V) hP.cuspRapidDecay hθ
  have hle : gkGen θ M ψ ≤ cuspSub θ V := gkGen_le θ M (A := cuspSub θ V) ⟨h1, h2⟩
    ⟨fun _ _ hg _ hf => rTr_mem_cuspSub hθ hg.1 hf, fun _ _ hX _ hf => Rder_mem_cuspSub hθ hX hf⟩
  exact ⟨b, fun x hx => b1 x (hle hx), fun x hx y hy => b2 x (hle hx) y (hle hy),
    fun τ g hg x hx y hy => b3 τ g hg.1 x (hle hx) y (hle hy),
    fun τ X hX x hx y hy => b4 τ X hX x (hle hx) y (hle hy)⟩
end GlobalTheory.CuspGKPet
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.cusp_form_petersson_nonvanishing_gelfandKirillov : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) ∧
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  first | exact @_root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator | exact _root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator | (intros; apply _root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGKForms
open Matrix Filter Topology GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.CuspGK
open Formalism.IndefR.Mult
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
section Sig
variable (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} {S : SPar} {φ ψ : GA D V → ℂ}
include hPr hθ
theorem hasTypeAt_of_cuspForm_gK (hV : V.SigOK) (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ S φ) : φ ∈ typeSub θ V τ S :=
  GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ V τ S φ hPr.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique) hPr.harishChandraModules
    hPr.casselmanWallach hθ hV (goodPar_of_isTypeAt hV h) hφ h
theorem isTypeAt_of_cuspForm_gK (hV : V.SigOK) (h : IsTypeAt θ V τ S φ) (hψ : IsAutFunSm θ V ψ) (h' : ψ ∈ typeSub θ V τ S) :
    IsTypeAt θ V τ S ψ :=
  GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series θ V τ S ψ hPr.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique) hPr.harishChandraModules
    hPr.casselmanWallach hθ hV (goodPar_of_isTypeAt hV h) hψ h'
theorem isTypeAt_add_of_sigma (hV : V.SigOK) (hφ : IsAutFunSm θ V φ) (hψ : IsAutFunSm θ V ψ) (h : IsTypeAt θ V τ S φ)
    (h' : IsTypeAt θ V τ S ψ) : IsTypeAt θ V τ S (φ + ψ) :=
  _root_.GlobalTheory.CuspGKForms.isTypeAt_of_cuspForm_gK hPr hθ hV h (GlobalTheory.Mem.AutSpace.isAutFunSm_add hφ hψ)
    (add_mem (_root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV hφ h) (_root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV hψ h'))
theorem isTypeAt_liftDeriv_of_sigma (hV : V.SigOK) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ' S φ) : IsTypeAt θ V τ' S (Rder θ V τ X φ) := by
  refine _root_.GlobalTheory.CuspGKForms.isTypeAt_of_cuspForm_gK hPr hθ hV h (GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hφ) fun C hC δ hδ => ?_
  obtain ⟨t, ht⟩ := exists_quotient_near hθ hX hφ hC (half_pos hδ)
  have hk := GlobalTheory.Mem.Lift.exp_mem hX t
  have m1 : rTr V (oneP θ V τ X t) φ ∈ typeSub θ V τ' S :=
    _root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV (isAutFunSm_rTr_atTau D θ hθ V φ hφ τ _ hk) (isTypeAt_rTr hθ h hk)
  have m2 : ((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ) ∈ typeSub θ V τ' S :=
    Submodule.smul_mem _ _ (add_mem m1 (Submodule.smul_mem _ _ (_root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV hφ h)))
  obtain ⟨χ, hχ, h2⟩ := m2 C hC (δ / 2) (half_pos hδ)
  refine ⟨χ, hχ, fun x hx => ?_⟩
  have := norm_sub_le_norm_sub_add_norm_sub (Rder θ V τ X φ x)
    ((((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x) (χ x)
  linarith [ht x hx, h2 x hx]
theorem isTypeAt_add_cuspForm (hφ : IsAutFunSm θ V φ) (hψ : IsAutFunSm θ V ψ) (h : IsTypeAt θ V τ S φ)
    (h' : IsTypeAt θ V τ S ψ) : IsTypeAt θ V τ S (φ + ψ) := by
  obtain ⟨s, hs⟩ := exists_sigOK V
  exact _root_.GlobalTheory.CuspGKForms.isTypeAt_add_of_sigma (V := GlobalTheory.SmoothAutCheck.reSig V s) hPr hθ hs
    ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s φ).2 hφ) ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s ψ).2 hψ) h h'
theorem isTypeAt_liftDeriv_cuspForm {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ' S φ) : IsTypeAt θ V τ' S (Rder θ V τ X φ) := by
  obtain ⟨s, hs⟩ := exists_sigOK V
  exact _root_.GlobalTheory.CuspGKForms.isTypeAt_liftDeriv_of_sigma (V := GlobalTheory.SmoothAutCheck.reSig V s) hPr hθ hs hX
    ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s φ).2 hφ) h
end Sig
variable {S : D.what₂.Tau → SPar}
def cuspFormGKSubmodule (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ) (M : DSModel V S) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsKFinCuspOfType θ M f}
  zero_mem' := ⟨Formalism.IndefR.Mult.isAutFunSm_zero θ V, Formalism.IndefR.Mult.isCuspFun_zero V,
    fun τ => (GlobalTheory.TypeAtTest.isTypeAt_zero θ V).2
      ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, M.ds τ, M.fr_unit τ, M.fr_gram τ⟩,
    ⊥, inferInstance, zero_mem _, fun τ g _ _ h hh => by
      rw [Submodule.mem_bot] at hh ⊢
      subst hh
      rfl⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3, W, hW, a4, a5⟩ ⟨b1, b2, b3, W', hW', b4, b5⟩
    refine ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add a1 b1, GlobalTheory.MultMem.isCuspFun_add a1.toIsAutFun b1.toIsAutFun a2 b2,
      fun τ => _root_.GlobalTheory.CuspGKForms.isTypeAt_add_cuspForm hPr hθ a1 b1 (a3 τ) (b3 τ), W ⊔ W', inferInstance, Submodule.add_mem_sup a4 b4,
      fun τ g hg hk h hh => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hh
    exact Submodule.add_mem_sup (a5 τ g hg hk y hy) (b5 τ g hg hk z hz)
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, W, hW, a4, a5⟩
    exact ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c a1, Formalism.IndefR.Mult.isCuspFun_smul V a2 c,
      fun τ => GlobalTheory.Mem.Th.isTypeAt_smul c (a3 τ), W, hW, W.smul_mem c a4, a5⟩
theorem isGKSubmodule_cuspFormGKSubmodule (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ) (M : DSModel V S) :
    IsGKSub θ M (_root_.GlobalTheory.CuspGKForms.cuspFormGKSubmodule hPr hθ M) := by
  constructor
  · intro τ g hg f hf
    obtain ⟨a1, a2, a3, W, hW, a4, a5⟩ := hf
    exact ⟨isAutFunSm_rTr_atTau D θ hθ V f a1 τ g hg.1, GlobalTheory.Cusp.isCuspFun_rTr a2 _,
      fun τ' => isTypeAt_rTr hθ (a3 τ') hg.1, W, hW, a5 τ g hg.1 hg.2 f a4, a5⟩
  · intro τ X hX f hf
    obtain ⟨a1, a2, a3, W, hW, a4, a5⟩ := hf
    refine ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX a1, GlobalTheory.CuspLie.isCuspFun_Rder hθ hX a1 a2,
      fun τ' => _root_.GlobalTheory.CuspGKForms.isTypeAt_liftDeriv_cuspForm hPr hθ hX a1 (a3 τ'),
      (Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 ((Submodule.FG.map₂ _ Module.Finite.fg_top (GlobalTheory.CuspLie.fg_comap hW)).map _),
      ⟨derEnd hθ τ X ⟨f, a1.smooth⟩,
        Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := X)) (n := (⟨f, a1.smooth⟩ : SmFun θ V)) a4,
        GlobalTheory.CuspLie.derEnd_coe hθ hX ⟨f, a1.smooth⟩⟩, fun τ' g hg hk => ?_⟩
    have hr := isRealPt_atTau hθ τ' hg
    have hi : IsRealPt θ (atTau θ V τ' g)⁻¹ :=
      ⟨inv_mem hr.1, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V _⟩
    set k := atTau θ V τ' g
    have hle : Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype) ≤
        (((Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype).comap
          (rTrLin k)).comap (SmFun θ V).subtype := by
      refine Submodule.map₂_le.2 fun Z _ u hu => ?_
      refine ⟨_, Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := adAt θ k⁻¹ τ Z))
        (n := ⟨rTr V k u.1, rTr_mem hθ hr u.2⟩) (a5 τ' g hg hk _ hu), ?_⟩
      show RderC θ V τ (adAt θ k⁻¹ τ Z) (rTr V k u.1) = rTr V k (RderC θ V τ Z u.1)
      funext y
      have := congrFun (RderC_rTr hθ hi τ Z (rTr V k u.1)) (y * k)
      rw [show rTr V k⁻¹ (rTr V k u.1) = u.1 from funext fun y => by simp [rTr]] at this
      rw [rTr, this, rTr, mul_inv_cancel_right]
    rintro _ ⟨u, hu, rfl⟩
    exact hle hu
theorem isKFiniteCuspOfType_of_mem_gKGenerated : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M ψ → ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f :=
  fun hPr _ θ _ _ M hθ _ hψ _ hf => gkGen_le θ M (A := _root_.GlobalTheory.CuspGKForms.cuspFormGKSubmodule hPr hθ M) hψ (_root_.GlobalTheory.CuspGKForms.isGKSubmodule_cuspFormGKSubmodule hPr hθ M) hf
end GlobalTheory.CuspGKForms
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.cuspForm_gK_submodule_of_type : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M ψ → ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f := by
  first | exact @_root_.GlobalTheory.CuspGKForms.isKFiniteCuspOfType_of_mem_gKGenerated | exact _root_.GlobalTheory.CuspGKForms.isKFiniteCuspOfType_of_mem_gKGenerated | (intros; apply _root_.GlobalTheory.CuspGKForms.isKFiniteCuspOfType_of_mem_gKGenerated <;> assumption)
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
noncomputable section
namespace GlobalTheory.SplitCharValue
theorem splitCharValue_split_characters : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ x₀ : (Formalism.L2.Theta.AE D)ˣ,
    (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) →
    (Mod1All ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ Mod1All ((ch.G.chrT p x₀ : Circle) : ℂ)) ∧
    ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrT p x₀ : Circle) : ℂ) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp e he x₀ hx
  have hW := ch.W.om_is p (defPair_inRange hp)
  obtain ⟨e', he', hoff, a, hx'⟩ : ∃ e' : Formalism.L2.Theta.AE D, IsSplitIdem D e' ∧
      (∀ q, GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.OffPrime e' q) ∧
      ∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e' * a + (1 - e') := by
    obtain ⟨a, ha | ha⟩ := hx
    · exact ⟨e, he, fun _ h => h, a, ha⟩
    · exact ⟨cA D e, GlobalTheory.ConjAdjWeil.isSplitIdem_conj he, fun _ h => offPrime_conj h, a, ha⟩
  have hS := char_split_value D _ _ hW.hecS hW.resS e' he' x₀ a hx'
  have hT := char_split_value D _ _ hW.hecT hW.resT e' he' x₀ a hx'
  exact ⟨⟨hS.1, hT.1⟩, fun q _ hq => ⟨hS.2 q (hoff q hq), hT.2 q (hoff q hq)⟩⟩
end GlobalTheory.SplitCharValue
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

theorem _root_.GlobalTheory.T.twist_split_character_values : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ x₀ : (Formalism.L2.Theta.AE D)ˣ,
    (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) →
    (Mod1All ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ Mod1All ((ch.G.chrT p x₀ : Circle) : ℂ)) ∧
    ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrT p x₀ : Circle) : ℂ) := by
  first | exact @_root_.GlobalTheory.SplitCharValue.splitCharValue_split_characters | exact _root_.GlobalTheory.SplitCharValue.splitCharValue_split_characters | (intros; apply _root_.GlobalTheory.SplitCharValue.splitCharValue_split_characters <;> assumption)
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
open GlobalTheory.RatMoveJets
noncomputable section
namespace GlobalTheory.RatMoveIop
open Formalism.L2.KerInert Formalism.L2.KerInert.PullbackComparison GlobalTheory.ThLoc.AllPlaces
section Arith
variable {F : Type} [NormedField F] {lam : Qbar →+* F}
end Arith
variable {D : D7} {N N' : ℕ}
variable (A : Matrix.unitaryGroup (Fin N) D.host.E) (A' : Matrix.unitaryGroup (Fin N') D.host.E)
variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
theorem twist_pairing_pullback_of_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {δ t0 : ℂ}, Crv D D.host.ccK δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 → ∀ {N N' : ℕ} {e0 : VC D N N' → ℂ}, oddE0 D D.host.ccK δ t0 N N' e0 → Even (N * N') →
    ∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D M → SD D M' →
    ∀ (U : Matrix.unitaryGroup (Fin N) D.host.E) (U' : Matrix.unitaryGroup (Fin N') D.host.E),
    ∃ ε : ℂ, Mod1All ε ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q M (stdL D N) → EqAt D q M' (stdL D N') →
        EqAt D q (SDLat.smulLat U.1 M) (stdL D N) → EqAt D q (SDLat.smulLat U'.1 M') (stdL D N') → GlobalTheory.MovedKappaEx.UnitAt q ε) ∧
      ∀ z, Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) M M') e0
          (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK δ) U.1 U'.1 z) =
        ε * Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N')
          (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (SDLat.smulLat U.1 M) (SDLat.smulLat U'.1 M')) e0 z := by
  intro _ hI D δ t0 hC ht N N' e0 he _ M M' hM hM' A A'
  obtain ⟨ε, h1, h2⟩ := iop_move A A' D.host.ccK δ (hI D) hC ht he.2.2.2.1 hM hM'
  have hc : ∀ σ : Qbar →+* ℂ, NormOne σ ε := fun σ =>
    h1 ℂ σ fun τ => ⟨(norm_det_complex _ A').1, (norm_det_complex _ A).2⟩
  refine ⟨ε, ⟨(hc (algebraMap Qbar ℂ)).1, fun σ => (hc σ).2⟩, fun q _ a1 a2 a3 a4 lam => ?_, h2⟩
  obtain ⟨h3, h4⟩ := h1 ℂ_[q] lam fun τ => ⟨(norm_det_padic _ A' a2 a4).1, (norm_det_padic _ A a1 a3).2⟩
  rw [lamC, dite_eq_left h3]
  exact h4
end GlobalTheory.RatMoveIop
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
open GlobalTheory.RatMoveJets

theorem _root_.GlobalTheory.T.twist_pairing_rational_pullback_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {δ t0 : ℂ}, Crv D D.host.ccK δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 → ∀ {N N' : ℕ} {e0 : VC D N N' → ℂ}, oddE0 D D.host.ccK δ t0 N N' e0 → Even (N * N') →
    ∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D M → SD D M' →
    ∀ (U : Matrix.unitaryGroup (Fin N) D.host.E) (U' : Matrix.unitaryGroup (Fin N') D.host.E),
    ∃ ε : ℂ, Mod1All ε ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q M (stdL D N) → EqAt D q M' (stdL D N') →
        EqAt D q (SDLat.smulLat U.1 M) (stdL D N) → EqAt D q (SDLat.smulLat U'.1 M') (stdL D N') → GlobalTheory.MovedKappaEx.UnitAt q ε) ∧
      ∀ z, Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) M M') e0
          (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK δ) U.1 U'.1 z) =
        ε * Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N')
          (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (SDLat.smulLat U.1 M) (SDLat.smulLat U'.1 M')) e0 z := by
  first | exact @_root_.GlobalTheory.RatMoveIop.twist_pairing_pullback_of_rational | exact _root_.GlobalTheory.RatMoveIop.twist_pairing_pullback_of_rational | (intros; apply _root_.GlobalTheory.RatMoveIop.twist_pairing_pullback_of_rational <;> assumption)
end
end

section

section
open NumberField
namespace GlobalTheory.GamLoss
variable {E : Type} [Field E] [NumberField E]
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FunObj
variable {D : D7}
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
variable {D : D7}
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SumSize GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)
variable {D : D7}
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem finite_place_gamma_loss_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinGamK := by
  intro _
  refine ⟨0, fun CF _ => ⟨90, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ _ => ?_⟩⟩⟩
  have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : (1 : ℝ) ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  have hlb : (1 : ℝ) ≤ Real.log large₂.sc.b := by
    show (1 : ℝ) ≤ Real.log (Real.exp large₂.sc.L)
    rw [Real.log_exp]; exact hL
  exact finGamAt_of ch hC hb hlb
end GlobalTheory.GamLoss
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.gamma_factor_loss_at_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinGamK := by
  first | exact @_root_.GlobalTheory.GamLoss.finite_place_gamma_loss_bound | exact _root_.GlobalTheory.GamLoss.finite_place_gamma_loss_bound | (intros; apply _root_.GlobalTheory.GamLoss.finite_place_gamma_loss_bound <;> assumption)
end
end
