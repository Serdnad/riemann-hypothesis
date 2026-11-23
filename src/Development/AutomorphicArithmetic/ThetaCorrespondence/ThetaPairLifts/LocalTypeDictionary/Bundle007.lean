module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle525
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle505
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle531
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle526
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle553
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle514
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle293
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle005
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsBis
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsTer
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerStd
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle004
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle001
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
theorem GlobalTheory.KTypeAdm.finiteDimensional_span_of_admissible_KType : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    ∀ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W → ψ ∈ W → GlobalTheory.KTypeProj.KStable θ M W →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    FiniteDimensional ℂ (GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) (W ⊓ GlobalTheory.CuspGK.gkGen θ M ψ)
      (GlobalTheory.CuspGK.gkGen θ M ψ)) := by
  intro hP D θ V S M hθ ψ hψ _hcusp W hW hψW hWK b hpos hherm _hK hskew
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  have hsm := GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ
  obtain ⟨U, hU, hlev⟩ := GlobalTheory.KTypeAdm.level_gkGen θ M hψ
  have hY : GlobalTheory.KTypeProj.KStable θ M (W ⊓ G) :=
    GlobalTheory.KTypeProj.kStable_inf θ M hWK (GlobalTheory.KTypeProj.kStable_gkGen θ M ψ)
  haveI hYf : FiniteDimensional ℂ ↥(W ⊓ G) := Submodule.finiteDimensional_of_le inf_le_left
  have hcont : ∀ f ∈ W ⊓ G, Continuous f := fun f hf => (hsm f hf.2).cont
  choose ρ hρc hρT using GlobalTheory.T.exists_continuousRep_rightTranslation_maxCompactStable θ V S M hθ (W ⊓ G) hYf hY hcont
  have hGK := GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ
  have hGsm : G ≤ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf => (hsm f hf).smooth
  have hGC : ∀ τ Z, ∀ f ∈ G, RderC θ V τ Z f ∈ G := fun τ Z f hf => by
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem (V := V) τ Z
    exact G.add_mem (hGK.lie τ _ h1 f hf) (G.smul_mem _ (hGK.lie τ _ h2 f hf))
  have hsym : ∀ τ k, ∀ x ∈ G, ∀ y ∈ G, b x (gelf θ V τ k y) = b (gelf θ V τ k x) y := fun τ =>
    GlobalTheory.T.gelfandInvariants_symmetric_of_derivativeAdjoint θ V hθ τ G hGsm (hGC τ) b (GlobalTheory.T.complexDerivative_adjoint_of_skew_form θ V τ G b (hskew τ))
  let F : D.what₂.Tau × ℕ → (GA D V → ℂ) → (GA D V → ℂ) := fun i => gelf θ V i.1 i.2
  have hFG : ∀ i, ∀ x ∈ G, F i x ∈ G := fun i => GlobalTheory.KTypeAdm.gelf_mem_of_isGKSub θ M hGK i.1 i.2
  have hFadd : ∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y := fun i x hx y hy =>
    (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) i.1 i.2).add x (hGsm hx) y (hGsm hy)
  have hFsmul : ∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x := fun i a x _ =>
    (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) i.1 i.2).smul a x
  have hFcomm : ∀ i j, ∀ x ∈ G, F i (F j x) = F j (F i x) := fun i j x hx =>
    GlobalTheory.CentreComm.comm_gelf (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) i.1 i.2)
      (fun Z => GlobalTheory.CentreComm.gelf_RderC hθ i.1 j.1 i.2 Z) j.2 x (hGsm hx)
  obtain ⟨Wz, hWz, hψz, hWzst⟩ := hψ.zfin
  haveI := hWz
  haveI : FiniteDimensional ℂ ↥(Wz ⊓ G) := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_jointEigenDecomposition_commuting_symmetricOps F (Wz ⊓ G) inferInstance
    (fun i x hx => ⟨hWzst i.1 i.2 x hx.1, hFG i x hx.2⟩) (fun i x hx y hy => hFadd i x hx.2 y hy.2)
    (fun i a x hx => hFsmul i a x hx.2) (fun i j x hx => hFcomm i j x hx.2) b (fun x hx => hpos x hx.2)
    (fun x hx y hy => hherm x hx.2 y hy.2) (fun i x hx y hy => hsym i.1 i.2 x hx.2 y hy.2)
  have hGS : G ≤ ⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ G ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h} := by
    refine GlobalTheory.CuspGK.gkGen_le θ M ?_ (GlobalTheory.T.isGKSubmodule_iSup_gelfandJointEigenspaces θ V S M hθ ψ hψ C)
    have := hC ψ ⟨hψz, GlobalTheory.CuspGK.mem_gkGen θ M ψ⟩
    refine (iSup₂_mono fun c _ => Submodule.span_mono ?_) this
    exact fun h hh => ⟨hh.1.2, hh.2⟩
  set P := GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) (W ⊓ G) G with hPdef
  have hPG : P ≤ G := GlobalTheory.KTypeProj.typeSpan_le _ _ _
  have hPst : ∀ i, ∀ x ∈ P, F i x ∈ P := fun i => GlobalTheory.T.gelfandInvariant_mem_intertwinedTypeSpan θ V S M hθ ψ hψ (W ⊓ G) i.1 i.2
  have hdec := GlobalTheory.T.mem_iSup_jointEigenspaces_inf_of_stableSubmodule F G P C hFG hFadd hFsmul hPG hPst (fun x hx => hGS hx)
  have htype : ∀ τ, ∀ h ∈ P, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) (ρ τ) h := by
    intro τ
    let Q : Submodule ℂ (GA D V → ℂ) :=
      { carrier := {h | GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) (ρ τ) h}
        add_mem' := fun ha hb x => Submodule.add_mem _ (ha x) (hb x)
        zero_mem' := fun x => Submodule.zero_mem _
        smul_mem' := fun c f hf x => Submodule.smul_mem _ c (hf x) }
    have hPQ : P ≤ Q := by
      refine iSup₂_le fun T hT => ?_
      rintro _ ⟨w, hw, rfl⟩
      exact hρT τ T hT.2 ⟨w, hw⟩
    exact fun h hh => hPQ hh
  have hfr : GlobalTheory.Published.AutFin.IsFrameFam V M.ε M.fr := fun τ => ⟨M.fr_unit τ, M.fr_gram τ⟩
  have hfin : ∀ c : D.what₂.Tau × ℕ → ℂ, FiniteDimensional ℂ
      (Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k)))) := fun c =>
    hP.harishChandraFinite D θ hθ V U hU M.ε M.fr hfr (fun _ => ↥(W ⊓ G)) ρ hρc _
  have hle : P ≤ C.sup fun c =>
      Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k))) := by
    intro x hx
    have := hdec x hx
    rw [← Finset.sup_eq_iSup] at this
    have key : ∀ c : D.what₂.Tau × ℕ → ℂ, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} ≤
        Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k))) := fun c =>
      Submodule.span_mono (by
        rintro h ⟨hP', hc⟩
        exact ⟨hsm h (hPG hP'), fun u hu hu' g => hlev h (hPG hP') u hu hu' g, fun τ => htype τ h hP',
          fun τ k => hc (τ, k)⟩)
    exact Finset.sup_mono_fun (fun c _ => key c) this
  haveI : ∀ c : D.what₂.Tau × ℕ → ℂ, FiniteDimensional ℂ
      (Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k)))) := hfin
  exact Submodule.finiteDimensional_of_le hle
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.admissible_KType_span_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    ∀ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W → ψ ∈ W → GlobalTheory.KTypeProj.KStable θ M W →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    FiniteDimensional ℂ (GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) (W ⊓ GlobalTheory.CuspGK.gkGen θ M ψ)
      (GlobalTheory.CuspGK.gkGen θ M ψ)) := by
  first | exact @_root_.GlobalTheory.KTypeAdm.finiteDimensional_span_of_admissible_KType | exact _root_.GlobalTheory.KTypeAdm.finiteDimensional_span_of_admissible_KType | (intros; apply _root_.GlobalTheory.KTypeAdm.finiteDimensional_span_of_admissible_KType <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), ∀ g ∈ UJset (N.M.ε τ), HasCtp θ N U (TyOf θ N ρ) τ (N.M.σ τ g) := by
  intro D θ hθ hp N U W _ _ ρ τ g hg
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hk : (N.M.fr τ)⁻¹ * g * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := conj_inv_mem hP hJ hg
  have comm : ∀ τ', τ' ≠ τ → ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ'),
      atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) * atTau θ N.V τ' h =
        atTau θ N.V τ' h * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) :=
    fun τ' hne h hh => GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm hne) _ hk h hh
  refine ⟨rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    exact hf.comp (continuous_mul_const _)
  · intro f f' _ _
    rfl
  · intro c f _
    rfl
  · rintro f ⟨⟨a1, a2, a3⟩, a4⟩
    refine ⟨⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ N.V f a1 τ _ hk, GlobalTheory.Cusp.isCuspFun_rTr a2 _,
      fun τ' => GlobalTheory.CuspGKForms.isTypeAt_rTr hθ (a3 τ') hk⟩, fun k hkU hkf x => ?_⟩
    simp only [rTr]
    rw [mul_assoc x, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc x]
    exact a4 k hkU hkf _
  · intro τ' hne f _ hf x
    have e : (fun k => rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)) f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) =
        fun k => f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) *
          GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) := funext fun k => by
      simp only [rTr, GlobalTheory.Published.AutFin.kAt]
      rw [mul_assoc x, mul_assoc x, comm τ' hne _
        (GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k)]
    show (fun k => _) ∈ _
    rw [e]
    exact hf _
  · intro τ' hne h hh f _
    funext x
    simp only [rTr]
    rw [mul_assoc x, mul_assoc x, comm τ' hne h hh]
  · intro τ' hne X hX f _
    funext x
    simp only [Rder, rTr, oneP]
    congr 1
    funext t
    rw [mul_assoc x, mul_assoc x, comm τ' hne _
      (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit N.V τ') hX t)]
  · intro φ _ x S v ℓ C hS _ h
    exact h.translate hσ.1 hS hg fun y hy => by
      simp only [res, rTr, at_mul hθ hP hJ hy hg, mul_assoc x]
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.placewise_decomposition_translation_invariant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), ∀ g ∈ UJset (N.M.ε τ), HasCtp θ N U (TyOf θ N ρ) τ (N.M.σ τ g) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_hasCtp_of_isClosed : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), (∀ f f' : GA D N.V → ℂ, f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U) → (0 : GA D N.V → ℂ) ∈ Cls θ N U → (∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U) → (∀ T T' : N.M.H τ → N.M.H τ, HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ T' → HasCtp θ N U (TyOf θ N ρ) τ (fun w => T w + T' w) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w)) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun _ => 0) := by
  intro D θ _ hp N U W _ _ ρ τ hadd _ hsmul
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ := (std_of_isDS hp.harishChandraModules (N.M.ds τ)).1
  have hs : ∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T →
      HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w) := by
    rintro c T ⟨A, hA, hm⟩
    refine ⟨fun φ => c • A φ, ⟨fun f hf => (hA.cont f hf).const_smul c, fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hsmul c _ (hA.maps f hf), fun τ' h f hf ht x => ?_, fun τ' h g hg f hf => ?_,
      fun τ' h X hX f hf => ?_⟩, fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).smul hσ hS c⟩
    · simp only [hA.add f f' hf hf', smul_add]
    · simp only [hA.smul a f hf, smul_comm c a]
    · exact Submodule.smul_mem _ c (hA.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, GlobalTheory.Mem.AutSpace.Rder_smul]
  refine ⟨?_, hs, ?_⟩
  · rintro T T' ⟨A, hA, hm⟩ ⟨A', hA', hm'⟩
    refine ⟨⟨fun φ => A φ + A' φ, ⟨fun f hf => (hA.cont f hf).add (hA'.cont f hf), fun f f' hf hf' => ?_,
      fun a f hf => ?_, fun f hf => hadd _ _ (hA.maps f hf) (hA'.maps f hf), fun τ' h f hf ht x => ?_,
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).add hσ (hm' φ hφ x S v ℓ C hS hc h) hS⟩,
      ⟨fun φ => A (A' φ), ⟨fun f hf => hA.cont _ (hA'.cont f hf), fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hA.maps _ (hA'.maps f hf), fun τ' h f hf ht => hA.keep τ' h _ (hA'.maps f hf) (hA'.keep τ' h f hf ht),
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => hm _ (hA'.maps φ hφ) x S _ ℓ C hS hc (hm' φ hφ x S v ℓ C hS hc h)⟩⟩
    · simp only [hA.add f f' hf hf', hA'.add f f' hf hf']
      abel
    · simp only [hA.smul a f hf, hA'.smul a f hf, smul_add]
    · exact Submodule.add_mem _ (hA.keep τ' h f hf ht x) (hA'.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf, hA'.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, hA'.lie τ' h X hX f hf]
      exact (GlobalTheory.Mem.AutSpace.Rder_add (hA.maps f hf).1.1.smooth (hA'.maps f hf).1.1.smooth hX).symm
    · simp only [hA'.add f f' hf hf', hA.add _ _ (hA'.cont f hf) (hA'.cont f' hf')]
    · simp only [hA'.smul a f hf, hA.smul a _ (hA'.cont f hf)]
    · simp only [hA'.tr τ' h g hg f hf, hA.tr τ' h g hg _ (hA'.maps f hf)]
    · simp only [hA'.lie τ' h X hX f hf, hA.lie τ' h X hX _ (hA'.maps f hf)]
  · simpa using hs 0 _ (hasCtp_id θ N U _ τ)
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.twist_placeDecomposition_hasCtp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), (∀ f f' : GA D N.V → ℂ, f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U) → (0 : GA D N.V → ℂ) ∈ Cls θ N U → (∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U) → (∀ T T' : N.M.H τ → N.M.H τ, HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ T' → HasCtp θ N U (TyOf θ N ρ) τ (fun w => T w + T' w) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w)) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun _ => 0) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.divisor_decomposition_of_local_factors : ∃ C1 : ℝ, 0 < C1 ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ (ch : Choice R) (CF : ℝ), ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.NormSum.Inp D →
      DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
      ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
      d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
      ∀ (a : ℝ) (v : VV ℂ (wt ch.G p.small)), InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
        InLat _ w (a + (vw w ((l : ℕ) : D.what₂.LL) : ℝ) * C1 *
            GlobalTheory.SumSize.TopInt.kerLoss ch.G δ C1 large₂.sc.b p.small p.big l (padicValNat l k))
          (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v) := by
  refine ⟨1, one_pos, ?_⟩
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch CF _ _ _ _ hI hDict S δ hL t p hp k d hk hd hz hP x y hR w l hl hw hA a v hv
  have hn := DefPair.nodes hp
  obtain ⟨k', hk', hd', hle, hsp⟩ := UpperTheory.WildA.depth large₂ hS.size d hP w l hl hw hA k hk hd
  obtain ⟨r, U, hU, e, hx⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.small hn.1 l hl x
  obtain ⟨r', U', hU', e', hy⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.big hn.2 l hl y
  have hmv := UpperTheory.WildA.move ch.S.Z hS.core.lev t p hp d x r y r' U U' hU hU'
  have hR' : ch.S.Z.IsRatAt d (r * x) (r' * y) := by
    intro i j
    have := UpperTheory.WildA.ratMove D _ _ _ _ _ _ hmv (fun i j => by
      have := hR i j
      rwa [Normal.kkIn, LinearMap.toMatrix_apply] at this) i j
    rwa [Normal.kkIn, LinearMap.toMatrix_apply]
  have h1 := UpperTheory.WildA.kerStd D large₂ Γ Pl0 T A Ks R F hS ch hI hDict S δ hL t p hp k' d hk' hd' hz hP _ _ hR' w l hl hw hsp hx hy
    large₂.sc.b
  have h2 := (UpperTheory.WildA.latMove D _ w a _ U v).2 hv
  rw [← e] at h2
  have h3 := UpperTheory.WildA.matLat D _ _ w l hl hw _ _ hx hy _ _ h1 a _ h2
  have h4 := LinearMap.congr_fun hmv v
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h4
  rw [h4, e'] at h3
  refine GlobalTheory.SumSize.TopInt.inLat_mono ((UpperTheory.WildA.latMove D _ w _ _ U' _).1 h3) ?_
  rw [mul_one]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (GlobalTheory.SumSize.TopInt.kerLoss_mono _ _ _ _ _ _ _ hle)
    (by exact_mod_cast GlobalTheory.SumSize.TopInt.vw_natCast_nonneg w l))
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem UpperTheory.WildA.ker_wild_ramification_map :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
          (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
          ∀ (ch : Choice R) (CF : ℝ), ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.NormSum.Inp D →
          DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
          ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
          d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
          ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
          ∀ (a : ℝ) (v : VV ℂ (wt ch.G p.small)), InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
            InLat _ w (a + (vw w ((l : ℕ) : D.what₂.LL) : ℝ) * C1 *
                GlobalTheory.SumSize.TopInt.kerLoss ch.G δ C1 large₂.sc.b p.small p.big l (padicValNat l k))
              (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v) := by
  refine ⟨1, one_pos, ?_⟩
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch CF _ _ _ _ hI hDict S δ hL t p hp k d hk hd hz hP x y hR w l hl hw hA a v hv
  have hn := DefPair.nodes hp
  obtain ⟨k', hk', hd', hle, hsp⟩ := UpperTheory.WildA.depth large₂ hS.size d hP w l hl hw hA k hk hd
  obtain ⟨r, U, hU, e, hx⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.small hn.1 l hl x
  obtain ⟨r', U', hU', e', hy⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.big hn.2 l hl y
  have hmv := UpperTheory.WildA.move ch.S.Z hS.core.lev t p hp d x r y r' U U' hU hU'
  have hR' : ch.S.Z.IsRatAt d (r * x) (r' * y) := by
    intro i j
    have := UpperTheory.WildA.ratMove D _ _ _ _ _ _ hmv (fun i j => by
      have := hR i j
      rwa [Normal.kkIn, LinearMap.toMatrix_apply] at this) i j
    rwa [Normal.kkIn, LinearMap.toMatrix_apply]
  have h1 := UpperTheory.WildA.kerStd D large₂ Γ Pl0 T A Ks R F hS ch hI hDict S δ hL t p hp k' d hk' hd' hz hP _ _ hR' w l hl hw hsp hx hy
    large₂.sc.b
  have h2 := (UpperTheory.WildA.latMove D _ w a _ U v).2 hv
  rw [← e] at h2
  have h3 := UpperTheory.WildA.matLat D _ _ w l hl hw _ _ hx hy _ _ h1 a _ h2
  have h4 := LinearMap.congr_fun hmv v
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h4
  rw [h4, e'] at h3
  refine GlobalTheory.SumSize.TopInt.inLat_mono ((UpperTheory.WildA.latMove D _ w _ _ U' _).1 h3) ?_
  rw [mul_one]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (GlobalTheory.SumSize.TopInt.kerLoss_mono _ _ _ _ _ _ _ hle)
    (by exact_mod_cast GlobalTheory.SumSize.TopInt.vw_natCast_nonneg w l))
end
end

section

section
namespace TwistAwayFromPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)
open GlobalTheory.SumSize
namespace GlobalTheory.CompanionTheory.Twist
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Host in
theorem twist_trivial_away_from_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → AwayK := by
  intro _
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w PP hP => ?_⟩⟩⟩
  have hr : ¬ (R.xiH (R.mu w)).UnrAt PP := (s.core.lev.Q_ram (R.mu w) PP).2 (Or.inl hP)
  by_cases hw : w ∈ R.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := s.mu_on w hw
    have e' : R.xiH (R.mu w) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    by_cases hd : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP
    · refine Or.inr fun l hl h1 h2 => hr fun x hx => ?_
      have hp : Formalism.EigenvalueLevelCeiling.plc w = l := by
        exact ((Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hl).1
          ((ringChar.spec _ l).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2)))
      have a1 := hd x hx
      have a2 := hψ.atl PP (hp ▸ h1) x
      rw [e']
      change (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
      rw [a1, a2, mul_one]
    · refine Or.inl (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))
      have key : ∀ p : ℕ, OverP D.host p PP → (p : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := fun p hp => by
        change algebraMap _ (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ PP.asIdeal
        rwa [map_natCast]
      unfold CharFrame.delAt at hd
      split_ifs at hd
      · exact Or.inr (Or.inr (Or.inr (key _ (by by_contra h; exact hd (R.C.isDel'.unr PP h)))))
      · exact Or.inr (Or.inr (Or.inl (key _ (by by_contra h; exact hd (R.C.isDel.unr PP h)))))
  · have e : R.mu w = A.μ0 := s.mu_off w hw
    refine absurd (fun x _ => ?_) hr
    rw [e, show R.xiH A.μ0 = 1 from s.core.lev.xi_base]
    rfl
end GlobalTheory.CompanionTheory.Twist
end
end
end TwistAwayFromPlace
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.twisted_local_factor_away_from_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → AwayK := by
  first | exact @_root_.TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.twist_trivial_away_from_level | exact _root_.TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.twist_trivial_away_from_level | (intros; apply _root_.TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.twist_trivial_away_from_level <;> assumption)
end
end
end
