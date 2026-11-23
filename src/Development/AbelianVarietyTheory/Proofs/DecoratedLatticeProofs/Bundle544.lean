module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle436
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle432
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle536
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle215
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle541
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle080
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle282
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle424
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle458
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle416
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle345
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle469
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle504
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep

theorem isBiTheta_add' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {f g : WO A S → WO S A' → ℂ}
    (hf : IsBiTheta ψ A S A' f) (hg : IsBiTheta ψ A S A' g) : IsBiTheta ψ A S A' (f + g) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · intro n L L' hL hL' hLf hL'f u v
    exact (hf.smooth n L L' hL hL' hLf hL'f u v).add (hg.smooth n L L' hL hL' hLf hL'f u v)
  · simp only [Pi.add_apply]; rw [hf.quasiL, hg.quasiL]; ring
  · simp only [Pi.add_apply]; rw [hf.quasiR, hg.quasiR]; ring
  · obtain ⟨U, hU, hUf⟩ := hf.levL
    obtain ⟨V, hV, hVf⟩ := hg.levL
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    funext u
    have h1 := congrFun (hUf a ha.1 ha' v) u
    have h2 := congrFun (hVf a ha.2 ha' v) u
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  · obtain ⟨U, hU, hUf⟩ := hf.levR
    obtain ⟨V, hV, hVf⟩ := hg.levR
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    funext v
    have h1 := congrFun (hUf a ha.1 ha' u) v
    have h2 := congrFun (hVf a ha.2 ha' u) v
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]

theorem isBiTheta_zero' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} : IsBiTheta ψ A S A' 0 := by
  refine ⟨?_, fun n L L' _ _ _ _ u v => ?_, fun γ u v => by simp, fun γ u v => by simp,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ v => ?_⟩,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ u => ?_⟩⟩
  · simp only [Pi.zero_apply]; exact continuous_const
  · simp only [Pi.zero_apply]; exact contDiff_const
  · funext x; simp [heisO]
  · funext x; simp [heisO]

theorem isBiTheta_of_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] (Λ : SB (X × Y) →ₗ[ℂ] (WO A S → WO S A' → ℂ))
    (h : ∀ a b, IsBiTheta ψ A S A' (Λ (GlobalTheory.LocFlat.CFac.prodSB a b))) (Ξ : SB (X × Y)) : IsBiTheta ψ A S A' (Λ Ξ) := by
  have hmem : Ξ ∈ Submodule.span ℂ (Set.range fun q : SB X × SB Y => GlobalTheory.LocFlat.CFac.prodSB q.1 q.2) := by
    rw [GlobalTheory.T.span_schwartzBruhatProduct_eq_top X Y]; trivial
  have key : ∀ c : ℂ, IsBiTheta ψ A S A' (Λ (c • Ξ)) := by
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      intro c
      have e : c • GlobalTheory.LocFlat.CFac.prodSB q.1 q.2 = GlobalTheory.LocFlat.CFac.prodSB (c • q.1) q.2 := by
        change c • GlobalTheory.LocFlat.CFac.prodSBBil X Y q.1 q.2 = GlobalTheory.LocFlat.CFac.prodSBBil X Y (c • q.1) q.2
        rw [map_smul, LinearMap.smul_apply]
      rw [e]; exact h _ _
    | zero => intro c; rw [smul_zero, map_zero]; exact isBiTheta_zero'
    | add x y _ _ hx hy => intro c; rw [smul_add, map_add (f := _)]; exact isBiTheta_add' (hx c) (hy c)
    | smul a x _ hx => intro c; rw [smul_smul]; exact hx _
  simpa using key 1

theorem tri : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ T₁ T₂, (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ φ, IsContAut S.B.A φ → ∃ (A : Submodule ℂ (GA D S.B'.V → ℂ)) (τ : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) A) (T : SB (Matrix Q.n₁ Q.n₀ Q.k) →ₗ[ℂ] SB (Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), IsSmoothRep τ ∧ (∀ y (f : A), (τ y f).1 = rTrans (Q.gl₂ y) f.1) ∧ (∀ f, IsContAut S.B'.V f → Q.Typed f → f ∈ A) ∧ TriPos Q.ψk Q.μ₁ Q.μ₂ (σ + 1) τ T ∧ (∀ Φ₁ Φ₂ (f : A), HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1)) ∧ ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f : A, T Ξ₁ Ξ₂ f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f.1 1 1 1 := by
  intro D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ φ hφ
  have hBF := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)
  have hFB := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)
  have hCL := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.LocFlat.contrFactor
  have hν : Q.ν.IsAddHaarMeasure := Q.unitVol.1
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes (ofSplit Q.q) S.B Q.F.s Q.F.F₀ Q.F.G₀ Q.F.bes
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.LocMod.GValProof.core_of_bes (ofSplit Q.q) S.B' (Q.F.s * (ofSplit Q.q).xi) Q.F.F₂ Q.F.G₂ Q.F.bes'
  have hjac : (ofSplit Q.q).IsJacFrame S.J Q.F.s (-(ofSplit Q.q).xi ^ 2 * (ofSplit Q.q).hz S.B') Q.F.F₁ Q.F.G₁ := by
    rw [← GlobalTheory.LocMod.GValProof.hz_link (ofSplit Q.q) S.B S.B' S.l]; exact Q.F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF Q.k (ofSplit Q.q) Q.ν hν ψ Q.ψk Q.char (σ + 1) S.B S.J S.s₁ Q.F.s Q.F.s_ne _ _ (Q.c + 1 + 1)
    Q.F.F₀ C₀ Q.F.G₀ Q.F.F₁ Q.F.G₁ hC₀ Q.F.bes Q.F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB Q.k (ofSplit Q.q) Q.ν hν ψ Q.ψk Q.char σ S.J S.B' S.s₂ Q.F.s Q.F.s_ne _ _ (Q.c + 1)
    Q.F.F₁ Q.F.G₁ Q.F.F₂ C₂ Q.F.G₂ hjac hC₂ Q.F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL Q.k (ofSplit Q.q) Q.ν hν ψ hstd Q.ψk Q.char (σ + 1) σ S.B S.B' S.l S.J.W₀ S.vL Q.F.s Q.F.s_ne
    _ _ _ Q.F.F₀ C₀ Q.F.F₁ Q.F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hψkc : Continuous Q.ψk := by
    obtain ⟨-, hψk, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D Q.k (ofSplit Q.q) ψ hstd
    exact (hψk Q.ψk Q.char).1
  have hΛθ : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (Λ Ξ) := by
    haveI := GlobalTheory.SplitWeil.t2Space Q.k
    haveI : NonarchimedeanAddGroup Q.k := ⟨fun V hV => by
      obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
      exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
        GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
    haveI : TotallyDisconnectedSpace Q.k := inferInstance
    haveI : ∀ n n' : Type, T2Space (Matrix n n' Q.k) := fun n n' => inferInstanceAs (T2Space (n → n' → Q.k))
    haveI : ∀ n n' : Type, TotallyDisconnectedSpace (Matrix n n' Q.k) :=
      fun n n' => inferInstanceAs (TotallyDisconnectedSpace (n → n' → Q.k))
    haveI : LocallyCompactSpace (Matrix Q.n₁ Q.n₀ Q.k) := inferInstanceAs (LocallyCompactSpace (Q.n₁ → Q.n₀ → Q.k))
    haveI : LocallyCompactSpace (Matrix Q.n₂ Q.n₁ Q.k) := inferInstanceAs (LocallyCompactSpace (Q.n₂ → Q.n₁ → Q.k))
    refine isBiTheta_of_prod Λ fun Ξ₁ Ξ₂ => ?_
    obtain ⟨φ₀, φ₀', hφ₀⟩ := GlobalTheory.ContractionLocal.exists_normPair Q.ψk Q.ν hψkc hν Q.n₁
    obtain ⟨Ξ', h1, h2⟩ := hΛe (GlobalTheory.ContractionLocal.colTens φ₀ Ξ₁) (GlobalTheory.ContractionLocal.rowTens φ₀' Ξ₂)
    have e : Ξ' = GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂ :=
      Subtype.ext (funext fun q => by rw [h1, GlobalTheory.ContractionLocal.contr_tens, hφ₀, mul_one]; rfl)
    rw [← e, ← h2]
    exact (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D ψ hstd _ _ S.B S.B' S.l S.J.W₀ S.vL _ _ (hU₁.theta _) (hU₂.theta _)).1
  have hθ : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) :=
    fun Ξ => GlobalTheory.T.isJointlySmoothBiTheta_twoVarCombination D ψ hstd _ _ _ _ (hΛθ Ξ) c₁ c₂
  obtain ⟨T, hT⟩ := GlobalTheory.T.doubleThetaLiftValue_bilinear D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ hΛθ
  have key : ∀ Ξ₁ Ξ₂ (f : GlobalTheory.TriStep.space Q), (GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T Ξ₁ Ξ₂ f =
      GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f.1 := fun Ξ₁ Ξ₂ f => hT _ f
  refine ⟨GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.rep Q, (GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T, GlobalTheory.TriStep.smooth Q,
    fun y f => rfl, GlobalTheory.T.mem_space_of_typed_automorphic D ψ σ S Q, ⟨fun Ψ₁ => ⟨fun Ψ₂ g hg v => ?_, fun g Ψ Ψ' v h => ?_⟩, fun g Ψ₁ Ψ₁' Ψ₂ Ψ₂' h₁ h₂ => ?_⟩,
    GlobalTheory.T.doubleStepValue_eq_trilinearTensorValue D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁e hU₂e hΛe T hT, fun Ξ₁ Ξ₂ d₁ d₂ h₁ h₂ O₁ O₂ hO₁ hO₂ f => ?_⟩
  · rw [key, key]
    exact GlobalTheory.T.doubleLiftValue_equivariant_symmetricUnipotent D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ _ g hg v.1 v.2
  · rw [key, key]
    exact GlobalTheory.T.local_bimodel_translation D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ψ₁ Ψ Ψ' h (hθ _) v.1 v.2
  · ext1 f
    rw [key, key]
    exact GlobalTheory.T.doubleThetaLiftValue_invariant_middleGL D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ψ₁ Ψ₁' Ψ₂ Ψ₂' h₁ h₂ (hθ _) f.1 f.2
  · rw [key]
    exact GlobalTheory.TriStep.valK_comb D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁e hU₂e hΛe Ξ₁ Ξ₂ d₁ d₂ h₁ h₂ O₁ O₂ hO₁ hO₂ f.1 f.2

end GlobalTheory.TriStep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.FinOneProof



theorem finOne : ∀ D : D7, FinOne D := by
  intro D ψ hstd σ S Q a
  have hOm := GlobalTheory.T.weilDatum_localModel_formula D
  have hFL := GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D
  have hFLs := GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D
  have hBF := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D hFL hFLs hOm
  have hFB := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D hFL hFLs hOm
  have hCo := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.T.heisenbergInvariant_factors_contraction
  obtain ⟨-, hchar, hxi, -, hcomp⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D Q.k (ofSplit Q.q) ψ hstd
  obtain ⟨hψc, hψ1⟩ := hchar Q.ψk Q.char
  haveI := Q.unitVol.1
  have hsd : IsSelfDual Q.ψk Q.ν := isSelfDual_of_isUnitVol Q.ν Q.cond Q.unitVol
  have hc : Q.c = 2 * σ := by have := Q.F.bes.1; omega
  obtain ⟨μV, hμV⟩ := hcomp S.s₁.χV
  obtain ⟨μW, hμW⟩ := hcomp S.s₁.χW
  obtain ⟨μV', hμV'⟩ := hcomp S.s₂.χV
  obtain ⟨μW', hμW'⟩ := hcomp S.s₂.χW
  obtain ⟨C₀, hC₀⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D Q.k (ofSplit Q.q) _ (σ + 1) Q.F.s Q.F.s_ne).1 S.B Q.F.F₀).1
  obtain ⟨C₂, hC₂⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D Q.k (ofSplit Q.q) _ σ (Q.F.s * (ofSplit Q.q).xi)
    (mul_ne_zero Q.F.s_ne hxi)).1 S.B' Q.F.F₂).1
  have hsb := GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective Q.k Q.ψk Q.ν hψc inferInstance
  have hjac' : (ofSplit Q.q).IsJacFrame S.J Q.F.s (-(ofSplit Q.q).xi ^ 2 * (ofSplit Q.q).hz S.B') Q.F.F₁ Q.F.G₁ :=
    GlobalTheory.LocMod.GSuppTwo.hz_link (ofSplit Q.q) S.l ▸ Q.F.jac

  let ca : ℂ := (((μV * μW⁻¹) (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ)
  let Φa : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) := ca • Q.Φ₁

  let cx : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → ℂ := fun x => (((μV' * μW'⁻¹) (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)
  let Φx : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
    fun x => cx x • Q.Φ₂

  have step₁ : ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v),
      ∀ x, ∃ U, (ofSplit Q.q).IsModel ψ C₀ Q.F.F₁ U ∧ ∀ Ψ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k),
        Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1) →
        flatBF S.s₁ (S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) (comb ψ _ _ Q.D₁ f₁)) = U Ψ := by
    intro f₁ f₂ hvac g hg h₁ hh₁ x
    obtain ⟨⟨Tm, O, hTm, hO, hTO⟩, -⟩ := hvac
    have hcomb : comb ψ _ _ Q.D₁ f₁ = Tm Q.Φ₁ := by
      rw [← hTO]; exact (Q.dat₁.2 Tm hTm O Q.Φ₁ hO rfl).symm
    let Φ' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) :=
      ⟨om μV⁻¹ a x Φa.1, om_mem_SB _ _ _ Φa.2⟩
    have hloc : S.s₁.om (Q.gl₀ a, Q.gl₁ x) (Tm Q.Φ₁) = Tm Φ' :=
      hOm Q.k (ofSplit Q.q) ψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil μV μW hμV hμW _ _ Q.F.G₀ Q.F.G₁ Tm hTm
        (Q.gl₀ a) a (Q.gl₁ x) x (Q.loc₀ a) (Q.loc₁ x) Q.Φ₁ Φ' (by
          funext z; simp only [Φ', Φa, ca, om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    have hmod := GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hstd S.B.V S.J.W _ _ S.s₁.om S.s₁.weil _ _ Q.F.G₀ Q.F.G₁
      Tm hTm g hg h₁ hh₁
    obtain ⟨U, hU, hflat⟩ := hBF Q.k (ofSplit Q.q) Q.ν inferInstance ψ Q.ψk Q.char (σ + 1) S.B S.J S.s₁ Q.F.s Q.F.s_ne _ _
      (Q.c + 1 + 1) Q.F.F₀ C₀ Q.F.G₀ Q.F.F₁ Q.F.G₁ hC₀ Q.F.bes Q.F.jac _ hmod
    refine ⟨U, hU, fun Ψ hΨ => ?_⟩
    have hm : S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) = S.s₁.om (g, h₁) * S.s₁.om (Q.gl₀ a, Q.gl₁ x) := by
      rw [← map_mul, Prod.mk_mul_mk]
    rw [hcomb, hm, Module.End.mul_apply, hloc]
    exact hflat Φ' Ψ hΨ

  have step₂ : ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v),
      ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v), ∀ x y, ∃ U, (ofSplit Q.q).IsModel ψ Q.F.F₁ C₂ U ∧
        ∀ Ψ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k), Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) (om μV'⁻¹ x y (Φx x).1) →
        flatFB S.s₂ (S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) (comb ψ _ _ Q.D₂ f₂)) = U Ψ := by
    intro f₁ f₂ hvac h₁ hh₁ h₂ hh₂ x y
    obtain ⟨-, ⟨Tm, O, hTm, hO, hTO⟩⟩ := hvac
    have hcomb : comb ψ _ _ Q.D₂ f₂ = Tm Q.Φ₂ := by
      rw [← hTO]; exact (Q.dat₂.2 Tm hTm O Q.Φ₂ hO rfl).symm
    let Φ' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
      ⟨om μV'⁻¹ x y (Φx x).1, om_mem_SB _ _ _ (Φx x).2⟩
    have hloc : S.s₂.om (Q.gl₁ x, Q.gl₂ y) (Tm Q.Φ₂) = Tm Φ' :=
      hOm Q.k (ofSplit Q.q) ψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil μV' μW' hμV' hμW' _ _ Q.F.G₁ Q.F.G₂ Tm hTm
        (Q.gl₁ x) x (Q.gl₂ y) y (Q.loc₁ x) (Q.loc₂ y) Q.Φ₂ Φ' (by
          funext z; simp only [Φ', Φx, cx, om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    have hmod := GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hstd S.J.W S.B'.V _ _ S.s₂.om S.s₂.weil _ _ Q.F.G₁ Q.F.G₂
      Tm hTm h₁ hh₁ h₂ hh₂
    obtain ⟨U, hU, hflat⟩ := hFB Q.k (ofSplit Q.q) Q.ν inferInstance ψ Q.ψk Q.char σ S.J S.B' S.s₂ Q.F.s Q.F.s_ne _ _
      (Q.c + 1) Q.F.F₁ Q.F.G₁ Q.F.F₂ C₂ Q.F.G₂ hjac' hC₂ Q.F.bes' _ hmod
    refine ⟨U, hU, fun Ψ hΨ => ?_⟩
    have hm : S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) = S.s₂.om (h₁, h₂) * S.s₂.om (Q.gl₁ x, Q.gl₂ y) := by
      rw [← map_mul, Prod.mk_mul_mk]
    rw [hcomb, hm, Module.End.mul_apply, hloc]
    exact hflat Φ' Ψ hΨ
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.fourierJacobi_flatMap_support_finite_cells Q.k Q.ψk hψc hψ1 Q.ν inferInstance Q.n₁ Q.n₀ (Q.c + 1 + 1) (σ + 1 + 1) (by omega) (by omega)
    μV⁻¹ Q.L₁.J Q.co₁.1 Φa a
  refine ⟨T₁, ?_, ?_⟩
  · intro f₁ f₂ hvac g hg h₁ hh₁ x hne
    obtain ⟨U, -, hU⟩ := step₁ f₁ f₂ hvac g hg h₁ hh₁ x
    let Ψ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ (om_mem_SB μV⁻¹ a x Φa.2)⟩
    rw [hU Ψ rfl] at hne
    have hne' : GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1) ≠ 0 := by
      intro h0
      apply hne
      have : Ψ = 0 := Subtype.ext h0
      rw [this, map_zero]
    obtain ⟨β, r, hr, t, ht, j, hj, hx⟩ := hT₁ x hne'
    refine ⟨t, ht, colE (Q.c + 1 + 1) (σ + 1 + 1) β * r, ?_, j, hj, hx⟩
    exact (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D Q.k (ofSplit Q.q)).2.1 Q.n₁ (Q.c + 1 + 1) (σ + 1) S.J Q.F.s _ Q.F.F₁ Q.F.G₁ Q.F.jac _ β r hr
      (Q.loc₁ _)
  · intro x
    obtain ⟨T₂, hT₂⟩ := GlobalTheory.T.localFlatMapContraction_support_finitelyManyCells Q.k Q.ψk hψc hψ1 Q.ν hsd Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) (by omega) μV⁻¹ μV'⁻¹
      Q.L₂.J Q.co₂.1 Φa (Φx x) a x
    refine ⟨T₂, ?_⟩
    intro f₁ f₂ hvac g hg h₁ hh₁ h₂ hh₂ y hne
    obtain ⟨U₁, hU₁, hf₁⟩ := step₁ f₁ f₂ hvac g hg h₁ hh₁ x
    obtain ⟨U₂, hU₂, hf₂⟩ := step₂ f₁ f₂ hvac h₁ hh₁ h₂ hh₂ x y
    let Ψ₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ (om_mem_SB μV⁻¹ a x Φa.2)⟩
    let Ψ₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1) (σ + 1) (by omega)).2 (by omega)).1 _ (om_mem_SB μV'⁻¹ x y (Φx x).2)⟩
    obtain ⟨Λ, -, hΛ⟩ := hCo Q.k (ofSplit Q.q) Q.ν inferInstance ψ hstd Q.ψk Q.char (σ + 1) σ S.B S.B' S.l S.J.W₀ S.vL
      Q.F.s Q.F.s_ne _ _ _ Q.F.F₀ C₀ Q.F.F₁ Q.F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
    obtain ⟨Ξ, hΞ, hΞΛ⟩ := hΛ Ψ₁ Ψ₂
    unfold Dbl2.con at hne
    rw [hf₁ Ψ₁ rfl, hf₂ Ψ₂ rfl, hΞΛ] at hne
    have hne' : GlobalTheory.LocFlat.contr Q.ψk Q.ν (GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1))
        (GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) (om μV'⁻¹ x y (Φx x).1)) ≠ 0 := by
      intro h0
      apply hne
      have : Ξ = 0 := Subtype.ext (hΞ.trans h0)
      rw [this, map_zero]
    obtain ⟨r, hr, t, ht, j, hj, hy⟩ := hT₂ y hne'
    exact ⟨t, ht, r, (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D Q.k (ofSplit Q.q)).2.2 Q.n₂ (Q.c + 1) σ S.B' (Q.F.s * (ofSplit Q.q).xi) Q.F.F₂ Q.F.G₂
      Q.F.bes' _ r hr (Q.loc₂ r), j, hj, hy⟩

end GlobalTheory.QPl.FinOneProof
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.VacSecondPf

variable {D : D7}

theorem latO_of_none (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (hP : ∀ v, ¬ P v) : latO S T LS LT P = ⊥ := by
  rw [eq_bot_iff, latO, AddSubgroup.closure_le]
  rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
  have h0 : α = 0 := by
    ext v : 1
    exact hα v (hP v)
  subst h0
  rw [SetLike.mem_coe, AddSubgroup.mem_bot]
  have hp : pairA D.host.F 0 0 = 0 := rfl
  ext i j
  simp [hp]

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem vac_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (P : Pl D → Prop), (∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v ∧ UnrAt s v) → ∀ f, Vac ψ J.W B.V LV LW P f → ∀ h₁ ∈ grpOff J.W P, ∀ h₂ ∈ grpOff B.V P, Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s (s.om (h₁, h₂) f)) := by
  intro D ψ σ J B s LV LV₀ LW LW₀ P hP f hf h₁ hh₁ h₂ hh₂
  have hflat : ∀ Q : Pl D → Prop, IsFlatFB s Q (flatFB s) := fun Q => (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ Q).2 σ J B s
  have htheta : IsThetaFunO ψ J.W B.V (s.om (h₁, h₂) f) := s.weil.om_pres _ _ hf.1
  have hth0 : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (h₁, h₂) f)) := (hflat P).Heisenberg₂.theta _ htheta
  by_cases hne : ∃ v, P v
  · obtain ⟨v₀, hv₀⟩ := hne
    have a₀ := (hP v₀ hv₀).1
    have hT : ∀ v, P v → Tame D v := fun v hv => (hP v hv).1.tame
    have L1 := GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW a₀.sdV a₀.sdW P hT
    have L0 := GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ LV₀ LW₀ a₀.sdV₀ a₀.sdW₀ P hT
    have hg : Vac ψ J.W B.V LV LW P (s.om (h₁, h₂) f) := (L1 f).2.1 hf h₁ hh₁ h₂ hh₂
    have hgv := ((L1 _).1.mp hg).2
    refine (L0 _).1.mpr ⟨hth0, fun v hv => ?_⟩
    exact (GlobalTheory.T.jacobiToBesselFlatMapSupport_proof D ψ σ J B s LV LV₀ LW LW₀ v (hP v hv).1 (hP v hv).2 (flatFB s) (hflat (· = v))
      ((GlobalTheory.T.flatMaps_heisenbergTranslation_law D ψ (· = v)).2 σ J B s) _ (hgv v hv)).1
  · push_neg at hne
    have hbot := latO_of_none J.W₀ B.V₀ (LV₀ : Set _) (LW₀ : Set _) P hne
    refine ⟨hth0, ?_, ?_⟩
    · intro u hu
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [two_nsmul, add_zero, heisO_zero]
    · intro e _ u hu _
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [heisO_zero]

end GlobalTheory.VacSecondPf
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.unfoldedBessel_continuous_leftInvariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → Continuous (unfF s vL Y G Φ) ∧ ∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, unfF s vL Y G Φ (γ * h) = unfF s vL Y G Φ h := by
  first | exact @GlobalTheory.Unf.FB.unfF_continuous_invariant | exact GlobalTheory.Unf.FB.unfF_continuous_invariant | (intros; apply GlobalTheory.Unf.FB.unfF_continuous_invariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepCell.LeftSecond

variable {D : D7}

theorem contAut_translate {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_of_mem_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  have hadd : ∀ {f g : GA D V → ℂ}, IsContAut V f → IsContAut V g → IsContAut V (f + g) := fun hf hg =>
    ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  have hsmul : ∀ {f : GA D V → ℂ}, IsContAut V f → ∀ c : ℂ, IsContAut V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact hsmul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact hadd hx hy
  | zero =>
    have h0 : IsContAut V (0 : GA D V → ℂ) := ⟨fun _ _ _ => rfl, continuous_const⟩
    simpa using h0
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact hadd (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact hsmul (h x) c

theorem theta_comb {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {P : Pl D → Prop}
    {e : WO S T →₀ ℂ} (he : CombAt P e) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T e f) :=
  (GlobalTheory.HeisComb.main D ψ S T).2.2.1 e f hf
    ((GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.1 e he).1 hψ

theorem integ_left_second : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (r * q₂) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f hf r hr q₁ q₂
  have hΦ₁ := theta_comb hc.std (hv.atG j).1 (theta_comb hc.std (hF.atQ j).1 h₁.1)
  have hΦ₂ := theta_comb hc.std (hv.atG (j + 1)).1 (theta_comb hc.std (hF.atQ (j + 1)).1 h₂.1)
  obtain ⟨J, χ, hle⟩ := ht.CC (j + 1 + 1) (by omega)
  have hfc : IsContAut (c.V (j + 1 + 1)) f := hf ▸ contAut_translate _ (contAut_of_mem_multT (hle G.2) x)
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => congrArg (w.ε j α g * ·) ?_
  exact (GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof D c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sBF j (σ + 1) h)
    (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ hΦ₁ hΦ₂ (φ α) (hv.ram j _ (hφ α)).1 g q₁ q₂).2 f hfc r hr

end GlobalTheory.DStepCell.LeftSecond

end
end
