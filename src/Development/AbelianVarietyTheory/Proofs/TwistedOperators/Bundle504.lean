module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle238
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle396
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle003
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.IdemSubDiff

variable {D : D7} [DecidableEq (Pl D.host.E)]

theorem comp_sum {es : Pl D.host.E → AE D} {S : Finset (Pl D.host.E)}
    (h : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP) :
    infPart D (∑ PP ∈ S, es PP) = 0 ∧
      ∀ w, cpt (D := D) w (toEAf D (∑ PP ∈ S, es PP)) = if w ∈ S then 1 else 0 := by
  refine ⟨?_, fun w => ?_⟩
  · rw [GlobalTheory.FunObj.Comparison₂.hom_sum]
    exact Finset.sum_eq_zero fun Q hQ => (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) (h Q hQ)).1
  · rw [GlobalTheory.FunObj.Comparison₂.hom_sum, GlobalTheory.FunObj.Comparison₂.hom_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single_of_mem w hw fun Q hQ hne => (cpt_of_isIdemAt (h Q hQ)).2 w hne.symm]
      exact (cpt_of_isIdemAt (h w hw)).1
    · exact Finset.sum_eq_zero fun Q hQ => (cpt_of_isIdemAt (h Q hQ)).2 w fun h' => hw (h' ▸ hQ)

theorem isIdemSum_sdiff : ∀ {D : D7} [DecidableEq (Pl D.host.E)] {e e₀ : AE D} {P P₀ : Finset (Pl D.host.E)},
    IsIdemSum e P → IsIdemSum e₀ P₀ → P₀ ⊆ P → IsIdemSum (e - e₀) (P \ P₀) ∧ e₀ * (e - e₀) = 0 := by
  intro D _ e e₀ P P₀ h h0 hsub
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  obtain ⟨i0, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum h0
  obtain ⟨j0, d⟩ := comp_sum hes
  rw [← he] at j0 d
  have hes0 : ∀ PP ∈ P₀, Formalism.L2.NTheta.IsIdemAt (es PP) PP := fun PP hPP => hes PP (hsub hPP)
  obtain ⟨k0, k⟩ := comp_sum hes0
  have he0 : e₀ = ∑ PP ∈ P₀, es PP := by
    refine GlobalTheory.FunObj.ae_ext (by rw [i0, k0]) fun w => ?_
    rw [k w]
    split_ifs with hw
    · exact c1 w hw
    · exact c0 w hw
  have hdiff : e - e₀ = ∑ PP ∈ P \ P₀, es PP := by
    rw [he, he0, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hmul : e * (e - e₀) = e - e₀ := by
    refine GlobalTheory.FunObj.ae_ext (by simp only [RingHom.map_mul, RingHom.map_sub, j0, i0, sub_zero, mul_zero]) fun w => ?_
    simp only [RingHom.map_mul, RingHom.map_sub, d w]
    by_cases hw : w ∈ P
    · rw [if_pos hw, one_mul]
    · have hw0 : w ∉ P₀ := fun h' => hw (hsub h')
      rw [if_neg hw, c0 w hw0, zero_mul, sub_zero]
  have horth : e₀ * (e - e₀) = 0 := by
    refine GlobalTheory.FunObj.ae_ext (by simp only [RingHom.map_mul, RingHom.map_sub, j0, i0, sub_zero, mul_zero, RingHom.map_zero]) fun w => ?_
    simp only [RingHom.map_mul, RingHom.map_sub, RingHom.map_zero, d w]
    by_cases hw0 : w ∈ P₀
    · rw [c1 w hw0, if_pos (hsub hw0), sub_self, mul_zero]
    · rw [c0 w hw0, zero_mul]
  refine ⟨⟨⟨es, fun PP hPP => hes PP (Finset.mem_sdiff.1 hPP).1, hdiff⟩, ?_⟩, horth⟩
  have h1 : (e - e₀) * cA D (e - e₀) = ((e - e₀) * cA D (e - e₀)) * (e * cA D e) := by
    conv_lhs => rw [← hmul]
    rw [map_mul]
    ring
  rw [h1, hc, mul_zero]

end GlobalTheory.IdemSubDiff
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
noncomputable section

namespace GlobalTheory.ArchLineSum

open GlobalTheory.SplitScalar GlobalTheory.LatVac

variable {D : D7}

theorem fstA_realAd (t : ℝ) : fstA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = fstA D.host.F (GlobalTheory.WittLevi.realAd D t) := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective
  show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm _) = _
  rw [RingEquiv.apply_symm_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  ext w
  · show t = InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).symm t)
    exact ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).apply_symm_apply t).symm
  · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)

theorem infPart_realAd (t : ℝ) : infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) =
    infPart D (GlobalTheory.WittLevi.realE D t) := by
  show fstA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) = fstA D.host.F (GlobalTheory.WittLevi.realAd D t) ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [fstA_realAd]

theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : ℝ) :
    θ ρ (infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t))) = t := by
  rw [infPart_realAd]; exact GlobalTheory.WittLevi.theta_realE hθ ρ t

theorem finPart_smul (u : AF D.host.F) (a : AE D) :
    finPart D (u • a) = (sndA D.host.F u ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a := by
  rw [Algebra.smul_def, map_mul]; rfl

theorem infPart_smul (u : AF D.host.F) (a : AE D) :
    infPart D (u • a) = infPart D (algebraMap (AF D.host.F) (AE D) u) * infPart D a := by
  rw [Algebra.smul_def, map_mul]



theorem realAd_smul_eq {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {w : WO S T}
    (hw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w) (t : ℝ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w = ∑ τ, lineAt θ τ (compAt θ τ w) t := by
  classical
  have hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w)) := fun τ =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  ext i j
  rw [← sub_eq_zero]
  apply GlobalTheory.StdUnn.RealComp.eq_zero_of_parts
  · rw [← GlobalTheory.StdUnn.RealComp.theta_zero_iff hθ]
    intro ρ

    rw [(infPart D).map_sub, (θ ρ).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (infPart D), map_sum (θ ρ)]
    have e1 : ∀ τ, θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) =
        if ρ = τ then (t : ℂ) * θ ρ (infPart D (w i j)) else 0 := by
      intro τ
      have := congrFun (congrFun ((hL τ).2.2 t ρ) i) j
      change θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) = _ at this
      rw [this]
      split_ifs with h
      · subst h; rfl
      · rfl
    rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_ite_eq Finset.univ ρ, if_pos (Finset.mem_univ _)]
    show θ ρ (infPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j)) = _
    rw [infPart_smul, (θ ρ).map_mul, theta_realAd hθ]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [(finPart D).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (finPart D)]
    show finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j) = _
    rw [finPart_smul, show sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul,
      zero_mul]
    exact (Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 t) i) j).symm

end GlobalTheory.ArchLineSum

namespace GlobalTheory.ArchLineSum

open GlobalTheory.SplitScalar GlobalTheory.LatVac



theorem hasDerivAt_realAd_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
    ∀ w : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w → ∀ x : WO S T,
      HasDerivAt (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x)
        (∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x) 0 := by
  intro D ψ θ hψ hθ S T f hf w hw x
  classical
  have hc : Continuous ψ := hψ.1.1
  have hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w)) := fun τ =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  let Λ : (D.what₂.Tau → ℝ) →+ WO S T :=
    ∑ τ, (lineAt θ τ (compAt θ τ w)).comp (Pi.evalAddMonoidHom (fun _ : D.what₂.Tau => ℝ) τ)
  have hΛ : ∀ s, Λ s = ∑ τ, lineAt θ τ (compAt θ τ w) (s τ) := fun s => by
    simp [Λ]
  have hΛc : Continuous Λ := by
    rw [show (Λ : (D.what₂.Tau → ℝ) → WO S T) = fun s => ∑ τ, lineAt θ τ (compAt θ τ w) (s τ) from funext hΛ]
    exact continuous_finsetSum _ fun τ _ => (hL τ).1.comp (continuous_apply τ)
  have hΛf : ∀ s, (Λ s).map (finPart D) = 0 := fun s => by
    ext i j
    rw [hΛ]
    show finPart D ((∑ τ, lineAt θ τ (compAt θ τ w) (s τ) : WO S T) i j) = 0

    rw [Matrix.sum_apply, map_sum (finPart D)]
    exact Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 (s τ)) i) j
  let G : (D.what₂.Tau → ℝ) → ℂ := fun s => heisO ψ S T (Λ s) f x
  have hχ : ∀ τ, Differentiable ℝ fun t : ℝ => ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) t)) := fun τ => by
    refine GlobalTheory.FockTranslate.differentiable_of_char _
      (hc.comp (continuous_const.mul (continuous_symplO S T continuous_const (hL τ).1))) ?_ ?_
    · rw [map_zero, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
    · intro s t
      rw [map_add (f := _), symplOH_add_right, AddChar.map_add_eq_mul]
  have hpsi : ∀ s, ψ (symplOH S T x (Λ s)) = ∏ τ, ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ))) := by
    intro s
    rw [hΛ]
    let φ : WO S T →+ AF D.host.F :=
      ⟨⟨symplOH S T x, by rw [symplOH, symplO_zero_right, mul_zero]⟩, symplOH_add_right S T x⟩
    have key : ∀ (s' : Finset D.what₂.Tau) (g : D.what₂.Tau → WO S T),
        ψ (φ (∑ τ ∈ s', g τ)) = ∏ τ ∈ s', ψ (φ (g τ)) := by
      intro s' g
      induction s' using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.prod_empty, map_zero, AddChar.map_zero_eq_one]
      | insert a s' ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, map_add (f := _), AddChar.map_add_eq_mul, ih]
    exact key Finset.univ _
  have hGd : Differentiable ℝ G := by
    have h1 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => ψ (symplOH S T x (Λ s)) := by
      simp only [hpsi]
      have hp : ∀ s' : Finset D.what₂.Tau, Differentiable ℝ fun s : D.what₂.Tau → ℝ =>
          ∏ τ ∈ s', ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ))) := by
        intro s'
        induction s' using Finset.induction_on with
        | empty => simp only [Finset.prod_empty]; exact differentiable_const _
        | insert a s' ha ih =>
          simp only [Finset.prod_insert ha]
          have hτ : Differentiable ℝ fun s : D.what₂.Tau → ℝ => s a := differentiable_apply a
          exact ((hχ a).comp hτ).mul ih
      exact hp Finset.univ
    have h2 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => f (x + Λ s) := by
      let e := Fintype.equivFin D.what₂.Tau
      let ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) ≃L[ℝ] (D.what₂.Tau → ℝ) :=
        (LinearEquiv.funCongrLeft ℝ ℝ e).toContinuousLinearEquiv
      have hs := hf.smooth _ (Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ)))
        (hΛc.comp ℓ.continuous) (fun t => hΛf _) x
      have : (fun s : D.what₂.Tau → ℝ => f (x + Λ s)) =
          (fun t => f (x + Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ)) t)) ∘ ℓ.symm := by
        funext s
        simp
      rw [this]
      exact (hs.differentiable (by simp)).comp ℓ.symm.differentiable
    exact h1.mul h2
  have hfun : (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x) =
      G ∘ (fun t : ℝ => fun _ : D.what₂.Tau => t) := by
    funext t
    simp only [Function.comp, G, hΛ]
    rw [realAd_smul_eq hθ hw t]
  have hdiag : HasDerivAt (fun t : ℝ => (fun _ : D.what₂.Tau => t)) (fun _ => (1 : ℝ)) 0 :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id 0
  have hG0 : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => fun _ : D.what₂.Tau => t) 0) := (hGd 0).hasFDerivAt
  have hcomp := hG0.comp_hasDerivAt (0 : ℝ) hdiag
  rw [hfun]
  suffices key : fderiv ℝ G 0 (fun _ => 1) = ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x by
    rw [← key]; exact hcomp

  rw [show (fun _ : D.what₂.Tau => (1 : ℝ)) = ∑ τ, Pi.single τ (1 : ℝ) from (Finset.univ_sum_single _).symm, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hline : HasDerivAt (fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ))
      ((1 : ℝ) • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0 := (hasDerivAt_id 0).smul_const _
  have hG0' : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0) := by
    simpa using (hGd 0).hasFDerivAt
  have h3 := hG0'.comp_hasDerivAt (0 : ℝ) hline
  rw [one_smul] at h3
  have e : (G ∘ fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) =
      fun t => heisO ψ S T (lineAt θ τ (compAt θ τ w) t) f x := by
    funext t
    simp only [Function.comp, G, hΛ]
    rw [Finset.sum_eq_single τ (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
    simp
  rw [e] at h3
  exact h3.deriv.symm

end GlobalTheory.ArchLineSum
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PeriodBound

theorem period_bound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) → (∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ) ∧ ∃ K : ℝ, ∀ w : M.Vec, ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖ ≤ K * ∏ τ, ‖(w τ : M.H τ)‖ := by
  intro hP hV D θ hθ V S M J χ t ht v F hF hFb
  obtain ⟨C0, hC0⟩ := hFb
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfin : v.μ v.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top hV V v.μ v.𝓕 v.haar v.fund
  have hval : ∀ x : SmT M, Continuous (t x) ∧ ∃ B : ℝ, ∀ g, ‖t x g‖ ≤ B := by
    intro x
    obtain ⟨ha, hc, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J χ t ht x
    exact ⟨ha.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ ha hc⟩
  have hint0 : ∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ := by
    intro x
    obtain ⟨hcont, B, hB⟩ := hval x
    refine Measure.integrableOn_of_bounded (M := C0 * B) hfin.ne
      ((hF.2.mul hcont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
    rw [norm_mul]
    exact mul_le_mul (hC0 g) (hB g) (norm_nonneg _) ((norm_nonneg _).trans (hC0 g))
  refine ⟨hint0, ?_⟩
  set T : MMap M := PiTensorProduct.lift.symm t with hTdef
  have hT : T ∈ Mult θ M J χ := (mem_multT θ M J χ t).1 ht
  obtain ⟨c, hc⟩ := GlobalTheory.SchurConst.schurMult_all hP D θ hθ V S M J χ v.μ v.𝓕 v.haar v.fund hθ v.haar v.fund T hT T hT
  have hTw : ∀ w : M.Vec, T w = t (PiTensorProduct.tprod ℂ w) := fun w => by
    rw [hTdef, PiTensorProduct.lift_symm]
    rfl
  set C' : ℝ := max C0 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hFC : ∀ g, ‖F g‖ ≤ C' := fun g => (hC0 g).trans (le_max_left _ _)
  refine ⟨C' * ((v.μ v.𝓕).toReal + ‖c‖) / 2, fun w => ?_⟩
  set s : ℝ := ∏ τ, ‖(w τ : M.H τ)‖ with hs
  have hs0 : 0 ≤ s := Finset.prod_nonneg fun τ _ => norm_nonneg _
  rcases hs0.eq_or_lt with h0 | hpos
  · obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 h0.symm
    have hwτ : w τ = 0 := Subtype.ext (norm_eq_zero.1 hτ)
    have h1 : PiTensorProduct.tprod ℂ w = 0 := (PiTensorProduct.tprod ℂ).map_coord_zero τ hwτ
    rw [h1, map_zero, ← h0]
    simp
  · obtain ⟨hint, heq⟩ := hc w w
    have hnsq : ∀ g, ‖star (T w g) * T w g‖ = ‖T w g‖ ^ 2 := fun g => by
      rw [norm_mul, norm_star, sq]
    have hint2 : IntegrableOn (fun g => ‖T w g‖ ^ 2) v.𝓕 v.μ := by
      have h := funext fun g => (hnsq g).symm
      rw [h]
      exact hint.norm
    have hsq : ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ ≤ ‖c‖ * s ^ 2 := by
      have h1 : ((∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ : ℝ) : ℂ) = ∫ g in v.𝓕, star (T w g) * T w g ∂v.μ := by
        rw [← integral_complex_ofReal]
        congr 1
        funext g
        rw [Complex.star_def, Complex.conj_mul']
        push_cast
        ring
      have hnn : 0 ≤ ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ := integral_nonneg fun g => sq_nonneg _
      have h2 : ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ = ‖∫ g in v.𝓕, star (T w g) * T w g ∂v.μ‖ := by
        rw [← h1, Complex.norm_of_nonneg hnn]
      rw [h2, heq, norm_mul, norm_prod, hs, ← Finset.prod_pow]
      refine le_of_eq ?_
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [inner_self_eq_norm_sq_to_K]
      simp
    have hpt : ∀ g, ‖F g * t (PiTensorProduct.tprod ℂ w) g‖ ≤ C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2 := by
      intro g
      rw [norm_mul, ← hTw]
      have h3 : ‖T w g‖ ≤ s / 2 + ‖T w g‖ ^ 2 / (2 * s) := by
        rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (‖T w g‖ - s)]
      calc ‖F g‖ * ‖T w g‖ ≤ C' * ‖T w g‖ := mul_le_mul_of_nonneg_right (hFC g) (norm_nonneg _)
        _ ≤ C' * (s / 2 + ‖T w g‖ ^ 2 / (2 * s)) := mul_le_mul_of_nonneg_left h3 hC'0
        _ = C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2 := by ring
    have hintR : IntegrableOn (fun g => C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2) v.𝓕 v.μ :=
      (integrableOn_const hfin.ne).add (hint2.const_mul _)
    calc ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖
        ≤ ∫ g in v.𝓕, ‖F g * t (PiTensorProduct.tprod ℂ w) g‖ ∂v.μ := norm_integral_le_integral_norm _
      _ ≤ ∫ g in v.𝓕, (C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2) ∂v.μ :=
          integral_mono (hint0 _).norm hintR hpt
      _ = (v.μ v.𝓕).toReal * (C' * s / 2) + C' / (2 * s) * ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ := by
          have hc1 : Integrable (fun _ : GA D V => C' * s / 2) (v.μ.restrict v.𝓕) := integrableOn_const hfin.ne
          have hc2 : Integrable (fun g => C' / (2 * s) * ‖T w g‖ ^ 2) (v.μ.restrict v.𝓕) := hint2.const_mul _
          rw [integral_add hc1 hc2, setIntegral_const,
            integral_const_mul, smul_eq_mul, Measure.real]
      _ ≤ (v.μ v.𝓕).toReal * (C' * s / 2) + C' / (2 * s) * (‖c‖ * s ^ 2) := by
          gcongr
      _ = C' * ((v.μ v.𝓕).toReal + ‖c‖) / 2 * s := by
          field_simp

end GlobalTheory.PeriodBound
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim.JetsAssembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem defTot_eq_sum {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    (M : Vol G) (σ : PolCol G × PolRow G →₀ ℂ) (τ : PureDat G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    defTot t S M σ τ φ F = σ.sum fun P c => c * defTot t S M (Finsupp.single P 1) τ φ F := by
  unfold defTot
  refine Finsupp.sum_congr fun P _ => ?_
  rw [Finsupp.sum_single_index (by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun d _ => ?_
  ring

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetsOne (ch : Choice R) : Prop :=
  ∀ P : PolCol ch.G × PolRow ch.G, ∃ κ : ℂ, ∀ t a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M τ,
    IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y,
      defTot t ch.S.toGridChoice M (Finsupp.single P 1) τ (colFn ch a) (formTop ch t y) =
        κ * ch.S.classSum (ch.Phi a) β τ (psiC (ch.Psi a)) (ch.S.formC t y)

theorem jetsAt_of_one (ch : Choice R) (hL : R.toLevCh.Is A.μ0) (h : JetsOne ch) : JetsAt ch := by
  refine ⟨fun t Φ β => StepsModel.exists_isTermVol ch.S.toGridChoice hL t Φ β, fun σ => ?_⟩
  choose κ hκ using h
  refine ⟨σ.sum fun P c => c * κ P, fun t a β hβ M τ hM hτ y => ?_⟩
  rw [defTot_eq_sum, Finsupp.sum_mul]
  refine Finsupp.sum_congr fun P _ => ?_
  rw [hκ P t a β hβ M τ hM hτ y, mul_assoc]

end GlobalTheory.RowClaim.JetsAssembly

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.exists_int_eq_exponent_add_half_index : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau) (a : ℚ), IsHeckeChar D χ → ResEta D χ n → HasInfExp D χ τ a → ∃ e : ℤ, (e : ℚ) = a + (n : ℚ) / 2 := by
  first | exact @GlobalTheory.SplitParity.exists_int_add_half | exact GlobalTheory.SplitParity.exists_int_add_half | (intros; apply GlobalTheory.SplitParity.exists_int_add_half <;> assumption)
end
