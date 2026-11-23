module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle477
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle541
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiEqSumCoupIdx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle471
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle469
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle543
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle544
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle545
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle550
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) Ψ₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.SeeSaw.GValMid.gValue_mid | exact GlobalTheory.SeeSaw.GValMid.gValue_mid | (intros; apply GlobalTheory.SeeSaw.GValMid.gValue_mid <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j (h : j + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 →
    (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j 0 h) (c.J j 0 h)) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) Ψ₂ →
    c.lst j h (v.τ j h) s₁ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eGT j h) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.lst j h (v.τ j h) s₁ Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.LevelLast.last_value | exact GlobalTheory.LevelLast.last_value | (intros; apply GlobalTheory.LevelLast.last_value <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LastPt



theorem kernel_eq_sum : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ α (S : Finset ((Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂)), Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S → ∀ (d₁ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) (d₁ yb) (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb)) → (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM (d₂ yb) (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb)) → c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂) = ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
  intro D c v χ Q hc hv h hr hτ s₁ hχ X₁ X₂ h₁ h₂ α S hS d₁ d₂ hd₁ hd₂
  classical
  have hs := Q.hs
  have hsc : Q.sc Q.s ≠ 0 := Q.sc_ne Q.s
  obtain ⟨T₁, hT₁, hX₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Q.k Q.q Q.unit _ _ _ _ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 rfl) c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd Q.s (by omega)) (hv.sd (Q.s + 1) (by omega)) (Q.latY _ _ _) (Q.latY _ _ _)).2 X₁ h₁
  obtain ⟨T₂, hT₂, hX₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Q.k Q.q Q.unit _ _ _ _ (Q.FY (Q.s + 1) 0 rfl) Q.FT c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd (Q.s + 1) (by omega)) hv.sdT (Q.latY _ _ _) Q.latT).2 X₂ h₂
  obtain ⟨F₀, hF₀⟩ := ((GlobalTheory.LocMod.normalFrames_exist D Q.k (ofSplit Q.q) _ 0 (Q.sc Q.s) hsc).1 (c.B Q.s 0 h)
    (Q.FX Q.s (by omega))).1
  have hjac := Q.jac Q.s 0 h 0 (by omega)
  obtain ⟨U₁, hU₁, hfl⟩ := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D) Q.k (ofSplit Q.q) Q.ν Q.unitVol.1
    c.ψ Q.ψk Q.char 0 (c.B Q.s 0 h) (c.J Q.s 0 h) s₁ (Q.sc Q.s) hsc _ _ 0 (Q.FX Q.s (by omega)) F₀
    (Q.FY Q.s (0 + 1) (by omega)) (Q.FX (Q.s + 1) le_rfl) (Q.FY (Q.s + 1) 0 rfl) hF₀ (Q.bes Q.s 0 h (0 + 1) (by omega)) hjac T₁ hT₁
  obtain ⟨U₂, hU₂, hres, hext⟩ := GlobalTheory.LevelLast.splitLocalPlace_isModel_wittExtendByZero_rankZero (ofSplit Q.q) c.ψ (c.jac Q.s 0 h).d (Q.FX (Q.s + 1) le_rfl)
    (Q.FY (Q.s + 1) 0 rfl) Q.FT hjac.2.1 T₂ hT₂
  let Φ₁ : SB _ := ⟨_, Q.reg.1 Q.s 0 rfl⟩
  let Φα : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) :=
    ⟨om (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (Q.T.Phi Q.s 0 rfl), om_mem_SB _ _ _ (Q.reg.1 Q.s 0 rfl)⟩
  let Φ₂ : SB _ := ⟨_, Q.reg.2.1⟩
  let O₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1))⟩
  let O₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1) ⊕ Fin 0)⟩
  let O₁' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s ⊕ Unit)⟩
  let O₂' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1))⟩
  let Ψα : SB _ := ⟨_, ((GlobalTheory.LocFlat.flat_SB_onto Q.k Q.ψk Q.ν Q.cond.continuous Q.unitVol.1 _ _ 0 (0 + 1) le_rfl).1
    le_rfl).1 _ Φα.2⟩
  obtain ⟨Y₂, hY₂⟩ := hres Φ₂
  have a₁ : comb c.ψ _ _ (Q.eL Q.s) X₁ = T₁ Φ₁ := by
    rw [← hX₁ O₁ rfl]
    exact ((Q.eL_at Q.s 0 rfl).2 T₁ hT₁ O₁ Φ₁ rfl rfl).symm
  have a₂ : comb c.ψ _ _ Q.eLT X₂ = T₂ Φ₂ := by
    rw [← hX₂ O₂ rfl]
    exact (Q.eLT_at.2 T₂ hT₂ O₂ Φ₂ rfl rfl).symm
  have a₃ := GlobalTheory.T.exchangeCombination_moves_lastStepDatum_to_chart D c v χ Q hc h s₁ hχ α T₁ hT₁ Φ₁ Φα rfl rfl
  have b₁ : flatBF s₁ (T₁ Φα) = U₁ Ψα := hfl Φα Ψα rfl
  have b₁' : flatBF s₁ (T₁ O₁) = U₁ O₁' := hfl O₁ O₁' (by
    have := (GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol (Q.X (Q.s + 1)) (Q.X Q.s) Unit 0 (0 + 1)).1
    rw [if_neg (by omega)] at this
    exact this.symm)
  have b₂ := hext Φ₂ Y₂ hY₂
  have b₂' := hext O₂ O₂' fun x => by
    have hx : (∀ r q, x r q ∈ 𝒪[Q.k]) ↔
        ∀ r (q : Q.X (Q.s + 1) ⊕ Fin 0), (fromCols x 0) r q ∈ 𝒪[Q.k] := by
      refine ⟨fun hx r q => ?_, fun hx r q => hx r (Sum.inl q)⟩
      rcases q with q | q
      · exact hx r q
      · exact q.elim0
    simp only [O₂, O₂', Set.indicator_apply, Set.mem_setOf_eq, hx]
  rw [a₁, a₂, a₃, ← hX₁ O₁ rfl, ← hX₂ O₂ rfl]
  unfold Comm.lst
  rw [b₁, b₁', b₂, b₂']
  obtain ⟨Λ, hΛ, hK⟩ := GlobalTheory.T.splitPlace_doubleStep_kernel_localModels D Q.k (ofSplit Q.q) Q.ν Q.unitVol.1 c.ψ hc.std Q.ψk Q.char 0 (c.B Q.s 0 h) (c.X (Q.s + 1))
    (c.X (Q.s + 1 + 1)) c.T c.Lz (c.oT (Q.s + 1 + 1) h) (v.τ Q.s h) hr hτ (Q.sc Q.s) Q.z₀ hsc (Q.tau h) _ _ _
    (Q.FX Q.s (by omega)) F₀ (Q.FX (Q.s + 1) le_rfl) Q.FT Q.FM hF₀ Q.last U₁ U₂ hU₁ hU₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Ψα Y₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁' O₂'
  have hv1 : valuation Q.k (-1 : Q.k) = 1 := by simp
  haveI := Q.unitVol.1
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.X (Q.s + 1)) (n' := Q.X Q.s)
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.Z ⊕ Unit) (n' := Q.X (Q.s + 1))
  let P₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s)⟩
  let P₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.Z ⊕ Unit) (Q.X (Q.s + 1))⟩
  let E₁ := fun yb => (⟨_, (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).1⟩ : SB _)
  let E₂ := fun yb => (⟨_, (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).2⟩ : SB _)
  let E := fun yb => (⟨fun q => (E₁ yb).1 q.1 * (E₂ yb).1 q.2, GlobalTheory.FinPl.Comm.prod_mem_SB (E₁ yb).2 (E₂ yb).2 (s := id)
    continuous_fst continuous_snd continuous_id fun _ => rfl⟩ :
      SB (Matrix (Q.X (Q.s + 1)) (Q.X Q.s) Q.k × Matrix (Q.Z ⊕ Unit) (Q.X (Q.s + 1)) Q.k))
  have hsum : Ξ = ∑ yb ∈ S, E yb := Subtype.ext (funext fun q => by
    have e : (fun y => Ψα.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = Q.T.Psi (Q.rep Q.s 0 rfl α) q.1 :=
      funext fun y => GlobalTheory.LevelLast.flCol_one _ _ _ _
    rw [hΞ q, hY₂, e, (GlobalTheory.Couple.psi_eq_sum_coupIdx Q.k Q.s Q.X Q.Z Q.T Q.A Q.c₁ Q.c₂ Q.adapt Q.ψk Q.cond.continuous Q.ν (-1) S hS
      _ ((Q.rep_bij Q.s 0 rfl).mapsTo (Set.mem_univ α)) q.1).2, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun yb _ => mul_left_comm _ _ _)
  have hone : ∀ q, Ξ'.1 q = P₁.1 q.1 * P₂.1 q.2 := fun q => by
    have e : (fun y => O₁'.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        P₁.1 q.1 * cosetInd (box _ (1 : Q.kˣ)) (Submodule.Quotient.mk 0) y :=
      funext fun y => GlobalTheory.LastTwoSteps.intInd_fromCols q.1 y
    rw [hΞ' q, e, GlobalTheory.LastTwoSteps.hat_const_mul, GlobalTheory.LastTwoSteps.hat_int Q.cond Q.unitVol hv1]
    simp only [P₂, O₂']
    rw [GlobalTheory.LastTwoSteps.intInd_rows q.2]
    ring
  refine Eq.trans (funext hΞK) ?_
  show Λ Ξ = _

  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun yb _ => ?_
  refine ((GlobalTheory.T.heisenbergCombination_twoVariableModel_and_lineExtension D Q.k (ofSplit Q.q) c.ψ _ _ _).1 _ _ _ _ _ _ Λ (d₁ yb) (d₂ yb) (E₁ yb) P₁ (E₂ yb) P₂ (E yb) Ξ' hΛ
    (hd₁ yb) (hd₂ yb) rfl rfl (fun _ => rfl) hone).trans ?_
  exact congrArg _ (funext hΞ'K).symm

end GlobalTheory.QPl.LastPt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelPart_laws_of_columnPins : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Is := by
  first | exact @GlobalTheory.KerLaws.clsKL_is | exact GlobalTheory.KerLaws.clsKL_is | (intros; apply GlobalTheory.KerLaws.clsKL_is <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.unitary_theta_innerProduct_formula_convergent_range : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : GlobalTheory.Core.Rk.IP.WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧ Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m ∧ petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
  first | exact @GlobalTheory.Core.Rk.IP.innerProduct_convergent | exact GlobalTheory.Core.Rk.IP.innerProduct_convergent | (intros; apply GlobalTheory.Core.Rk.IP.innerProduct_convergent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlaceDoubleStepFinitelyManyCellsUniform_proof : ∀ D : D7, FinOne D := by
  first | exact @GlobalTheory.QPl.FinOneProof.finOne | exact GlobalTheory.QPl.FinOneProof.finOne | (intros; apply GlobalTheory.QPl.FinOneProof.finOne <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_doubleStep_trilinearForm_properties : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ T₁ T₂, (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ φ, IsContAut S.B.A φ → ∃ (A : Submodule ℂ (GA D S.B'.V → ℂ)) (τ : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) A) (T : SB (Matrix Q.n₁ Q.n₀ Q.k) →ₗ[ℂ] SB (Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), IsSmoothRep τ ∧ (∀ y (f : A), (τ y f).1 = rTrans (Q.gl₂ y) f.1) ∧ (∀ f, IsContAut S.B'.V f → Q.Typed f → f ∈ A) ∧ TriPos Q.ψk Q.μ₁ Q.μ₂ (σ + 1) τ T ∧ (∀ Φ₁ Φ₂ (f : A), HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1)) ∧ ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f : A, T Ξ₁ Ξ₂ f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f.1 1 1 1 := by
  first | exact @GlobalTheory.TriStep.tri | exact GlobalTheory.TriStep.tri | (intros; apply GlobalTheory.TriStep.tri <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.Unf

theorem _root_.GlobalTheory.T.flatMap_handedFunction_vanishing_period_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (f : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W f → ∀ r ∈ jacGrp J.d, r ∈ grpAt J.W P → (flatBF s (s.om (1, r) f) = 0 ↔ flatBF s f = 0)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (f : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V f → ∀ r ∈ besGrp B.d B.o, r ∈ grpAt B.V P → (handFB s vL Y (flatFB s (s.om (1, r) f)) = 0 ↔ handFB s vL Y (flatFB s f) = 0) := by
  first | exact @GlobalTheory.FlatRInv.vanish_invariant | exact GlobalTheory.FlatRInv.vanish_invariant | (intros; apply GlobalTheory.FlatRInv.vanish_invariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacMove
variable {D : D7}

theorem mt_mul₀ (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one₀ (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv] at e
  exact e.symm

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : Lat S} {P : Pl D → Prop} (h : Moves S g L M P)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : mt S g *ᵥ z ∈ latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact GlobalTheory.FinPl.MovedVac.smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_eq (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h u = HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹) := rfl

theorem actO_mem_latO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [actO_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem mem_latO_iff_actO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) (u : WO S T) :
    u ∈ latO S T (Λ : Set _) (Λ' : Set _) P ↔ actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  refine ⟨actO_mem_latO hΛ hM hΛ' hM' hg hh, fun hu => ?_⟩
  have := actO_mem_latO hM hΛ hM' hΛ' (moves_inv hg) (moves_inv hh) hu
  rwa [GlobalTheory.SplitHecke.actO_inv_actO] at this

end GlobalTheory.VacMove

namespace GlobalTheory.VacMove

theorem isThetaAt_moveLat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Λ M : Lat S) (Λ' M' : Lat T), IsSelfDualC S Λ → IsSelfDualC S M → IsSelfDualC T Λ' → IsSelfDualC T M' → ∀ b ∈ GfC S, ∀ b' ∈ GfC T, Moves S b Λ M (fun _ => True) → Moves T b' Λ' M' (fun _ => True) → ∀ e Φ f₀ f, e * e = e → infPart D e = 0 → IsThetaFunO ψ S T f₀ → IsThetaFunO ψ S T f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀) (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) (om (b, b') f) := by
  intro D ψ S T χS χT om hW Λ M Λ' M' hΛ hM hΛ' hM' b _ b' _ hb hb' e Φ f₀ f hee hinf hf₀ _ hf
  have key := mem_latO_iff_actO hΛ hM hΛ' hM' hb hb'
  have key' := mem_latO_iff_actO hM hΛ hM' hΛ' (moves_inv hb) (moves_inv hb')
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T Λ Λ' hΛ hΛ' e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨⟨_, GlobalTheory.SplitMove.isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T M M' hM hM' e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW key' hT' th1
  have ev : om (b⁻¹, b'⁻¹) (om (b, b') f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (b⁻¹, b'⁻¹) (T' fun t => Φ (actO S T b⁻¹ b'⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

end GlobalTheory.VacMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.secondFlatMap_unipotent_stabilizer_translate_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LW : Lat B.V) (v : Pl D), IsSelfDualC J.W LV → IsSelfDualC B.V LW → Tame D v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ (x : GA D B.V) (κ : GA D B.V), InK B.V LW (· = v) κ → flatFB s (s.om (1, n * x * κ) f) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s (s.om (1, x) f) := by
  first | exact @GlobalTheory.FinPl.flatFB_om_shift | exact GlobalTheory.FinPl.flatFB_om_shift | (intros; apply GlobalTheory.FinPl.flatFB_om_shift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.secondFlatMap_vacuum_translate_isVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (P : Pl D → Prop), (∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v ∧ UnrAt s v) → ∀ f, Vac ψ J.W B.V LV LW P f → ∀ h₁ ∈ grpOff J.W P, ∀ h₂ ∈ grpOff B.V P, Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s (s.om (h₁, h₂) f)) := by
  first | exact @GlobalTheory.VacSecondPf.vac_second | exact GlobalTheory.VacSecondPf.vac_second | (intros; apply GlobalTheory.VacSecondPf.vac_second <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.secondFlatMap_moved_core_lattice_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ γ ∈ grpAt B.V₀ (· = v), ∃ M : Lat B.V₀, IsSelfDualC B.V₀ M ∧ Moves B.V₀ γ LW₀ M (· = v) ∧ Vac ψ J.W₀ B.V₀ LV₀ M (· = v) (flatFB s (s.om (1, B.d.emb0 γ) f)) := by
  first | exact @GlobalTheory.FinPl.movedVac | exact GlobalTheory.FinPl.movedVac | (intros; apply GlobalTheory.FinPl.movedVac <;> assumption)
end
