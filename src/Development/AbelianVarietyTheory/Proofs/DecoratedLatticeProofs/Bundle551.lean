module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle010
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle518
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle465
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyFiniteOfTupleConditions
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle471
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle548
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle522
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurAtRecordGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle451
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle453
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle530
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle422
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle345
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle340
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle549
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle505
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLevelPrimeLawDoubleStep
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF

@[expose] public section

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpRecordGap

theorem isHCParam_u (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (fun i => ((P.u i : ℚ) : ℝ)) := by
  have hk := R.m_add_three_le_k
  obtain ⟨c, hc⟩ := R.k_even
  have step : ∀ (i : ℕ) (h : i + 1 < R.k), P.u ⟨i + 1, h⟩ < P.u ⟨i, by omega⟩ := fun i h =>
    lt_trans (P.v_gt_u ⟨i, by omega⟩) (P.u_gt_v ⟨i, by omega⟩)
  refine ⟨?_, fun a => ?_⟩
  · have key : ∀ (d i : ℕ) (h : i + d + 1 < R.k), P.u ⟨i + d + 1, h⟩ < P.u ⟨i, by omega⟩ := by
      intro d
      induction d with
      | zero => intro i h; exact step i h
      | succ d ih => intro i h; exact lt_trans (step (i + d + 1) h) (ih i (by omega))
    intro i j hij
    have hlt : i.val < j.val := hij
    have := key (j.val - i.val - 1) i.val (by omega)
    have e : P.u ⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ = P.u j := congrArg P.u (Fin.ext (by simp; omega))
    rw [e] at this
    beta_reduce
    exact_mod_cast this
  · obtain ⟨z, hz⟩ := P.u_half a
    refine ⟨z - c + 1, ?_⟩
    simp only
    rw [hz, hc]; push_cast; ring

theorem isHCParam_uS (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (uS D w τ) :=
  isHCParam_u D.R (D.hcW w τ)

theorem weyl_at (D : D7) : VanishingOnXAndXPlusBranching.adm12 D := by
  intro τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D w τ)).1 H _ hg

theorem ampOn_singleton : ∀ c : ℝ, AmpOn {c} := by
  intro c Cg cb Cu cT CT hcb _
  obtain ⟨CPT, hPT⟩ := GlobalTheory.T.ampleTheta_wideRange_large_constants Cg cb Cu cT CT c
  obtain ⟨CDl, hDl⟩ := GlobalTheory.CoreDlGap.ptDl_at_record Cg cb Cu cT CT c
  obtain ⟨Ca, hCa, hAbs⟩ := GlobalTheory.AbsRecGap.abs_all_at_record_gap Cg cb Cu cT CT c
  obtain ⟨CS, tS, hS⟩ := GlobalTheory.Amp.schur_at_record_gap Cg cb Cu cT CT c
  obtain ⟨tL, hL⟩ := GlobalTheory.T.exists_threshold_criticalLevel_lower_bound cb Cu hcb
  obtain ⟨tV, hV⟩ := GlobalTheory.T.normalizedFormalDegree_eq_vandermonde_of_sizes
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := GlobalTheory.T.ampAt_of_admitted_bounds Cg CPT CDl 1 Ca CS zero_le_one hCa
  refine ⟨C, C2, Ch, hC, hCh, fun Cpr δ hδ => ?_⟩
  obtain ⟨t0, H0⟩ := H Cpr δ hδ
  obtain ⟨t1, h1⟩ := hPT (max Cpr 0)
  obtain ⟨t2, h2⟩ := hDl (max Cpr 0)
  obtain ⟨t3, h3⟩ := GlobalTheory.T.realPlaceAmplitude_norm_le_const_div_formalDegree Cg cb Cu cT CT c (max Cpr 0)
  obtain ⟨t4, h4⟩ := hAbs (max Cpr 0)
  obtain ⟨t5, h5⟩ := GlobalTheory.T.formalDegree_ratio_eq_vandermonde_ratio_along_line (max Cpr 0)
  refine ⟨max t0 (max t1 (max t2 (max t3 (max t4 (max tS (max tL (max tV t5))))))),
    fun C0 hC0 C' Cl hC' hCl D large₂ hG hT _ hTF => ?_⟩
  obtain rfl : C0 = c := hC0
  simp only [max_le_iff] at hC' hCl
  obtain ⟨a0, a1, a2, a3, a4, aS, -, aV, a5⟩ := hC'
  obtain ⟨b0, b1, b2, b3, b4, bS, bL, bV, b5⟩ := hCl
  have hLow : VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 := fun h0 =>
    hL D large₂ C' Cl Cg cT CT C0 bL
      (hV D large₂ C' Cl Cg cb Cu cT CT aV bV hT h0.1 (GlobalTheory.T.dataNW_of_standingNumericalData D C0 h0.2.2 h0.2.1)) h0
  exact H0 D large₂ C' Cl cb Cu cT CT C0 a0 b0 hG
    (h1 D large₂ C' Cl a1 b1 hT hTF)
    (h2 D large₂ C' Cl a2 b2 hT)
    hLow
    (h3 D large₂ C' Cl a3 b3 hT)
    (Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
      (h5 D large₂ C' Cl Cg cb Cu cT CT C0 1 a5 b5 hT))
    (h4 D large₂ C' Cl a4 b4)
    (hS D large₂ C' Cl aS bS hT)
    (weyl_at D)

end GlobalTheory.AmpRecordGap
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_unfoldedValue_commonConstants_fixedLevel : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → GValue (t := t) (v.withCG a) := by
  first | exact @GlobalTheory.SeeSaw.GValAll.gValue_common | exact GlobalTheory.SeeSaw.GValAll.gValue_common | (intros; apply GlobalTheory.SeeSaw.GValAll.gValue_common <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_twistPlace_finitely_many_cells : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ ((F.Q i).eL j) f₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  first | exact @GlobalTheory.QFinOneAt.finOne_pin | exact GlobalTheory.QFinOneAt.finOne_pin | (intros; apply GlobalTheory.QFinOneAt.finOne_pin <;> assumption)
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

namespace GlobalTheory.QLastOne



theorem lastOne : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂))) = ∑ y, (Nat.card {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} : ℂ) • c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by

  intro D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u
  classical
  obtain ⟨hfin, -, hsymm, htrans, hstab⟩ := GlobalTheory.T.twistPlace_couplingIndex_finite_level_stable D c v χ Q

  have hcomb : ∀ {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
      (FS : GlobalTheory.LocMod.Frame Q.k S.rank Y') (FT : GlobalTheory.LocMod.Frame Q.k T.rank Y) (Ξ : Matrix Y Y' Q.k → ℂ),
      Ξ ∈ SB _ → ∃ d, (ofSplit Q.q).IsCombAt c.ψ FS FT d Ξ := by
    intro S T Y Y' _ _ _ _ FS FT Ξ hΞ
    let O : SB (Matrix Y Y' Q.k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Y Y'⟩
    have hO : O ≠ 0 := by
      intro h0
      have := congrFun (congrArg Subtype.val h0) 0
      simp [O, Set.indicator_apply] at this
    obtain ⟨d, hd, hT⟩ := GlobalTheory.T.exists_heisenberg_combination_split_place_datum D Q.k (ofSplit Q.q) Y Y' S T FS FT c.ψ hc.std O ⟨Ξ, hΞ⟩ hO
    refine ⟨d, hd, fun Tm hTm Φ₀ Φ h0 h1 => ?_⟩
    have e0 : Φ₀ = O := Subtype.ext h0
    have e1 : Φ = ⟨Ξ, hΞ⟩ := Subtype.ext h1
    rw [e0, e1]
    exact hT Tm hTm
  choose d₁ hd₁ using fun yb => hcomb (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).1
  choose d₂ hd₂ using fun yb => hcomb (Q.FX (Q.s + 1) le_rfl) Q.FM _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).2
  set S := hfin.toFinset with hS
  have hSc : Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S := by simp [S]
  have hmemS : ∀ yb, yb ∈ S ↔ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := fun yb => by simp [S]
  set C := c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂ with hC
  have hpt := GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α S hSc d₁ d₂ hd₁ hd₂
  have hlin := GlobalTheory.T.seeSawLastTwoSteps_doubleLift_additive D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1 φ hφ
  rw [hpt, hlin _ S d₁ d₂ (fun i => (hd₁ i).1) (fun i => (hd₂ i).1)]

  set B : Q.Ch (Q.s + 1) → GA D (c.X (Q.s + 1 + 1)) → ℂ := fun y =>
    c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) with hB

  have hterm : ∀ yb ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ yb]) (aconv [c₂, d₂ yb]) C) =
      ∑ y, if SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb then B y else 0 := by
    intro yb hyb
    obtain ⟨y₀, hy₀⟩ := Q.cos_cov yb ((hmemS yb).1 hyb)
    rw [Finset.sum_eq_single y₀]
    · rw [if_pos hy₀]
      exact GlobalTheory.T.doubleThetaLift_lastSteps_couplingCoset_orbit_invariant D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u y₀ yb hy₀
        (d₁ yb) (d₂ yb) (hd₁ yb) (hd₂ yb)
    · intro y _ hy
      rw [if_neg]
      intro h'
      exact hy (Q.cos_inj y y₀ (htrans _ _ _ h' (hsymm _ _ hy₀)))
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  by_cases hy : Q.cos y ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)
  · have hset : {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} =
        ↑(S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb) := by
      ext yb
      simp only [Set.mem_setOf_eq, Finset.coe_filter]
      exact ⟨fun h' => ⟨(hmemS yb).2 (hstab _ hy yb h'), h'⟩, fun h' => h'.2⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.cast_smul_eq_nsmul]
  · have hempty : (S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro yb hyb h'
      exact hy (hstab yb ((hmemS yb).1 hyb) _ (hsymm _ _ h'))
    have hnot : Q.cos y ∉ S := fun h' => hy ((hmemS _).1 h')

    have hz : biComb c.ψ _ _ _ (Q.dL Q.s α y) (Q.dL (Q.s + 1) y u) C = 0 := by
      have h2 := GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α (insert (Q.cos y) S)
        (hSc.trans (by simp)) (Function.update d₁ (Q.cos y) (Q.dL Q.s α y))
        (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u))
        (fun yb => by
          by_cases e : yb = Q.cos y
          · subst e; rw [Function.update_self]; exact Q.dL_pen α y
          · rw [Function.update_of_ne e]; exact hd₁ yb)
        (fun yb => by
          by_cases e : yb = Q.cos y
          · subst e; rw [Function.update_self]; exact Q.dL_top y u
          · rw [Function.update_of_ne e]; exact hd₂ yb)
      rw [hpt, Finset.sum_insert hnot, Function.update_self, Function.update_self] at h2
      have h3 : ∑ yb ∈ S, biComb c.ψ _ _ _ (Function.update d₁ (Q.cos y) (Q.dL Q.s α y) yb)
          (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u) yb) C =
          ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C := by
        refine Finset.sum_congr rfl fun yb hyb => ?_
        have e : yb ≠ Q.cos y := fun e => hnot (e ▸ hyb)
        rw [Function.update_of_ne e, Function.update_of_ne e]
      rw [h3] at h2
      rw [← hC] at h2
      have h4 := congrArg (fun F => F - ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C) h2
      simp only [sub_self, add_sub_cancel_right] at h4
      exact h4.symm
    have hB0 : c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) = 0 := by
      have e1 := hlin Unit (Finset.univ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u)
        (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)
      have e2 := hlin Unit (∅ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u)
        (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)
      simp only [Finset.univ_unique, Finset.sum_singleton, Finset.sum_empty] at e1 e2
      rw [hz] at e1
      rw [← e1, e2]
    rw [hempty, Finset.card_empty, zero_smul, hB0, smul_zero]

end GlobalTheory.QLastOne
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
namespace GlobalTheory.LocMod

theorem pi_e_self {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.π p.e = 1 := by
  have h := p.ι_π 1
  rw [map_one, mul_one] at h
  rw [← h, p.π_ι]

theorem pi_eq_zero_of {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {e : AE D} (h : e * p.e = 0) : p.π e = 0 := by
  have := congrArg p.π h
  rwa [map_mul, pi_e_self, mul_one, map_zero] at this

theorem up_down_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = t.map (fun x => p.e * x) := by
  unfold Place.up Place.down
  have hM : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ =
      (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [hM]
  ext i j
  simp only [Matrix.map_apply, p.ι_π]

theorem ratDatum_factor : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (Ξ Ξ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → (∀ γ, Ξ' γ = Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f f', IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) Ξ' f₀ f' → f' = comb ψ S T c f := by
  intro D k _ _ _ _ p ψ hψ _hdense S T Y Y' _ _ _ _ FS FT P PP e hPP hIdemAt hE hE' hstd Ξ Ξ' Ξk hΞk hΞ' c hc f₀ f f' hf₀ hvac hf hf'
  obtain ⟨Φ, hΦSB, hΦrat, hθ⟩ := hf
  obtain ⟨Φ', hΦ'SB, hΦ'rat, hθ'⟩ := hf'
  obtain ⟨T', hT'⟩ := hθ'.1
  have hf'T : f' = T' Φ' := hθ'.2 T' hT'
  have horth : e * p.e = 0 := GlobalTheory.T.splitPlaceIdempotent_mul_idemSum_eq_zero_of_not_mem D k p P PP e hPP hIdemAt hE
  have hstabp := GlobalTheory.T.standardLatticeHomCompletion_stable_splitIdempotent D S T p.e p.split
  have hθT' := GlobalTheory.T.placeModel_standardLattice_values_are_theta D ψ hψ S T _ (e + p.e) hE' f₀ T' hf₀ hvac hT'
  have hsb := GlobalTheory.T.isSchwartzBruhat_tensor_half_add_placeIdempotent D k p S T Y Y' FS FT e horth hstd hstabp Φ hΦSB
  have hmodel := GlobalTheory.T.isLocalModel_tensorWithHalfFunction D k p ψ S T Y Y' FS FT e horth Φ hΦSB.1 f₀ T' hT' hθT' hsb
  have hvacm := GlobalTheory.T.isPlaceModel_tensorIntegralIndicator D k p ψ S T Y Y' FS FT e horth hstd hstabp f₀ T' hT'
    (fun Φ₁ h₁ => GlobalTheory.T.isSchwartzBruhat_tensor_half_add_placeIdempotent D k p S T Y Y' FS FT e horth hstd hstabp Φ₁ h₁ _ (GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat k Y Y'))
  have hfT : f = T' (p.tensorOne FS FT Φ) := hθ.2 _ hvacm
  have hπe : p.π e = 0 := pi_eq_zero_of p horth
  have hpe2 : p.e * p.e = p.e := p.split.1
  have hid : Φ' = p.tensorAt FS FT Φ Ξk := by
    refine GlobalTheory.T.schwartzBruhat_half_eq_of_eq_on_rational D S T _ (e + p.e) hE' Φ' _ hΦ'SB (hsb Ξk hΞk) fun γ => ?_
    rw [hΦ'rat, hΞ']
    have hd : p.down FS FT (γ.map fun a => (e + p.e) * incA D a) = FT.γ * γ.map p.pr * FS.β := by
      unfold Place.down
      congr 2
      ext i j
      simp only [Matrix.map_apply, map_mul, map_add (f := _), hπe, pi_e_self, zero_add, one_mul, Place.pr]
    have hs : (γ.map fun a => (e + p.e) * incA D a) - p.up FS FT (p.down FS FT (γ.map fun a => (e + p.e) * incA D a)) =
        γ.map fun a => e * incA D a := by
      rw [up_down_eq]
      ext i j
      simp only [Matrix.sub_apply, Matrix.map_apply]
      have h2 : p.e * e = 0 := by rw [mul_comm]; exact horth
      linear_combination (-(incA D (γ i j))) * h2 + (-(incA D (γ i j))) * hpe2
    simp only [Place.tensorAt]
    rw [hs, hd, hΦrat]
  have key := hc.2 (T' ∘ₗ p.tensorL FS FT Φ) hmodel ⟨Place.intInd Y Y', GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat k Y Y'⟩ ⟨Ξk, hΞk⟩ rfl rfl
  rw [hf'T, hid, hfT]
  simpa only [LinearMap.comp_apply, Place.tensorL_apply, Place.tensorOne_apply] using key

end GlobalTheory.LocMod
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

theorem _root_.GlobalTheory.T.doubleThetaStep_splitPlace_value_periodGroup_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → Q.Typed f → ∀ g h₁ h₂, g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v) → h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v) → h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v) → ∀ a x y, ∀ r ∈ RFJ Q.k Q.n₁ (Q.c + 1 + 1) (σ + 1), ∀ j ∈ Q.L₁.J, ∀ r' ∈ R Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ j' ∈ Q.L₂.J, S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ (r * x * j)) (h₂ * Q.gl₂ (r' * y * j')) = S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) := by
  exact @GlobalTheory.DblInv.val_inv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlaceDoubleStepLocalIteratedIntegral_proof : ∀ D : D7, ValOne D := by
  first | exact @GlobalTheory.ValOneAt.valOne_all | exact GlobalTheory.ValOneAt.valOne_all | (intros; apply GlobalTheory.ValOneAt.valOne_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.locally_finite_of_tuple_conditions : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → OffLaw v w → GSupp (t := t) v → QFin v w → t.LocFin := by
  first | exact @GlobalTheory.FirstCells.locFin | exact GlobalTheory.FirstCells.locFin | (intros; apply GlobalTheory.FirstCells.locFin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB

theorem weilRepresentationOnFunctions_embed_mul {D : D7} {V W : HSp D} (om : Om V W) (e g : GA D V) (h : GA D W) (Φ : WO V W → ℂ) :
    om (g, h) (om (e, 1) Φ) = om (g * e, h) Φ := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem fjN_unfold : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → ∀ h₀, ∫ n in J.vN.𝓝, fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n ∂J.vN.ν = ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑 h₀
  obtain ⟨x₀, hx₀, hbase, hR, -, -⟩ := GlobalTheory.T.fourierBesselBasePoint_isUnfoldingBasePoint_spec D σ B
  obtain ⟨-, -, hvM, -⟩ := GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D
  obtain ⟨vb⟩ := hvM (σ + 1) J.W₀.rank
  obtain ⟨om', hom'⟩ := (hD ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  have hq : Quasi ψ J.W₀ B.L (Y h₀) := quasi_of_fam hY h₀
  have hTh := GlobalTheory.T.fourierBesselThetaIntegrand_isUnfoldingTheta D ψ s.weil.std σ J B (Y h₀) hq x₀ hx₀
  have hΦ' : IsThetaFunO ψ J.W B.V (s.om (J.d.emb0 h₀, 1) Φ) := s.weil.om_pres _ _ hΦ
  have h𝓑' : IsFundamentalDomain (GQ B.V ⊓ Rgrp B.V (rat x₀) : Subgroup (GA D B.V)) 𝓑 s.vW.μ := by
    rw [hR]; exact h𝓑
  have key := (GlobalTheory.T.unfold_over_flagUnipotent_thetaLift D hD ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om' s.weil hom' s.vS J.vN vb s.vU s.vW x₀
    (th J ψ B (Y h₀)) hbase hTh G (s.om (J.d.emb0 h₀, 1) Φ) hG hΦ' 𝓑 h𝓑').2
  have hL : (fun n : flagN J.d => fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n) =
      fun n => th J ψ B (Y h₀) n.1 * liftS s.om s.vW.μ s.vW.𝓕 G (s.om (J.d.emb0 h₀, 1) Φ) n.1 := by
    funext n
    simp only [fjSrcKerFun, JacLev.ker, th, Step.lift, liftS_apply, zl, weilRepresentationOnFunctions_embed_mul]
    ring
  have hR' : (fun h => G h * fl ψ J.d B.V s.vS vb s.vU (th J ψ B (Y h₀)) (rat x₀) (s.om (1, h) (s.om (J.d.emb0 h₀, 1) Φ))) =
      fun h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) := by
    funext h
    rw [weilRepresentationOnFunctions_embed_mul, one_mul, hx₀, (GlobalTheory.T.unfoldedTerm_basePoint_eq_flatMap_pairing D ψ σ J B s vb vL (Y h₀) _ hq (s.weil.om_pres _ _ hΦ)).1]
  rw [hL, ← hR']
  exact key

end GlobalTheory.Unf.FB

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.levelPrime_law_last_two_steps_all_tuples : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, ∀ f, IsContAut c.T f → ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ = o.mono r e (t.sBF j 0 h).χW * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  first | exact @GlobalTheory.FinPl.TLastAll.main | exact GlobalTheory.FinPl.TLastAll.main | (intros; apply GlobalTheory.FinPl.TLastAll.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.seeSawLevelPrimeLaw_doubleStep : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) = o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)))) := by
  first | exact @GlobalTheory.LevPrimeMid.lawLevelPrime_double | exact GlobalTheory.LevPrimeMid.lawLevelPrime_double | (intros; apply GlobalTheory.LevPrimeMid.lawLevelPrime_double <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.seeSawUnfoldedVacuaOfShape_proof : ∀ D : D7, GlobalTheory.SeeSaw.VacOfShape D := by
  first | exact @GlobalTheory.SeeSaw.VacShape.vacOfShape | exact GlobalTheory.SeeSaw.VacShape.vacOfShape | (intros; apply GlobalTheory.SeeSaw.VacShape.vacOfShape <;> assumption)
end
