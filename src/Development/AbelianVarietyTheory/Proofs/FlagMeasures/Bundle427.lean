module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle105
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle246
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle424
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle415
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle274
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle310
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle205
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle228
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle307
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle426
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle423
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle380
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle400
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle328
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle422
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle418
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.generic_iff_zero_defectGroup_coordinates : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (t₀.generic ↔ G.Gen (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam)) := by
  first | exact @GlobalTheory.HL.GenCoord.generic_iff_gen | exact GlobalTheory.HL.GenCoord.generic_iff_gen | (intros; apply GlobalTheory.HL.GenCoord.generic_iff_gen <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.globalAmplitude_eq_localAmplitudes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (R : ∀ p, LocNG.Reps (FP p)) (S1 : Finset (PlF D)) (Om : Finset {p // p ∈ S1}) (d : ∀ p : {p // p ∈ S1}, LocNG.Datum (FP p.1)), (∀ p, p ∉ S1 → (FP p).PrimeTo) → (∀ p, p ∈ Om ↔ ¬ (FP p.1).PrimeTo) → (∀ p : {p // p ∈ S1}, Over (FP p.1) (d p) (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1 t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u'))) → ∀ Q : Prop → Prop, ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ = ‖∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) else LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t))‖ := by
  first | exact @GlobalTheory.HL.AmpLoc.global_amp_local | exact GlobalTheory.HL.AmpLoc.global_amp_local | (intros; apply GlobalTheory.HL.AmpLoc.global_amp_local <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_global_vector_congruent_local_orthogonal : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O, c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), ∀ x ∈ lattice₂ D Z.M p Λ, x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) → ∃ l ∈ Lrep Λ F, x - baseChange₂ D p l ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))) (lattice₂ D Z.M p Λ) := by
  first | exact @GlobalTheory.LocApprox.approx | exact GlobalTheory.LocApprox.approx | (intros; apply GlobalTheory.LocApprox.approx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem lemmaPG_record : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg C : ℝ, 40 ≤ Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Glob0 D x eps CD Cg → Nodes D x eps → DuWin D 3 → AdmissibleBoundsFromSource.hyp D large₂ 3 C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ Formalism.L2.SG.RowsConc.TFrameAt D ∧ C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 ∧ C ≤ (D.R.k : ℝ) := by
  intro hSM hDs eps CD heps0 heps1 hCD C' Cl Cg C hCl40 hClCD
  have hCl0 : (0 : ℝ) < Cl := by linarith
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.dataConditions_of_global_and_real_rows eps CD heps0 heps1 hCD
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.hypotheses_of_global_rows_and_nodes eps CD heps0 heps1 hCD C' Cl Cg hCl0 hClCD
  obtain ⟨x3, hx3⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD heps0 heps1 hCD (max C (3 * Real.exp 8))
  refine ⟨max x1 (max x2 x3), ?_⟩
  intro x hx D large₂ hL hC' hTies hAdm hG hN hW
  have hx1' : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2' : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3' : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx

  obtain ⟨-, hAr⟩ := GlobalTheory.T.two_le_rootDiscriminant_and_split_arithmetic_conditions D
  have hData : StandingNumericalData D 3 := hx1 x hx1' D Cg 3 hG hN hAr hW

  obtain ⟨-, -, -, -, -, hm1, hk, hxe⟩ := hx3 x hx3' _ _ _ _ _ hG.nums
  have hxe0 : (0 : ℝ) ≤ x ^ eps := le_of_lt (lt_trans zero_lt_one hxe)
  have h3 : (3 : ℝ) ≤ max C (3 * Real.exp 8) :=
    le_trans (by have := Real.add_one_le_exp (8 : ℝ); linarith) (le_max_right _ _)
  have hCm : C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxe0) hm1
  have h3m : 3 * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right h3 hxe0) hm1
  have h3k : 3 * Real.exp 8 ≤ (D.R.k : ℝ) := le_trans (le_max_right _ _) hk
  have hCk : C ≤ (D.R.k : ℝ) := le_trans (le_max_left _ _) hk

  have hLpos : 0 < large₂.sc.L := by rw [hL]; linarith
  have hb1 : 1 < large₂.sc.b := by
    show 1 < Real.exp large₂.sc.L
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hLpos
  have hb0 : 0 < large₂.sc.b := lt_trans zero_lt_one hb1
  have hm0 : (0 : ℝ) < (D.R.m : ℝ) := by
    have := D.R.two_le_m
    exact_mod_cast (show 0 < D.R.m by omega)
  have hT1 : ∀ u, (1 : ℝ) ≤ Tr D u := fun u => by
    show (1 : ℝ) ≤ ((D.mem u).A.T : ℝ)
    exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hmb : (D.R.m : ℝ) * Real.log large₂.sc.b ≠ 0 := (mul_pos hm0 (Real.log_pos hb1)).ne'
  obtain ⟨CT0, hCT0⟩ : ∃ c : ℝ, c * ((D.R.m : ℝ) * Real.log large₂.sc.b) = ∑ v, Real.log (Tr D v) :=
    ⟨(∑ v, Real.log (Tr D v)) / ((D.R.m : ℝ) * Real.log large₂.sc.b), div_mul_cancel₀ _ hmb⟩
  have hwin0 : ∀ u, large₂.sc.b ^ ((0 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧
      Tr D u ≤ large₂.sc.b ^ (CT0 * (D.R.m : ℝ)) := by
    intro u
    refine ⟨by rw [zero_mul, Real.rpow_zero]; exact hT1 u, ?_⟩
    rw [Real.rpow_def_of_pos hb0,
      show Real.log large₂.sc.b * (CT0 * (D.R.m : ℝ)) = CT0 * ((D.R.m : ℝ) * Real.log large₂.sc.b) by ring, hCT0]
    calc Tr D u = Real.exp (Real.log (Tr D u)) :=
          (Real.exp_log (lt_of_lt_of_le zero_lt_one (hT1 u))).symm
      _ ≤ Real.exp (∑ v, Real.log (Tr D v)) :=
          Real.exp_le_exp.mpr (Finset.single_le_sum (fun v _ => Real.log_nonneg (hT1 v))
            (Finset.mem_univ u))

  have hHyp0 : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 := hx2 x hx2' D large₂ 0 CT0 hL hC' hG hN hwin0
  have hCnt : Cnt.Hyp0 D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 :=
    (⟨hHyp0, hData, by norm_num⟩ : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 ∧ StandingNumericalData D 3 ∧ (1 : ℝ) ≤ 3)

  have hFr := (GlobalTheory.pgFrame_at_record hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm).1
  have hwin := GlobalTheory.T.levelPrimes_size_bounds_columnDimension hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm

  have hHyp : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) :=
    hx2 x hx2' D large₂ (1 / 2) (4 * Cg + 13) hL hC' hG hN hwin
  exact ⟨(⟨hData, hHyp, by norm_num⟩ :
      StandingNumericalData D 3 ∧ StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ (1 : ℝ) ≤ 3), hFr, hCm, hCk⟩

end GlobalTheory.Diag.PG
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsRange

theorem one_le_foldr_max (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons a L ih => exact le_trans ih (le_max_right _ _)

theorem le_foldr_max (L : List ℝ) (x : ℝ) (hx : x ∈ L) : x ≤ L.foldr max 1 := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem ratio_le (r k N e : ℕ) (b v g θ θ' ka X Cg : ℝ) (hb : 2 ≤ b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) (hg : 1 ≤ g)
    (hgb : g ≤ b ^ (2 * Cg)) (hka : ka = Real.pi / v) (hθ0 : 0 < θ) (hθ : θ ≤ b ^ X) (hθ' : b ^ (-X) ≤ θ')
    (hN : N ≤ r ^ 2) (he : e ≤ r * k) :
    (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N) ≤
      b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) * v⁻¹ ^ e := by
  have hb0 : 0 < b := by linarith
  have hv0 : 0 < v := by linarith
  have hg0 : 0 < g := by linarith
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'
  have hpi := Real.pi_pos
  have e1 : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  have e2 : (2 * v) ^ (-((r : ℝ) * k)) = ((2 * v) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast]; push_cast; rfl
  have e3 : 2 * ka / g / (2 * Real.pi) = (v * g)⁻¹ := by
    rw [hka]; field_simp
  have e4 : (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N)
      = (θ * θ'⁻¹ * (2 ^ (r ^ 2) * (v * g) ^ N)) * v⁻¹ ^ (r * k) := by
    rw [e1, e2, e3, pow_add, mul_pow 2 v, inv_pow, inv_pow]
    field_simp
  rw [e4]
  have h1 : θ'⁻¹ ≤ b ^ X := by
    have := inv_anti₀ (Real.rpow_pos_of_pos hb0 _) hθ'
    rwa [Real.rpow_neg hb0.le, inv_inv] at this
  have h2 : (v * g) ^ N ≤ (b * b ^ (2 * Cg)) ^ (r ^ 2) := by
    refine le_trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hv hg) hN) ?_
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul (by linarith) hgb hg0.le hb0.le) _
  have h3 : (2 : ℝ) ^ (r ^ 2) ≤ b ^ (r ^ 2) := pow_le_pow_left₀ (by norm_num) hb _
  have h4 : v⁻¹ ^ (r * k) ≤ v⁻¹ ^ e := pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hv) he
  have e5 : b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) =
      b ^ X * b ^ X * (b ^ (r ^ 2) * (b * b ^ (2 * Cg)) ^ (r ^ 2)) := by
    rw [← mul_pow, ← mul_assoc, ← Real.rpow_add hb0, Real.rpow_add hb0 (2 * X), Real.rpow_mul hb0.le (2 + 2 * Cg),
      Real.rpow_add hb0 2, Real.rpow_two, two_mul X, sq b, ← Real.rpow_natCast _ (r ^ 2)]
    push_cast; rfl
  rw [e5]
  gcongr

theorem absBd_le (r k : ℕ) (b v Q A De Dd C M m : ℝ) (hr : 1 ≤ r) (hm : m = 2 * r + 2) (hb : Real.exp 1 ≤ b)
    (hv : 0 < v) (hM : 0 ≤ M) (hDe : 1 ≤ De) (hD : 0 ≤ Dd)
    (hQ : Q ≤ b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r)))
    (hC : A + 44 + 24 * M ≤ C) (hC1 : 14 ≤ C) (hC2 : 8 * Real.pi * Real.exp 1 ≤ C) :
    Q * absBd k r (b ^ (M * m)) De Dd ≤
      (b ^ (C * m) * De) ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
  have hb1 : 1 ≤ b := le_trans (Real.one_le_exp (by norm_num)) hb
  have hb0 : 0 < b := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm0 : 0 ≤ m := by linarith
  have hpi := Real.pi_pos
  have h1 : (4 * r : ℝ) ≤ b ^ m := by
    have a1 : Real.exp m ≤ b ^ m := by
      rw [← Real.exp_one_rpow]; exact Real.rpow_le_rpow (Real.exp_pos 1).le hb hm0
    have a2 : (r : ℝ) + 1 + 1 ≤ Real.exp (r + 1) := Real.add_one_le_exp _
    have a3 : Real.exp m = Real.exp (r + 1) * Real.exp (r + 1) := by rw [← Real.exp_add, hm]; ring_nf
    nlinarith
  have h2 : (4 * r : ℝ) ^ (44 * r ^ 3) ≤ b ^ (44 * (m * (r : ℝ) ^ 3)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) h1 _) (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h3 : (b ^ (M * m)) ^ (24 * r ^ 3) = b ^ (24 * M * (m * (r : ℝ) ^ 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h4 : De ^ (14 * r ^ 2) ≤ De ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hDe ?_
    push_cast
    have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
    exact mul_le_mul hC1 this (by positivity) (by linarith)
  have h5 : (8 * Real.pi * Real.exp 1 / k) ^ (r * (k - 2 - r)) ≤ (C / k) ^ (r * (k - 2 - r)) := by
    gcongr
  have h6 : b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) ≤
      (b ^ (C * m)) ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_mul hb0.le]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have t : 0 ≤ m * (r : ℝ) ^ 3 := by positivity
    have c : A + 44 + 24 * M ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right c t
    nlinarith
  have hC0 : 0 ≤ C := by linarith
  calc Q * absBd k r (b ^ (M * m)) De Dd
      ≤ (b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r))) *
        (b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) * De ^ (C * (r : ℝ) ^ 3) *
          (C / k) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹) := by
        unfold absBd
        rw [h3]
        refine mul_le_mul hQ ?_ (by positivity) (by positivity)
        gcongr
    _ = (b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3))) *
          De ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
        rw [show C / (k * v) = C / k * v⁻¹ by rw [← div_div, div_eq_mul_inv], mul_pow]; ring
    _ ≤ _ := by
        rw [Real.mul_rpow (by positivity) (by linarith)]
        gcongr

theorem abs_range : ∀ Cg cb Cu cT CT C0 C1 CMo : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ Cn : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo →
      ABSr D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro Cg cb Cu cT CT C0 C1 CMo
  refine ⟨8 * |C1| + 2 * |Cg| + 46 + 24 * max CMo 0 + 8 * Real.pi * Real.exp 1, fun C hC => ⟨4, ?_⟩⟩
  intro Cn D large₂ C' Cl hBig hMom hZ τ w w' hTT θ hθ W hW lam' hlam S hS γ p hp θ' hθ' νR hνR hDr
  obtain ⟨hrd, -, hm4⟩ := hBig
  have hm4' : 4 ≤ D.R.m := by exact_mod_cast hm4
  obtain ⟨-, -, hb, hm, -, -, -, hk, hv, -, hka, hvb, hg, hgb, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hrd hZ
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hv0 : 0 < D.host.v := by linarith
  have hg0 : 0 < gg D := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'.1
  have hpi := Real.pi_pos
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hr : 1 ≤ D.R.rS := by omega
  have hk' : 2 * D.R.rS + 6 ≤ D.R.k := by
    have : D.R.m * 2 ≤ D.R.m ^ 4 := by
      rw [show D.R.m ^ 4 = D.R.m * D.R.m ^ 3 by ring]
      exact Nat.mul_le_mul_left _ (le_trans (by norm_num) (Nat.pow_le_pow_left hm4' 3))
    omega
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.majorantMomentBound_both_sides D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm4' hMom hZ τ w w' hTT θ hθ W hW
    lam' hlam S hS
  obtain ⟨-, -, hμN, hS1, hS2⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' S hθ0 hv0 hTT hW hS
  rw [hμN] at hS1 hS2
  have hDr' : Dr D.R.k D.R.rS W.z W.z' γ = ‖DminN W.z W.z' γ D.R.rS‖ := by
    unfold Dr DminN; rw [dite_eq_left (by omega)]
  have hTF : TwoFl D.R.k D.R.rS W.z W.z' γ :=
    ⟨hS1.1, hS2.1, hS1.2.1, hS2.2.1, hp.1, hp.2.2, by rw [hDr']; exact norm_ne_zero_iff.2 hDr⟩
  obtain ⟨hends, -, -, -, hD0, -⟩ := GlobalTheory.T.cellPoint_blockEnds_leadingMinors D W.z W.z' γ p hS1.1 hS2.1 hS1.2.1 hS2.2.1 hp
  set De : ℝ := ((ptBlockEnds p).map fun l => max 1 ‖DminN W.z W.z' γ l‖⁻¹).foldr max 1 with hDe
  have hDe1 : 1 ≤ De := one_le_foldr_max _
  have hOK : DeOK D.R.k D.R.rS W.z W.z' γ De := by
    refine ⟨hDe1, fun l _ hl => ?_⟩
    have e : Dmin D.R.k D.R.rS W.z W.z' γ l = DminN W.z W.z' γ l.val := by
      unfold DminN; rw [dite_eq_left l.2]
    rw [e] at hl ⊢
    rcases Nat.eq_zero_or_pos l.val with h0 | h0
    · rw [h0, hD0]; simpa using hDe1
    · exact le_trans (le_max_right 1 _)
        (le_foldr_max _ _ (List.mem_map.2 ⟨l.val, (hends l.val h0).1 hl, rfl⟩))
  obtain ⟨p', μR, hroot, hquot⟩ := hνR
  obtain ⟨hN, hnorm⟩ := GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure D W.z W.z' p' γ μR θ' hTF hroot hθ'0.le (by positivity)
  have hM0 : 0 ≤ max CMo 0 := le_max_right _ _
  have hH : 1 ≤ large₂.sc.b ^ (max CMo 0 * D.R.m) := Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨hint, hbd⟩ := GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le D.R.k D.R.rS W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' _ νR S.Φ S.Φ' γ
    S.cN _ _ _ De hr hk' (by positivity) (by positivity) hH hS1 hS2 hM1 hM2 hTF hOK hnorm hquot
  refine ⟨hint, le_trans hbd ?_⟩
  rw [hDr']
  have hmr : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  have hr' : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg Cg
  have a3 : 0 ≤ 8 * Real.pi * Real.exp 1 := by positivity
  refine absBd_le D.R.rS D.R.k large₂.sc.b D.host.v _ (8 * |C1| + 2 * |Cg| + 2) De _ C (max CMo 0) D.R.m hr hmr hb.le hv0
    hM0 hDe1 (norm_nonneg _) ?_ (by linarith) (by linarith) (by linarith)
  refine le_trans (ratio_le D.R.rS D.R.k _ (D.R.rS * (D.R.k - 2 - D.R.rS)) large₂.sc.b D.host.v (gg D) θ θ' D.host.ka _ Cg
    hb2 hv hvb hg hgb hka hθ0 hθ.2 hθ'.1 hN (Nat.mul_le_mul_left _ (by omega))) ?_
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
  have r3 : (D.R.rS : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
  have r23 : (D.R.rS : ℝ) ^ 2 ≤ (D.R.rS : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
  have m0 : (1 : ℝ) ≤ D.R.m := by linarith
  have b1 : (D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.m * (D.R.rS : ℝ) ^ 3) := by
    have : (D.R.m : ℝ) ≤ 4 * (D.R.rS : ℝ) ^ 3 := by linarith
    nlinarith
  have b2 : (D.R.rS : ℝ) ^ 2 ≤ D.R.m * (D.R.rS : ℝ) ^ 3 := by nlinarith
  have c1 : C1 * (D.R.m : ℝ) ^ 2 ≤ |C1| * (4 * (D.R.m * (D.R.rS : ℝ) ^ 3)) :=
    mul_le_mul (le_abs_self _) b1 (by positivity) a1
  have c2 : Cg * (D.R.rS : ℝ) ^ 2 ≤ |Cg| * (D.R.m * (D.R.rS : ℝ) ^ 3) :=
    mul_le_mul (le_abs_self _) b2 (by positivity) a2
  nlinarith

end GlobalTheory.Amp.AbsRange
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

private lemma hsNormSq_eq_sum_norm_sq {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (J : Wq →L[ℂ] Wp) :
    hsNormSq J = ∑ i, ‖J (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_le_finrank_target_mul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (J : Wq →L[ℂ] Wp) : hsNormSq J ≤ Module.finrank ℂ Wp * ‖J‖ ^ 2 := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq

  rw [hsNormSq_eq_sum_norm_sq]
  calc ∑ i, ‖J (stdOrthonormalBasis ℂ Wq i)‖ ^ 2
        = ∑ i, ∑ j, ‖⟪(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j),
            stdOrthonormalBasis ℂ Wq i⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← (stdOrthonormalBasis ℂ Wp).sum_sq_norm_inner_right (J (stdOrthonormalBasis ℂ Wq i))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (stdOrthonormalBasis ℂ Wq).sum_sq_norm_inner_left _
    _ ≤ ∑ _j : Fin (Module.finrank ℂ Wp), ‖J‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hle : ‖(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j)‖ ≤ ‖J‖ := by
          calc _ ≤ ‖ContinuousLinearMap.adjoint J‖ * ‖stdOrthonormalBasis ℂ Wp j‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ = ‖J‖ := by
                rw [LinearIsometryEquiv.norm_map, (stdOrthonormalBasis ℂ Wp).orthonormal.1 j, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = Module.finrank ℂ Wp * ‖J‖ ^ 2 := by simp

theorem sqrt_hsNormSq_amplitude_le_degBd : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → ∀ (j : ℕ) (hj : j ≤ D.R.rS) (q : ℕ) (γ : Mat D.R.k D.R.rS) (s H₁ De : ℝ) (μR νR : Measure (Mt D.R.k D.R.rS)), 1 ≤ j → j + 2 ≤ D.R.k → 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ q → 0 < s → 1 ≤ H₁ → TailBd W.z W.νS A.Φ q H₁ → TailBd W.z' W.νS' A.Φ' q H₁ → DeOK D.R.k D.R.rS W.z W.z' γ De → IsNormalFormStabilizerMeasure D.R.k D.R.rS hj W.z W.z' γ s μR → IsQuotMeas W.μG μR νR → Real.sqrt (hsNormSq (A.J νR γ)) ≤ Real.sqrt (Module.finrank ℂ W.Wp) * (((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) / s * degBd D.R.k D.R.rS j q H₁ De (Dj D.R.k D.R.rS hj W.z W.z' γ) (sgV D.R.k D.R.rS W.z W.z' γ H₁)) := by
  intro D τ w w' θ W lam A hv hθ hw hw' hW hS j hj q γ s H₁ De μR νR hj1 hjk hq hs hH hT hT' hDe hN hQ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.amplitude_one_side_of_good_local_data D τ w w' θ W lam A hv hθ hw hw' hW hS
  have hκ : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ) (by positivity)
  have hb := (GlobalTheory.T.amplitude_degenerate_operatorNorm_le_realPlace D.R.k D.R.rS j hj W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' μR νR
    A.Φ A.Φ' γ A.cN _ s H₁ De q hj1 hjk hq hκ hs hH h1 h2 hT hT' hDe hN hQ).2

  calc Real.sqrt (hsNormSq (A.J νR γ))
        ≤ Real.sqrt (Module.finrank ℂ W.Wp * ‖A.J νR γ‖ ^ 2) :=
          Real.sqrt_le_sqrt (hsNormSq_le_finrank_target_mul (A.J νR γ))
    _ = Real.sqrt (Module.finrank ℂ W.Wp) * ‖A.J νR γ‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

end GlobalTheory.Amp
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.block_projection_bessel : Hyps → AmpKF → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  first | exact @GlobalTheory.CellPieri.amp_pieri | exact GlobalTheory.CellPieri.amp_pieri | (intros; apply GlobalTheory.CellPieri.amp_pieri <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.depthZeroIdentity_finiteType_of_typePrimeComponent : ∀ (D : D7) (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D), IsComp I rep cp → ∀ σ k v (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), (∀ y ∈ fixK1 (cp σ k v).ρ, actK (cp σ k v).ρ a y = y) → ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → GlobalTheory.LabPin.SerFix (rep σ) s a := by
  first | exact @GlobalTheory.DepthZeroSer.serFix_of_comp | exact GlobalTheory.DepthZeroSer.serFix_of_comp | (intros; apply GlobalTheory.DepthZeroSer.serFix_of_comp <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localHaarMeasures_pullback_realGroup : GlobalTheory.TypeAsm.PullC := by
  first | exact @GlobalTheory.PullbackComparison.pullC_holds | exact GlobalTheory.PullbackComparison.pullC_holds | (intros; apply GlobalTheory.PullbackComparison.pullC_holds <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem levelConj_holds : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), LevelConj D F := by
  intro D F X hK u wt ιA h0 hW hI hL
  obtain ⟨Fr, hFr⟩ := GlobalTheory.T.exists_frame_adelicColumnLattice_linked_reference D X u wt ιA hW hI
  obtain ⟨hMq, -, -, -, -, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  obtain ⟨hT, hg, hTg, hf, hNk, hH, hdet⟩ := record_facts D u
  have hΛ : ∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat D.host.F (F u).cls0.lev.Lb ↔ x ∈ hat D.host.F (Mq wt) := by
    intro x
    rw [hMq x]
    exact hL x
  obtain ⟨h1, hL1, hK1⟩ := GlobalTheory.T.exists_adelic_correction_level_character D.host.F D.host.E D.sp.cm (D.R.N 0) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) hH hdet
    (D.mem u).A.T D.R.f D.R.t D.R.k D.R.k D.R.k (D.R.N 0) D.host.g (F u).cls0.lev (F u).gl (F u).glev0
    hNk.symm hNk.symm hNk.symm rfl (D.mem u).A.T_prime D.host.g_prime D.host.g_ne hTg hg hT hf
    (hat D.host.F (Mq wt)) Fr h0 hΛ
  refine ⟨h1, fun x => ?_, fun h y hy => ?_⟩
  · exact (hL1 x).trans (hMq x)
  · have hin := GlobalTheory.T.mem_columnLevel_iff_mem_linkedFrameLevel D X u wt ιA hW hI hK Fr hFr h y hy
    have hch := GlobalTheory.T.columns_character_eq_linked_frame_character D X u wt ιA hW hI hK Fr hFr h y hy
    refine ⟨hin.trans (hK1 y).1, fun hk hy' => ?_⟩
    rw [hch hk]
    exact (hK1 y).2 hy'

end GlobalTheory.St.G
end
