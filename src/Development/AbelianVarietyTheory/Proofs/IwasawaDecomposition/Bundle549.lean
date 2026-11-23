module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle525
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle548
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle010
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationRulesHold
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle536
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle544
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Formalism.SharpRestriction.GrowthBounds.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle543
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle546
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries



noncomputable section

namespace GlobalTheory.ArcNormal

theorem exists_chart_theta_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ (κ : ℂ) (r : PowerSeries ℂ) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)), κ ≠ 0 ∧ PowerSeries.constantCoeff r ≠ 0 ∧ IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ ∧ IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ ∧ ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (M.θ j) = valAt' x _ (w₁.s (fun _ => j, k)).val * ((κ * rw) * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z) := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hL2 := GlobalTheory.abelianSchemeLaws_all.2
  obtain ⟨hA, hB⟩ := GlobalTheory.theta_generates_along_arc hL.globalFns hL.secBaseChange Y a χ W
  have hw0 : Ha.T < ((Ha.T + 1 : ℝ) * Complex.I : ℂ).im := by simp
  have hne : ∃ j, th.f j ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨hs, hp⟩ := Θ.pos _ hw0
    have h7 := (GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic g Θ.S (Θ.τ ((Ha.T + 1 : ℝ) * Complex.I)) Θ.c₁ Θ.c₂ hs hp Θ.half₁ Θ.half₂ Θ.c₁_S).1
    apply h7
    funext v
    set w := ((Ha.T + 1 : ℝ) * Complex.I : ℂ) with hwdef
    have hz : Θ.h.mulVec (∑ k, v k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = v := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' v).symm
    rw [← hz]
    generalize (∑ k, v k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = z
    obtain ⟨fr, -, n, -, -, hv⟩ := Θ.onB w hw0
    obtain ⟨j, hj⟩ := exists_chart a.D₀.P.isLB ((show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) (IsLocalRing.closedPoint ℂ))
    have hU : ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) ⁻¹ᵁ a.D₀.P.L.U j := fun q _ =>
      (Subsingleton.elim (α := PrimeSpectrum ℂ) (IsLocalRing.closedPoint ℂ) q) ▸ hj
    have e := hv j z hU
    have e0 : valAt' (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) (a.D₀.P.L.U j) (th.f j) = 0 := by
      rw [hc j]
      exact (dif_pos hU).trans ((congrArg _ (map_zero _)).trans (map_zero _))
    rw [e0] at e
    have := (mul_eq_zero.1 e.symm).resolve_right (n j z hU)
    exact (mul_eq_zero.1 this).resolve_left Θ.κ_ne
  have hth : GlobalTheory.ArcQ.ThNZ th := ((GlobalTheory.ThetaOverField.nonzero_generates hL hL2 ℂ a.D₀ th).1).1 hne
  obtain ⟨⟨t, ht, -⟩, hnz⟩ := hB th
  obtain ⟨σ0, fam, hfam0, hexp, -, -, -, -, ⟨w₂, hw₂⟩, hrest⟩ := hA t (hnz t ht hth _)
  have hpull : GlobalTheory.ThetaUnit.IsPullTerm W.P.D.toPre W.φ W.w th (fam 0) := hfam0 ▸ ht
  obtain ⟨-, hr⟩ := (hrest w₂ hw₂.1).2 hPI
  obtain ⟨r, hr⟩ := hr M.U M.θ hM ⟨M.θ_mem, M.gen⟩
  obtain ⟨w₀, h₀⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso Y.m0.toSABMap
  obtain ⟨w₁, h₁⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso Y.m
  obtain ⟨fr₀, hfr₀⟩ := Θ.frame _ hw0
  obtain ⟨κ, hκ, -, -, hmain⟩ := Ha.theta th σ0 fam Θ.bas Θ.S Θ.h Θ.τ Θ.c₁ Θ.c₂ w₂ w₁ w₀ hne hexp hpull Θ.sympl Θ.ker Θ.per Θ.half₁ Θ.half₂ hw₂ h₁ h₀ ⟨_, fr₀, hw0, hfr₀⟩
  obtain ⟨T', hT'⟩ := hmain M.U M.θ r.val hM M.θ_mem hr
  refine ⟨κ, r.val, w₀, w₁, hκ, ?_, h₀, h₁, T', hT'⟩
  exact ((PowerSeries.isUnit_iff_constantCoeff).1 r.isUnit).ne_zero

theorem exists_bounds_of_sumsAt : ∀ (κ : ℂ), κ ≠ 0 → ∀ r : PowerSeries ℂ, PowerSeries.constantCoeff r ≠ 0 → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ rw : ℂ, SumsAt r w rw → C⁻¹ ≤ ‖κ * rw‖ ∧ ‖κ * rw‖ ≤ C := by
  intro κ hκ r hr0
  by_cases hex : ∃ w₀ rw₀, SumsAt r w₀ rw₀
  swap
  · exact ⟨0, 1, one_pos, fun w _ rw h => (hex ⟨w, rw, h⟩).elim⟩
  obtain ⟨w₀, rw₀, h₀⟩ := hex
  have hq₀ : 0 < ‖eTwoPi w₀‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  obtain ⟨B, hB⟩ : ∃ B, ∀ n, ‖PowerSeries.coeff n r * eTwoPi w₀ ^ n‖ ≤ B := by
    obtain ⟨B, hB⟩ := h₀.summable.tendsto_atTop_zero.norm.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have ha₀ : 0 < ‖PowerSeries.constantCoeff r‖ := norm_pos_iff.2 hr0
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  set A := ‖PowerSeries.constantCoeff r‖ with hA
  set B' := max B 1 with hB'
  have hB'1 : 1 ≤ B' := le_max_right _ _
  set t : ℝ := min (1 / 2) (A / (4 * B')) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos ha₀ (by linarith))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htB : t ≤ A / (4 * B') := min_le_right _ _
  have htB' : 4 * B' * t ≤ A := by
    have := mul_le_mul_of_nonneg_left htB (by linarith : (0:ℝ) ≤ 4 * B')
    rwa [mul_div_cancel₀ _ (by linarith : (4 * B' : ℝ) ≠ 0)] at this
  refine ⟨-Real.log (t * ‖eTwoPi w₀‖) / (2 * Real.pi), max (3 / 2 * (‖κ‖ * A)) (2 / (‖κ‖ * A)),
    lt_max_of_lt_left (by positivity), fun w hw rw hrw => ?_⟩
  have hqn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    simp [eTwoPi, Complex.norm_exp]
  have hq : ‖eTwoPi w‖ ≤ t * ‖eTwoPi w₀‖ := by
    rw [hqn]
    have hpos : 0 < t * ‖eTwoPi w₀‖ := mul_pos ht0 hq₀
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.2
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).1 hw
    linarith
  have hf := (hasSum_nat_add_iff' 1).2 hrw
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hf
  have hg : HasSum (fun n : ℕ => B' * t * t ^ n) (B' * t * (1 - t)⁻¹) :=
    (hasSum_geometric_of_lt_one ht0.le (by linarith)).mul_left (B' * t)
  have hle : ‖rw - PowerSeries.constantCoeff r‖ ≤ B' * t * (1 - t)⁻¹ := by
    refine hf.norm_le_of_bounded hg fun n => ?_
    have h1 : ‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w₀‖ ^ (n + 1) ≤ B' := by
      have := hB (n + 1)
      rw [norm_mul, norm_pow] at this
      exact this.trans (le_max_left _ _)
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w‖ ^ (n + 1)
        ≤ ‖PowerSeries.coeff (n + 1) r‖ * (t * ‖eTwoPi w₀‖) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq _) (norm_nonneg _)
      _ = (‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w₀‖ ^ (n + 1)) * t ^ (n + 1) := by ring
      _ ≤ B' * t ^ (n + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = B' * t * t ^ n := by ring
  have h2 : B' * t * (1 - t)⁻¹ ≤ A / 2 := by
    have h1t : 0 < 1 - t := by linarith
    rw [← div_eq_mul_inv, div_le_iff₀ h1t]
    nlinarith
  have hlo : A / 2 ≤ ‖rw‖ := by
    have := norm_sub_norm_le (PowerSeries.constantCoeff r) rw
    rw [norm_sub_rev] at this
    linarith
  have hhi : ‖rw‖ ≤ 3 / 2 * A := by
    have := norm_sub_norm_le rw (PowerSeries.constantCoeff r)
    linarith
  rw [norm_mul]
  constructor
  · have hx : 0 < ‖κ‖ * A := mul_pos hκ' ha₀
    calc (max (3 / 2 * (‖κ‖ * A)) (2 / (‖κ‖ * A)))⁻¹ ≤ (2 / (‖κ‖ * A))⁻¹ :=
          inv_anti₀ (by positivity) (le_max_right _ _)
      _ = ‖κ‖ * (A / 2) := by field_simp
      _ ≤ ‖κ‖ * ‖rw‖ := mul_le_mul_of_nonneg_left hlo hκ'.le
  · calc ‖κ‖ * ‖rw‖ ≤ ‖κ‖ * (3 / 2 * A) := mul_le_mul_of_nonneg_left hhi hκ'.le
      _ = 3 / 2 * (‖κ‖ * A) := by ring
      _ ≤ _ := le_max_left _ _

theorem theta_const_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → C⁻¹ ≤ ‖c₀‖ ∧ ‖c₀‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  obtain ⟨κ, r, w₀, w₁, hκ, hr0, h₀, h₁, T', hT'⟩ := exists_chart_theta_unit E H Dw l Xo c σ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  obtain ⟨T₃, C, hC, hb⟩ := exists_bounds_of_sumsAt κ hκ r hr0
  refine ⟨max T' (max Ha.T T₃), C, hC, fun w hw yF e₁ e₂ hz x φ hx u c₀ hrig hfib hfn => ?_⟩
  simp only [max_lt_iff] at hw
  obtain ⟨rw, hrw, hval⟩ := hT' w hw.1
  obtain rfl := GlobalTheory.T.thetaConstant_uniformisedChartFibre_eq_familyConstant E H Dw l Xo c σ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM w hw.2.1 w₀ w₁ h₀ h₁ (κ * rw) hval yF e₁ e₂ hz x φ hx u c₀ hrig hfib hfn
  exact hb w hw.2.2 rw hrw

end GlobalTheory.ArcNormal
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcLieCoord

open MonoidalCategory CartesianMonoidalCategory MonObj Filter GlobalTheory.ArcLie

theorem comb_tan {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) (hv : ∀ k, IsTangent (v k)) (c : Fin n → R) (w : epsR R ⟶ G) (hc : IsLieComb c v w) :
    IsTangent w := by
  rw [GlobalTheory.PowLie.isLieComb_iff_prod] at hc
  subst hc
  rw [GlobalTheory.PowLie.isTangent_iff]
  have e0 : ∀ a : R, GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc a = GlobalTheory.PowLie.zeroPt R := fun a => by
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]
    rw [GlobalTheory.TanMod.spMap_comp']
    congr 1
    refine RingHom.ext fun r => ?_
    simp [epsScaleR]
  have e1 := map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G) (GlobalTheory.PowLie.zeroPt R)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k)
    Finset.univ
  refine e1.trans ?_
  refine (Finset.prod_congr rfl fun k _ => ?_).trans (Finset.prod_const_one)
  show GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1
  rw [← Category.assoc, e0, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]
  rfl

theorem sep_laurent {X : Scheme.{0}} {x : Sp (PowerSeries ℂ) ⟶ X} {G : Over X} {G' : Over (Sp (PowerSeries ℂ))} [GrpObj G]
    [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {n : ℕ}
    (v : Fin n → (epsR (PowerSeries ℂ) ⟶ G')) (hv : IsLieBasis v) {V : G.left.Opens} (hA : IsAffineOpen V)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) (a : Fin n → ℂ⸨X⸩)
    (ha : ∀ f : Γ(G.left, V), ∑ k, a k * HahnSeries.ofPowerSeries ℤ ℂ (valR ((v k).left ≫ φ) V f).snd = 0) : a = 0 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (PowerSeries ℂ)) (S := ℂ⸨X⸩)
    Finset.univ a
  choose b hb using fun k => hd k (Finset.mem_univ k)
  have hinj : Function.Injective (HahnSeries.ofPowerSeries ℤ ℂ) := HahnSeries.ofPowerSeries_injective
  have hb' : ∀ k, HahnSeries.ofPowerSeries ℤ ℂ (b k) = HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * a k := fun k => by
    rw [← LaurentSeries.coe_algebraMap, hb k, Algebra.smul_def, LaurentSeries.coe_algebraMap]
  have h0 := GlobalTheory.T.derivatives_separate_lieBasis_coeffs_cartesian h v hv hA hV b fun f => hinj (by

    rw [map_sum, map_zero]
    have e := congrArg (fun t => HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * t) (ha f)
    simp only [mul_zero, Finset.mul_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hb', _root_.mul_assoc])
  funext k
  have hd0 : HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) ≠ 0 := fun e =>
    nonZeroDivisors.coe_ne_zero d (hinj (e.trans (map_zero _).symm))
  have := hb' k
  rw [h0, Pi.zero_apply, map_zero] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hd0

theorem valR_eq_ev' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = ev x U h f := by
  rw [valR, dite_eq_left h]; rfl

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem point_snd {Y : Model Xo c β} (M : GChart Y) {z : Sp ℂ ⟶ Y.X} {hz : ⊤ ≤ z ⁻¹ᵁ M.U} {x : KeyIn ℂ}
    {φ : x.P.A.left ⟶ Y.t.G.left} (hK : GlobalTheory.ArcNormal.KeyAtVia M z hz x φ) {g : ℕ} (u : HolUnif x.P.A x.P.L g)
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y.t.G.left)) (he : ∀ t, e t = (u.ex t).left ≫ φ) (i : Fin x.P.g) (j : Fin M.n)
    (hij : (i : ℕ) = j) (wv : Fin g → ℂ) (hd : u.IsDiff wv (x.v i)) (V : Y.t.G.left.Opens)
    (hV : ⊤ ≤ (spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j) ⁻¹ᵁ V) (f : Γ(Y.t.G.left, V)) :
    (valR (spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j) V f).snd = fderiv ℂ (fun t => valAt' (e t) V f) 0 wv := by
  obtain ⟨-, -, hg', -, -, -, -, hv⟩ := hK
  have e1 : (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j := by
    rw [hv i]
    congr 2
    exact Fin.ext hij
  rw [← e1] at hV ⊢
  have hU : ⊤ ≤ (x.v i).left ⁻¹ᵁ (φ ⁻¹ᵁ V) := hV
  have hd' := hd (φ ⁻¹ᵁ V) hU ((φ.app V).hom f)
  have e2 : (fun t => valAt' (e t) V f) = fun t => valAt' (u.ex t).left (φ ⁻¹ᵁ V) ((φ.app V).hom f) :=
    funext fun t => by rw [he, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_comp]
  rw [e2, ← hd', GlobalTheory.HolHom.valR_comp, GlobalTheory.HolHom.valR_eq _ _ hU]
  rfl

end Point


open AlgebraicGeometry CategoryTheory Limits in
theorem lie_coords_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U) (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ) (hn : M.n = g) (v' : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) → IsLieBasis v → (Matrix.of z).det ≠ 0 → (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ (Fin.cast hn.symm i)) → (∀ i, IsLieComb (A i) v (v' i)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → ∀ i, (∀ k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)) ∧ ∀ j, Wv (Fin.cast hg.symm i) j = ∑ k, (∑' m : ℕ, PowerSeries.coeff m (A i k) * eTwoPi w ^ m) * z k j := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha M hM e v z hn v' A _ _ _ hχ _ hez hvb hdet hv' hA
  let Ω : Type := {q : ℂ × (Sp ℂ ⟶ Xo.XF c) × ((Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left)) × (Fin g → Fin g → ℂ) //
    q.2.1 ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw q.1) ∧ q.2.1 ≫ pullback.snd _ _ = spMap σ ∧
    (∀ t, q.2.2.1 t ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw q.1) t).left ∧
      q.2.2.1 t ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ) ∧
    ⊤ ≤ (q.2.1 ≫ Y.j) ⁻¹ᵁ M.U ∧ ∀ (hz : ⊤ ≤ (q.2.1 ≫ Y.j) ⁻¹ᵁ M.U) (i : Fin g) (Vo : Y.t.G.left.Opens)
      (f : Γ(Y.t.G.left, Vo)), ⊤ ≤ (spMap (dualMap (ev (q.2.1 ≫ Y.j) M.U hz)) ≫ M.v₀ (Fin.cast hn.symm i)) ⁻¹ᵁ Vo →
      (valR (spMap (dualMap (ev (q.2.1 ≫ Y.j) M.U hz)) ≫ M.v₀ (Fin.cast hn.symm i)) Vo f).snd =
        ∑ k, q.2.2.2 i k * fderiv ℂ (fun t => valAt' (q.2.2.1 t ≫ Y.m.φ) Vo f) 0 (z k)}
  let pw : Ω → ℂ := fun ω => ω.1.1
  let ψ : Ω → (Γ(Y.X, M.U) →+* ℂ) := fun ω => ev (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1
  have hcart := W.m.cart
  have tanv : ∀ k, IsTangent (v k) := hvb.1
  suffices hs : ∀ i k, Cv pw (HahnSeries.ofPowerSeries ℤ ℂ (A i k)) (fun ω => ω.1.2.2.2 i k) by
    obtain ⟨T, hT⟩ := high_iff.1 (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => hs i k)
    refine ⟨T, fun w hw yF h1 h2 hz x φ hK hg u Wv hF hD i => ?_⟩
    choose xF hxF using hF
    have hu : IsUnit (Matrix.of z).det := isUnit_iff_ne_zero.2 hdet
    let Gw : Fin g → Fin g → ℂ := fun i' => Matrix.vecMul (Wv (Fin.cast hg.symm i')) (Matrix.of z)⁻¹
    have hGw : ∀ i' j, Wv (Fin.cast hg.symm i') j = ∑ k, Gw i' k * z k j := fun i' j => by
      have e0 : Matrix.vecMul (Gw i') (Matrix.of z) = Wv (Fin.cast hg.symm i') := by
        simp only [Gw]
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
      rw [← e0]
      simp [Matrix.vecMul, dotProduct]
    have hω : ∀ (hz' : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (i' : Fin g) (Vo : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, Vo)),
        ⊤ ≤ (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) ⁻¹ᵁ Vo →
        (valR (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) Vo f).snd =
          ∑ k, Gw i' k * fderiv ℂ (fun t => valAt' (xF t ≫ Y.m.φ) Vo f) 0 (z k) := by
      intro hz' i' Vo f hV
      rw [point_snd M hK u (fun t => xF t ≫ Y.m.φ) (fun t => (hxF t).2.2.symm) (Fin.cast hg.symm i') (Fin.cast hn.symm i')
        rfl _ (hD _) Vo hV f]
      have e3 : Wv (Fin.cast hg.symm i') = ∑ k, Gw i' k • z k := funext fun j => by
        rw [hGw i' j, Finset.sum_apply]
        simp

      rw [e3, map_sum]
      simp [smul_eq_mul]
    have hT' := hT ⟨(w, yF, xF, Gw), h1, h2, fun t => ⟨(hxF t).1, (hxF t).2.1⟩, hz, hω⟩ hw i
    have hS : ∀ k, SumsAt (A i k) w (Gw i k) := fun k => GlobalTheory.Conv.sumsAt_iff.2 (hT' k)
    refine ⟨fun k => HasSum.summable (hS k), fun j => ?_⟩
    rw [hGw i j]
    exact Finset.sum_congr rfl fun k _ => by rw [HasSum.tsum_eq (hS k)]
  intro i
  obtain ⟨Vo, hVo, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y.t.G.left) (U := ⊤)
    (x := (show Sp (PowerSeries ℂ) ⟶ Y.t.G.left from (η[W.t.G]).left ≫ W.m.φ) (IsLocalRing.closedPoint (PowerSeries ℂ)))
    trivial
  have hVη : ⊤ ≤ ((η[W.t.G]).left ≫ W.m.φ) ⁻¹ᵁ Vo :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (PowerSeries ℂ)) _ hpV).ge
  have hvV : ∀ k, ⊤ ≤ ((v k).left ≫ W.m.φ) ⁻¹ᵁ Vo := fun k => tan_le hcart _ (tanv k) Vo hVη
  have hv'V : ⊤ ≤ ((v' i).left ≫ W.m.φ) ⁻¹ᵁ Vo := tan_le hcart _ (comb_tan v tanv _ _ (hA i)) Vo hVη
  let φL : Γ(Y.X, M.U) →+* ℂ⸨X⸩ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (ev χ M.U hM)
  have eχ : spMap (dualMap φL) ≫ M.v₀ (Fin.cast hn.symm i) =
      spMap (dualMap (HahnSeries.ofPowerSeries ℤ ℂ)) ≫ (v' i).left ≫ W.m.φ := by
    rw [hv' i, dualMap_comp, ← spMap_comp', Category.assoc]
  have hc : ∀ r, Cv pw (φL r) (fun ω => ψ ω r) := by
    intro r
    obtain ⟨T', hT'⟩ := Ha.point M.U r hM
    refine high_iff.2 ⟨T', fun ω hω => ?_⟩
    obtain ⟨-, hs⟩ := hT' _ hω ω.1.2.1 ω.2.1 ω.2.2.1
    have h3 := GlobalTheory.Conv.sumsAt_iff.1 hs
    have e4 : valR χ M.U r = ev χ M.U hM r := valR_eq_ev' χ M.U hM r
    have e5 : valAt' (ω.1.2.1 ≫ Y.j) M.U r = ψ ω r := valR_eq_ev' (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1 r
    rw [e4, e5] at h3
    exact h3
  have hch := fun f => cv_chart (M.v₀ (Fin.cast hn.symm i)) Vo f φL ψ hc (by rw [eχ]; exact le_preimage_comp _ hv'V)
  refine cv_coeff (F := Γ(Y.t.G.left, Vo)) (m := g)
    (A := fun f k => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v k).left ≫ W.m.φ) Vo f).snd)
    (B := fun f => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v' i).left ≫ W.m.φ) Vo f).snd)
    (Aw := fun f k ω => fderiv ℂ (fun t => valAt' (ω.1.2.2.1 t ≫ Y.m.φ) Vo f) 0 (z k))
    (Bw := fun f ω => (valR (spMap (dualMap (ψ ω)) ≫ M.v₀ (Fin.cast hn.symm i)) Vo f).snd)
    (Gw := fun k ω => ω.1.2.2.2 i k)
    (fun f => ?_) (sep_laurent hcart v hvb hVo hVη) (fun f k => ?_) (fun f => ?_) (fun f => ?_)

  · rw [comb_snd hcart v tanv (A i) (v' i) (hA i) Vo hVη f, map_sum]
    exact Finset.sum_congr rfl fun k _ => map_mul _ _ _
  · obtain ⟨T', hT'⟩ := Ha.diff (z k) (e k) (v k) Vo f (hez k).2.1 (hez k).2.2
      (fun n ρ κ vn h1 h2 h3 h4 h5 => (hez k).1 n ρ κ vn h1 h2 h3 h4 (thick_base _ n (v k) ρ vn h1 h5) h5) (hvV k)
    exact high_iff.2 ⟨T', fun ω hω => GlobalTheory.Conv.sumsAt_iff.1 (hT' _ hω _ ω.2.2.2.1)⟩
  · have h1 := (hch f).2
    rw [eχ, GlobalTheory.HolHom.valR_spMap _ _ _ hv'V] at h1
    simpa [dualMap] using h1
  · filter_upwards [(hch f).1] with ω hω
    exact ω.2.2.2.2.2 ω.2.2.2.2.1 i Vo f hω

end GlobalTheory.ArcLieCoord
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.exists_arc_fibre_uniformisation_theta_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_ : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) := by
  first | exact @GlobalTheory.ArcNormal.exists_unif_of_arc | exact GlobalTheory.ArcNormal.exists_unif_of_arc | (intros; apply GlobalTheory.ArcNormal.exists_unif_of_arc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilRepresentationRules_hold : ∀ D : D7, WeilRules D := by
  first | exact @GlobalTheory.Mem.WeilRule.weilRules | exact GlobalTheory.Mem.WeilRule.weilRules | (intros; apply GlobalTheory.Mem.WeilRule.weilRules <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_adelicRowsDivision_over_replacedLaterStages : ∀ (B : Base) (C : Cols B) (a : Late B C) (c : Refill a) (px : PreX B.toPre) (I : ColIn B px) (hX : B.fields.Ok) (T : TwDat B) (Wt : Set B.places.Pl) (ix : C.Tup ≃ I.ι) (p0 : BaseLevelRowSide a.D) (r : RowsAre a.st I hX T Wt ix p0), ∃ r' : RowsAre c.to.st I hX T Wt ix (Tr.baseLevelRowSideTransport c p0), r'.z = GlobalTheory.Mem.R3.Rw.Mv.cpDat c.to c.same r.z ∧ HEq r'.Y.tup r.Y.tup ∧ HEq r'.Y.tupT r.Y.tupT ∧ HEq r'.Y.PY.ψ r.Y.PY.ψ ∧ HEq (fun i => (r'.Y.PW i).ψ) (fun i => (r.Y.PW i).ψ) ∧ HEq (fun π => principalLevelFrame.rowRepR r'.z.R.θ (r'.Y.eFT π)) (fun π => principalLevelFrame.rowRepR r.z.R.θ (r.Y.eFT π)) ∧ HEq (fun x => (r'.Y.Ish.jE x).1) (fun x => (r.Y.Ish.jE x).1) ∧ HEq (fun x => (r'.Y.Iz.jE x).1) (fun x => (r.Y.Iz.jE x).1) ∧ HEq r'.Y.eE r.Y.eE ∧ HEq r'.Y.jA r.Y.jA ∧ HEq r'.Y.jA0 r.Y.jA0 ∧ HEq r'.Y.eMt r.Y.eMt ∧ HEq r'.Y.mj.eW r.Y.mj.eW ∧ HEq r'.Z.jW r.Z.jW ∧ HEq r'.Z.eRR r.Z.eRR ∧ HEq r'.Z.eRR0 r.Z.eRR0 := by
  exact GlobalTheory.Mem.R3.Rw.Mv.rowsAre_refill
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_comparisonData_steps_upTo_rank : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.CertEq.exists_comparisonData_steps_at_baseCharacter | exact GlobalTheory.Mem.Top.KerOne.CertEq.exists_comparisonData_steps_at_baseCharacter | (intros; apply GlobalTheory.Mem.Top.KerOne.CertEq.exists_comparisonData_steps_at_baseCharacter <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.finiteGroupAction_coordinatewise_fieldEmbedding : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → ∀ (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL), (∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) → ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → (z'.R.toRealDat.FW j').ρ g' x' k' = φ ((z.R.toRealDat.FW j).ρ g x k)) := by
  exact @GlobalTheory.Mem.R3.RhoExt.rho_ext
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.furtherPlace_penultimateChart_character_inverseValue : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v x.1 = 1 := by
  first | exact @GlobalTheory.Mem.Col2.QChi.chi_embU_mul_valV | exact GlobalTheory.Mem.Col2.QChi.chi_embU_mul_valV | (intros; apply GlobalTheory.Mem.Col2.QChi.chi_embU_mul_valV <;> assumption)
end
