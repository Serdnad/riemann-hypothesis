module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle434
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Mathlib.Algebra.Order.Chebyshev
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem _root_.GlobalTheory.T.torusElementConjugatedByFrame_mem_specialUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ), torusGL hx θ ∈ realSU X.Ψ X.Gm := by
  first | exact @GlobalTheory.TorusFrame.torusGL_mem_realSU | exact GlobalTheory.TorusFrame.torusGL_mem_realSU | (intros; apply GlobalTheory.TorusFrame.torusGL_mem_realSU <;> assumption)
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem _root_.GlobalTheory.T.torusTangent_mem_specialUnitaryLie_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∀ θ : X.Ψ → Fin (r - 1) → ℝ, torusDer x θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (torusDer x θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0 := by
  first | exact @GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame | exact GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame | (intros; apply GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

theorem _root_.GlobalTheory.T.exists_whittakerBumpArchimedeanFactor_one_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧ bumpInf f (oneL E n) ≠ 0 := by
  first | exact @GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero | exact GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero | (intros; apply GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

theorem sum_norm_mulVec_sq_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (c : ℝ)
    (h : ∀ i j, ‖M i j‖ ≤ c) (w : Fin n → ℂ) :
    ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ ((m : ℝ) * n * c ^ 2) * ∑ j, ‖w j‖ ^ 2 := by
  have hi : ∀ i, ‖(M *ᵥ w) i‖ ≤ c * ∑ j, ‖w j‖ := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    calc ‖∑ j, M i j * w j‖ ≤ ∑ j, ‖M i j * w j‖ := norm_sum_le _ _
      _ ≤ ∑ j, c * ‖w j‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)
      _ = c * ∑ j, ‖w j‖ := by rw [Finset.mul_sum]
  have hs : (∑ j, ‖w j‖) ^ 2 ≤ n * ∑ j, ‖w j‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖w j‖)
  have hi2 : ∀ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c ^ 2 * (n * ∑ j, ‖w j‖ ^ 2) := fun i => by
    calc ‖(M *ᵥ w) i‖ ^ 2 ≤ (c * ∑ j, ‖w j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hi i) 2
      _ = c ^ 2 * (∑ j, ‖w j‖) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg c)
  calc ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ ∑ _i : Fin m, c ^ 2 * (n * ∑ j, ‖w j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hi2 i
    _ = _ := by simp [Finset.sum_const]; ring

theorem sqrt_sum_norm_sq_eq {n : ℕ} (x : Fin n → ℂ) :
    Real.sqrt (∑ i, ‖x i‖ ^ 2) = ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq]

theorem norm_toLp_mulVec_le {m n r : ℕ} (hm : m ≤ r) (hn : n ≤ r) (M : Matrix (Fin m) (Fin n) ℂ)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ i j, ‖M i j‖ ≤ c) (w : Fin n → ℂ) :
    ‖WithLp.toLp 2 (M *ᵥ w)‖ ≤ (r * c) * ‖WithLp.toLp 2 w‖ := by
  rw [← sqrt_sum_norm_sq_eq, ← sqrt_sum_norm_sq_eq]
  have hmn : (m : ℝ) * n * c ^ 2 ≤ ((r : ℝ) * c) ^ 2 := by
    have h1 : (m : ℝ) ≤ r := by exact_mod_cast hm
    have h2 : (n : ℝ) ≤ r := by exact_mod_cast hn
    have : (m : ℝ) * n ≤ (r : ℝ) * r :=
      mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith [sq_nonneg c]
  have hS := sum_norm_mulVec_sq_le M c h w
  have hB : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc Real.sqrt (∑ i, ‖(M *ᵥ w) i‖ ^ 2) ≤ Real.sqrt (((r : ℝ) * c) ^ 2 * ∑ j, ‖w j‖ ^ 2) :=
        Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_right hmn hB))
    _ = (r * c) * Real.sqrt (∑ j, ‖w j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hc)]

end GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_coord_le (X : Data E r) (z : V (nd X)) (k : Fin (nd X)) : ‖z k‖ ≤ ‖z‖ :=
  PiLp.norm_apply_le z k

theorem norm_chartMatrixTopBlock_sub_one_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i j : Fin X.p0) :
    ‖(chartMatrixTopBlock X z τ - 1) i j‖ ≤ ‖z‖ := by
  simp only [chartMatrixTopBlock, Matrix.sub_apply, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat,
    Matrix.one_apply]
  split_ifs
  all_goals first
    | (rw [sub_zero]; exact norm_coord_le X z _)
    | (rw [sub_self, norm_zero]; exact norm_nonneg _)
    | (exfalso; simp only [Fin.lt_def, Fin.ext_iff, Fin.coe_castLE] at *; omega)

theorem norm_chartBottomLeftBlock_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i : Fin (r - X.p0)) (j : Fin X.p0) :
    ‖chartBottomLeftBlock X z τ i j‖ ≤ ‖z‖ := by
  simp only [chartBottomLeftBlock, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat]
  split_ifs with h1 h2
  · exact norm_coord_le X z _
  · exact absurd h2 (by intro h; have := congrArg Fin.val h; simp at this; omega)
  · exact absurd (show Fin.castLE X.p0_le j < ⟨X.p0 + i, by have := i.isLt; have := X.p0_le; omega⟩ from
      by rw [Fin.lt_def]; simp; omega) h1

end GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

theorem zN_graphCoord_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → X.zN (graphCoord X z) ≤ 1 / 50 := by
  intro E _ _ _ r X z hz
  have hε : 0 ≤ ‖z‖ := norm_nonneg z
  have hrε : (r : ℝ) * ‖z‖ ≤ 1 / 100 := by
    rcases Nat.eq_zero_or_pos r with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast h
      nlinarith
  apply Real.iSup_le _ (by norm_num)
  intro τ
  apply Real.sSup_le _ (by norm_num)
  rintro t ⟨v, hv, rfl⟩
  have hunit : IsUnit (chartMatrixTopBlock X z τ).det := by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one
  have hAv : Matrix.of (graphCoord X z τ) *ᵥ v = chartBottomLeftBlock X z τ *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) := by
    change (chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹) *ᵥ v = _
    exact (Matrix.mulVec_mulVec _ _ _).symm
  have hvw : v = (chartMatrixTopBlock X z τ)⁻¹ *ᵥ v + (chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
    abel
  have h1 := norm_toLp_mulVec_le (Nat.sub_le r X.p0) X.p0_le (chartBottomLeftBlock X z τ) ‖z‖ hε
    (norm_chartBottomLeftBlock_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)
  have h2 := norm_toLp_mulVec_le X.p0_le X.p0_le (chartMatrixTopBlock X z τ - 1) ‖z‖ hε
    (norm_chartMatrixTopBlock_sub_one_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)
  have h3 : ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)‖ ≤ ‖WithLp.toLp 2 v‖ +
      ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))‖ := by
    have hv' : WithLp.toLp 2 v = WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) +
        WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)) := by
      rw [← WithLp.toLp_add, ← hvw]
    have : WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) = WithLp.toLp 2 v -
        WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)) := by
      rw [hv', add_sub_cancel_right]
    rw [this]
    exact norm_sub_le _ _
  have hvpos : 0 < ‖WithLp.toLp 2 v‖ :=
    norm_pos_iff.mpr fun h => hv (by simpa using congrArg WithLp.ofLp h)
  rw [sqrt_sum_norm_sq_eq, sqrt_sum_norm_sq_eq, hAv, div_le_iff₀ hvpos]
  have hb := norm_nonneg (WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))
  have h4 := mul_le_mul_of_nonneg_right hrε hb
  linarith

end GlobalTheory.ChartGraph
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

theorem _root_.GlobalTheory.T.chart_firstColumns_eq_graph_times_topBlock : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (z : V (nd X)) (τ : X.Ψ), (chartMatrixTopBlock X z τ).det = 1 ∧ ∀ a : Fin X.p0,
    col (mat (cpt X x z) τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a • col (mat (X.xZ x (graphCoord X z)) τ) (Fin.castLE X.p0_le c) := by
  first | exact @GlobalTheory.ChartGraph.cols_graph | exact GlobalTheory.ChartGraph.cols_graph | (intros; apply GlobalTheory.ChartGraph.cols_graph <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel

theorem _root_.GlobalTheory.T.exists_fullSymplecticLevelStructure_of_tateIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    {z : kˣ}, IsPrimitiveRoot z l.M' → z ^ (l.M' / l.A) = I.ζ l.A →
    ∃ ev : D.La → Q, IsSympLevel D act e l.M' z ev ∧ Induces l (I.ev l.A) (I.ev l.M) ev := by
  first | exact @GlobalTheory.FullLevel.exists_sympLevel_of_tate | exact GlobalTheory.FullLevel.exists_sympLevel_of_tate | (intros; apply GlobalTheory.FullLevel.exists_sympLevel_of_tate <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.mem_fullLevelGroup_iff_congruence_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (r : ℕ) (Y : Data E r), GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsSelfDualTr Y → ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧ ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M' • y := by
  first | exact @GlobalTheory.EqCovol.mem_iff_congr_lcm | exact GlobalTheory.EqCovol.mem_iff_congr_lcm | (intros; apply GlobalTheory.EqCovol.mem_iff_congr_lcm <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel

theorem _root_.GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop},
    (∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c') →
    ∀ {z : kˣ}, IsPrimitiveRoot z l.M' → ∀ {etaA eta ev ev' : D.La → Q},
    IsSympLevel D act e l.M' z ev → Induces l etaA eta ev →
    IsSympLevel D act e l.M' z ev' → Induces l etaA eta ev' → ev = ev' := by
  first | exact @GlobalTheory.FullLevel.isSympLevel_unique | exact GlobalTheory.FullLevel.isSympLevel_unique | (intros; apply GlobalTheory.FullLevel.isSympLevel_unique <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.LieIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def skewSub (G : Matrix (Fin r) (Fin r) E) : Submodule (maximalRealSubfield E) (Matrix (Fin r) (Fin r) E) where
  carrier := {X | X.trace = 0 ∧ ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0}
  zero_mem' := ⟨by simp, by simp [herm, cc]⟩
  add_mem' {X Y} hX hY := by
    refine ⟨by rw [trace_add, hX.1, hY.1, add_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    have h2 := hY.2 u w
    simp only [herm, cc, add_mulVec, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2
  smul_mem' c X hX := by
    have hc : IsCMField.complexConj E (c : E) = c := IsCMField.complexConj_apply_eq_self E c
    have e : c • X = (c : E) • X := rfl
    refine ⟨by rw [e, trace_smul, hX.1, smul_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    rw [e]
    simp only [herm, cc, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hc] at h1 ⊢
    have e1 : ∀ a b, ((c : E) * (X *ᵥ u) a) * G a b * (IsCMField.complexConj E) (w b) =
        (c : E) * ((X *ᵥ u) a * G a b * (IsCMField.complexConj E) (w b)) := fun a b => by ring
    have e2 : ∀ a b, u a * G a b * ((c : E) * (IsCMField.complexConj E) ((X *ᵥ w) b)) =
        (c : E) * (u a * G a b * (IsCMField.complexConj E) ((X *ᵥ w) b)) := fun a b => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    rw [← mul_add, h1, mul_zero]

def trForm (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0) :
    LinearMap.BilinForm (maximalRealSubfield E) (skewSub G) :=
  LinearMap.mk₂ (maximalRealSubfield E)
    (fun X Y => ⟨(X.1 * Y.1).trace, GlobalTheory.T.trace_product_skew_hermitian_real E r G X.1 Y.1 hG hd X.2.2 Y.2.2⟩)
    (fun X₁ X₂ Y => Subtype.ext (by simp [add_mul, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))
    (fun X Y₁ Y₂ => Subtype.ext (by simp [mul_add, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))

theorem trForm_apply (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (X Y : skewSub G) : ((trForm G hG hd X Y : maximalRealSubfield E) : E) = (X.1 * Y.1).trace := rfl

theorem norm_algebraMap_real (d : maximalRealSubfield E) :
    Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E d) = (Algebra.norm ℚ d) ^ 2 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := maximalRealSubfield E), Algebra.norm_algebraMap,
    Algebra.IsQuadraticExtension.finrank_eq_two, map_pow]

theorem isIntegral_coe_iff (x : maximalRealSubfield E) : IsIntegral ℤ (x : E) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E).toRingHom.injective

theorem abs_norm_gram_eq_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → SelfDualLat G Λ → (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e → |((Algebra.norm ℚ (Matrix.of fun i j => Matrix.trace (e i * e j)).det : ℚ) : ℝ)| = (((lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) : ℝ) * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2) ^ 2 := by
  intro E _ _ _ r G Λ e hr hΛ he hli
  obtain ⟨hG, hd, hfg, hsp, -⟩ := hΛ
  have heV : ∀ i, e i ∈ skewSub G := fun i => ⟨(he i).1, (he i).2.1⟩
  set v : Fin (r ^ 2 - 1) → skewSub G := fun i => ⟨e i, heV i⟩ with hv_def
  have hve : (skewSub G).subtype ∘ v = e := rfl
  have hvli : LinearIndependent (maximalRealSubfield E) v :=
    LinearIndependent.of_comp (skewSub G).subtype (by rw [hve]; exact hli)
  have hmapv : Submodule.map (skewSub G).subtype (Submodule.span (maximalRealSubfield E) (Set.range v)) =
      Submodule.span _ (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp, hve]
  have hspan : ⊤ ≤ Submodule.span (maximalRealSubfield E) (Set.range v) := by
    rintro ⟨X, hX⟩ -
    have h := GlobalTheory.T.lie_basis_spans_unitary_lie E r G e hG hd heV hli X hX.1 hX.2
    rw [← hmapv] at h
    obtain ⟨y, hy, hyX⟩ := h
    have : y = ⟨X, hX⟩ := Subtype.ext hyX
    rwa [← this]
  set b := Module.Basis.mk hvli hspan with hb
  have hbv : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hvli hspan i
  set B := trForm G hG hd with hB
  set f : skewSub G →+ Matrix (Fin r) (Fin r) E := (skewSub G).subtype.toAddMonoidHom with hf_def
  have hf : Function.Injective f := Subtype.val_injective
  set L' := (lieLat G Λ).comap f with hL'
  have hLrange : lieLat G Λ ≤ f.range := fun X hX => ⟨⟨X, hX.1, hX.2.1⟩, rfl⟩
  have hLmap : L'.map f = lieLat G Λ := AddSubgroup.map_comap_eq_self hLrange
  have hsymm : B.IsSymm := ⟨fun x y => Subtype.ext (by rw [hB, trForm_apply, trForm_apply]; exact Matrix.trace_mul_comm _ _)⟩
  have hsep : ∀ X : skewSub G, (∀ Y : skewSub G, B X Y = 0) → X = 0 := by
    intro X hX
    apply Subtype.ext
    refine GlobalTheory.T.eq_zero_of_trace_form_skew_hermitian E r G X.1 hG hd X.2.1 X.2.2 fun Y hY1 hY2 => ?_
    have := congrArg (fun z : maximalRealSubfield E => (z : E)) (hX ⟨Y, hY1, hY2⟩)
    simpa [hB, trForm_apply] using this
  have hnd : B.Nondegenerate := ⟨fun X hX => hsep X hX, fun Y hY => hsep Y fun X => by rw [hsymm.eq]; exact hY X⟩
  have hbL : ∀ i, b i ∈ L' := fun i => by rw [hbv]; exact he i
  have hsm : ∀ (a : 𝓞 (maximalRealSubfield E)) x, x ∈ L' → a • x ∈ L' := by
    intro a x hx
    refine ⟨(a • x).2.1, (a • x).2.2, fun y hy => ?_⟩
    have hc : IsIntegral ℤ (((a : maximalRealSubfield E) : E)) := (isIntegral_coe_iff _).2 a.isIntegral_coe
    have e1 : (f (a • x)) = (((a : maximalRealSubfield E) : E)) • x.1 := rfl
    rw [e1, smul_mulVec]
    have e2 : (((a : maximalRealSubfield E) : E)) • (x.1 *ᵥ y) = (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) • (x.1 *ᵥ y) := by
      rw [← algebraMap_smul E (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) (x.1 *ᵥ y)]; rfl
    rw [e2]
    exact Λ.smul_mem _ (hx.2.2 y hy)
  have hint : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (B x y) := by
    intro x hx y hy
    rw [← isIntegral_coe_iff, hB, trForm_apply]
    refine GlobalTheory.T.trace_integral_of_preserved_lattice E r Λ _ hfg hsp fun z hz => ?_
    rw [← mulVec_mulVec]
    exact hx.2.2 _ (hy.2.2 z hz)
  have key := GlobalTheory.T.norm_gram_det_eq_index (maximalRealSubfield E) (skewSub G) (r ^ 2 - 1) b B L' hsymm hnd hbL hsm hint
  have hdet : (Matrix.of fun i j => Matrix.trace (e i * e j)).det =
      algebraMap (maximalRealSubfield E) E (Matrix.of fun i j => B (b i) (b j)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hbv]
    rfl
  have I1 : (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) =
      L'.relIndex (AddSubgroup.closure {y | ∀ x ∈ L', IsIntegral ℤ (B x y)}) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap, AddMonoidHom.map_closure]
    congr 2
    ext Y
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨Y, h1, h2⟩, fun x hx => ?_, rfl⟩
      rw [← isIntegral_coe_iff, hB, trForm_apply]
      exact h3 _ hx
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2.1, y.2.2, fun X hX => ?_⟩
      have := hy ⟨X, hX.1, hX.2.1⟩ hX
      rw [← isIntegral_coe_iff, hB, trForm_apply] at this
      exact this
  have I2 : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) =
      (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).toAddSubgroup.relIndex L' := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap]
    congr 1
    let g : skewSub G →ₗ[𝓞 (maximalRealSubfield E)] Matrix (Fin r) (Fin r) E :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).map g =
        Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      simp [g, hbv, v]
    rw [← hg, Submodule.map_toAddSubgroup]
    rfl
  rw [hdet, norm_algebraMap_real, I1, I2, ← key]
  push_cast
  rw [abs_pow, sq_abs]

end GlobalTheory.LieIndex
end

section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.OriginBox

section Entries
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

theorem stepPt_var (x₀ : Matrix n n' k) (e : StepVar n c n' → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) (hb : basePt c x₀ r s = 0) : stepPt x₀ e r s = e ⟨(r, s), h⟩ := by
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply, hb, zero_add, dif_pos h]

theorem basePt_inr_succ (x₀ : Matrix n n' k) (i : Fin c) : basePt c x₀ (.inr i) (.inr i.succ) = 0 := by
  simp [basePt]

theorem basePt_inl_inr (x₀ : Matrix n n' k) (r : n) (i : Fin (c + 1)) : basePt c x₀ (.inl r) (.inr i) = 0 := by
  simp [basePt]

theorem basePt_inr_inl (x₀ : Matrix n n' k) (l : Fin c) (s : n') : basePt c x₀ (.inr l) (.inl s) = 0 := by
  simp [basePt]

end Entries

section Main
variable {k : Type} [Field k] [ValuativeRel k]

theorem phase_origin_le (G : Grid k) (ϖ : kˣ) (a a' : ℤ) (e : Vars G) (he : e ∈ box G ϖ a a') :
    valuation k (phase (0 : ColArgs G) e) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
  have hbox : ∀ j v {A : ℤ}, boxExp G a a' j v = A → valuation k (e j v) ≤ valuation k ((ϖ ^ A : kˣ) : k) :=
    fun j v A hA => hA ▸ he j (Set.mem_univ j) v (Set.mem_univ v)
  have hmul : ∀ {x y : k} {A B : ℤ}, valuation k x ≤ valuation k ((ϖ ^ A : kˣ) : k) →
      valuation k y ≤ valuation k ((ϖ ^ B : kˣ) : k) → A + B = a + a' →
      valuation k (x * y) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
    intro x y A B hx hy hAB
    rw [← hAB, _root_.zpow_add, Units.val_mul, map_mul, map_mul]
    exact mul_le_mul' hx hy
  unfold phase
  refine Valuation.map_sum_le _ fun j _ => Valuation.map_add_le _ ?_ ?_
  · unfold ch
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [stepPt_var _ _ (Or.inl (by simp [Free])) (basePt_inr_succ _ i)]
    refine hbox _ _ ?_
    simp only [boxExp, auxiliaryVectorUniformizerExponent, Fin.val_succ]
    push_cast
    ring
  · split_ifs with hc
    · refine Valuation.map_sum_le _ fun r _ => ?_
      unfold rowVar
      split_ifs with h
      · rw [Finset.sum_mul]
        refine Valuation.map_sum_le _ fun l _ => ?_
        split_ifs with hl
        · have hc' : Odd (G.m - 2 - (j + 1)) := by
            obtain ⟨q, hq⟩ := hc
            exact ⟨q - 1, by omega⟩
          unfold colVar
          rw [stepPt_var (c := G.m - 2 - (j + 1)) (r := .inr l) (s := .inl r) _ _ (Or.inr ⟨hc', hl⟩) (basePt_inr_inl _ l r),
            stepPt_var (c := G.m - 2 - j) (r := .inl r) (s := .inr ⟨(G.m - 2 - j) / 2, by omega⟩) _ _ (Or.inr ⟨hc, rfl⟩) (basePt_inl_inr _ r _)]
          refine hmul (hbox _ _ rfl) (hbox _ _ rfl) ?_
          obtain ⟨q, hq⟩ := hc
          have h1 : (G.m - 2 - (j + 1) : ℕ) = q + q - 1 := by omega
          have h2 : (l : ℕ) + 1 = q := by omega
          have h3 : (G.m - 2 - j) / 2 = q := by omega
          have h4 : (((q + q - 1 : ℕ)) : ℤ) = 2 * (q : ℤ) - 1 := by omega
          have h5 : ((l : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
          simp only [boxExp, auxiliaryVectorUniformizerExponent]
          rw [h5, h3, hq, h1, h4]
          push_cast
          ring
        · simp
      · simp
    · simp

end Main
end GlobalTheory.OriginBox
end
