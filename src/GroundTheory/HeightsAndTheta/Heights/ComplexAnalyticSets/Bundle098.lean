module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle087
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle088
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle079
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle085
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace TubeCollarComparison

theorem contDiffAt_logSq_comp {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (P : MvPolynomial (Fin m) ℂ)
    (x : Fin n → ℂ) (hP : eval (A *ᵥ x) P ≠ 0) :
    ContDiffAt ℝ 2 (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) x := by
  have h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) (A *ᵥ x) :=
    (((TubeFormComparison.analyticAt_eval P _).contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ
  have hv : ContDiffAt ℝ 2 (logAbsSq P) (A *ᵥ x) := h1.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hP))
  have hA : ContDiff ℝ 2 (fun x : Fin n → ℂ => A *ᵥ x) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ
  exact ((hv.comp x hA.contDiffAt).pow 2).div_const 2

theorem abs_maDens_collar_le {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hg : ContDiffAt ℝ 2 g (s y)) {c : ℝ}
    (hb : (hessC g (s y) + (c : ℂ) • 1).PosSemidef ∧ (-hessC g (s y) + (c : ℂ) • 1).PosSemidef) :
    |maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) y| ≤
      3 ^ (d + 1) * c * maDens (fun _ : Fin (d + 1) => euclPot ∘ s) y := by
  set Jc := ReciprocityTheory.AnForm.A.jacC s y with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hH : hessC (g ∘ s) y = Bᴴ * hessC g (s y) * B := by
    rw [hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hg
  have hG : hessC (euclPot ∘ s) y = Bᴴ * B := by
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hE2, TubeFormComparison.hessC_euclPot, hBJ, Matrix.mul_one]
  have hGp : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  set Av : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    fun k => hessC (vecCons g (fun _ => euclPot) k ∘ s) y with hAv
  set a : Fin (d + 1) → ℂ := Fin.cons (c : ℂ) (fun _ => 1) with ha
  set Bv : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun k => a k • (Bᴴ * B) with hBv
  have hle : ∀ k, (Bv k - Av k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, ha, Fin.cons_zero, Matrix.cons_val_zero, hH]
      have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC g (s y) * B = Bᴴ * (-hessC g (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one]
        abel
      rw [e]
      exact hb.2.conjTranspose_mul_mul_same B
    · simp only [hAv, hBv, ha, Fin.cons_succ, Matrix.cons_val_succ, hG, one_smul, sub_self]
      exact Matrix.PosSemidef.zero
  have hge : ∀ k, (Av k + Bv k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, ha, Fin.cons_zero, Matrix.cons_val_zero, hH]
      have e : Bᴴ * hessC g (s y) * B + (c : ℂ) • (Bᴴ * B) = Bᴴ * (hessC g (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [e]
      exact hb.1.conjTranspose_mul_mul_same B
    · simp only [hAv, hBv, ha, Fin.cons_succ, Matrix.cons_val_succ, hG, one_smul]
      exact hGp.add hGp
  have hmain := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le Av Bv hle hge
  have hscale : mdisc Bv = (c : ℂ) * mdisc (fun _ : Fin (d + 1) => hessC (euclPot ∘ s) y) := by
    obtain ⟨L, hL⟩ := (by
      show ∃ F : MultilinearMap (RingHom.id ℂ)
          (fun _ : Fin (d + 1) => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ℂ,
          ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
      refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
        _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
      intro A k c B
      simpa only [RingHom.id_apply, smul_eq_mul] using
        (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
    rw [hG, ← hL, hBv, L.map_smul_univ, smul_eq_mul, Fin.prod_univ_succ]
    simp [ha]
  rw [hscale, Complex.re_ofReal_mul] at hmain
  have hm : ∀ Φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ, maDens Φ y =
      ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * (mdisc fun k => hessC (Φ k) y).re :=
    fun Φ => rfl
  rw [hm, hm, abs_mul]
  have hK0 : 0 ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) := by positivity
  rw [abs_of_nonneg hK0]
  calc ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * |(mdisc Av).re|
      ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * ‖mdisc Av‖ := by
        gcongr
        exact Complex.abs_re_le_norm _
    _ ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) *
        (3 ^ (d + 1) * (c * (mdisc fun _ : Fin (d + 1) => hessC (euclPot ∘ s) y).re)) := by
        gcongr
    _ = _ := by ring

end TubeCollarComparison


open TubeFormComparison TubeCollarComparison in
theorem TubeCollarCompare.proof : TubeCollarCompare.Statement := by
  intro n d J A P R _hJ _hdim hA _hP
  set g : (Fin n → ℂ) → ℝ := fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2 with hgdef
  set U : Set (Fin n → ℂ) := {x | eval (A *ᵥ x) P ≠ 0} with hUdef
  set K : Set (Fin n → ℂ) :=
    Metric.closedBall 0 R ∩ {x | Real.exp (-Real.exp 1) ≤ ‖eval (A *ᵥ x) P‖ ^ 2} with hKdef
  have hcont : Continuous fun x : Fin n → ℂ => eval (A *ᵥ x) P :=
    (MvPolynomial.continuous_eval P).comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).continuous
  have hU : IsOpen U := isOpen_ne_fun hcont continuous_const
  have hK : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const (hcont.norm.pow 2))
  have hKU : K ⊆ U := fun x hx h0 => by
    have h : Real.exp (-Real.exp 1) ≤ ‖eval (A *ᵥ x) P‖ ^ 2 := hx.2
    rw [h0, norm_zero] at h
    linarith [Real.exp_pos (-Real.exp 1), show (0 : ℝ) ^ 2 = 0 by norm_num]
  have hgU : ContDiffOn ℝ 2 g U := fun x hx => (contDiffAt_logSq_comp A P x hx).contDiffWithinAt
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound (fun _ : Fin 1 => g) K hK (fun _ => U) (fun _ => hU)
    (fun _ => hKU) (fun _ => hgU)
  have hC : 0 ≤ (3 : ℝ) ^ (d + 1) * c := by positivity
  refine ⟨3 ^ (d + 1) * c, fun y => ?_⟩
  by_cases hy : y ∈ {y | -Real.exp 1 ≤ logAbsSq P y}
  swap
  · rw [Set.indicator_of_notMem hy]
    exact mul_nonneg hC (finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity)
  rw [Set.indicator_of_mem hy]
  unfold tubeDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', hsec, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  set f := (Metric.closedBall (0 : Fin n → ℂ) R).indicator fun x => tubeWeight P (A *ᵥ x) with hfdef
  by_cases hf : f x = 0
  · rw [hf, zero_mul, abs_zero]
    exact mul_nonneg hC (abs_nonneg _)
  have hxB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
    by_contra h
    exact hf (Set.indicator_of_notMem h _)
  have hv1 : logAbsSq P (A *ᵥ x) ≤ -1 := by
    by_contra h
    exact hf (by simp [hfdef, Set.indicator_of_mem hxB, tubeWeight, h])
  have hP : eval (A *ᵥ x) P ≠ 0 := by
    intro h0
    simp [logAbsSq, h0] at hv1
    linarith
  have hxK : x ∈ K := by
    refine ⟨hxB, ?_⟩
    have h2 : 0 < ‖eval (A *ᵥ x) P‖ ^ 2 := by positivity
    have h3 := Real.exp_le_exp.2 (show -Real.exp 1 ≤ logAbsSq P (A *ᵥ x) from hy)
    rwa [logAbsSq, Real.exp_log h2] at h3
  have hw : |f x| ≤ 1 := by
    rw [hfdef, Set.indicator_of_mem hxB]
    simp only [tubeWeight, if_pos hv1]
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hg2 : ContDiffAt ℝ 2 g (s (A *ᵥ x)) := by
    rw [hsx']
    exact contDiffAt_logSq_comp A P x hP
  have hbx := hb 0 (s (A *ᵥ x)) (by rw [hsx']; exact hxK)
  have key := abs_maDens_collar_le g s (A *ᵥ x) hsa hg2 hbx
  rw [abs_mul, abs_mul, Set.indicator_of_mem hxB, abs_one, one_mul]
  calc |f x| * |maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) (A *ᵥ x)|
      ≤ 1 * (3 ^ (d + 1) * c * maDens (fun _ : Fin (d + 1) => euclPot ∘ s) (A *ᵥ x)) :=
        mul_le_mul hw key (abs_nonneg _) zero_le_one
    _ ≤ 3 ^ (d + 1) * c * |maDens (fun k => (fun _ : Fin (d + 1) => euclPot) k ∘ s) (A *ᵥ x)| := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) hC

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

theorem measurable_poincareDeepWeight : Measurable poincareDeepWeight := by
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact Measurable.ite (measurableSet_lt hn.log measurable_const) (hn.mul (hn.log.pow_const 2)).inv
    measurable_const

theorem tubeDeep_term (hR : TubeDeepRankOne.Statement) {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} {P : MvPolynomial (Fin (d + 1)) ℂ} {R : ℝ} {y : Fin (d + 1) → ℂ}
    {x : Fin n → ℂ} {s : (Fin (d + 1) → ℂ) → Fin n → ℂ} (hx : x ∈ fibre J A y) (hs : IsSheetAt J A x s)
    (hy : logAbsSq P y < -Real.exp 1) :
    |(Metric.closedBall 0 R).indicator (fun x => tubeWeight P (A *ᵥ x)) x *
        ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y| =
      (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 *
          ((2 / Real.pi) ^ (d + 1) * poincareDeepWeight (deepMap P s I y 0)) := by
  obtain ⟨U, hU, hxU, hsd, -, hsec, -⟩ := hs
  have hAx : A *ᵥ x = y := hx.2
  rw [hAx] at hxU
  have hP : eval y P ≠ 0 := by
    intro h0
    simp only [logAbsSq, h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Real.log_zero] at hy
    linarith [Real.exp_pos 1]
  rw [hR n d A P U s y hU hxU hsd (fun y' hy' => (hsec y' hy').1) hP]
  have hw : ∀ I : Fin d → Fin n,
      poincareDeepWeight (deepMap P s I y 0) = (‖eval y P‖ ^ 2 * logAbsSq P y ^ 2)⁻¹ := by
    intro I
    simp only [deepMap, Matrix.cons_val_zero, poincareDeepWeight]
    exact if_pos hy
  have ht : tubeWeight P y = (logAbsSq P y ^ 2)⁻¹ :=
    if_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  simp only [hw]
  by_cases hxR : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
  · rw [Set.indicator_of_mem hxR, Set.indicator_of_mem hxR, hAx, ht, one_mul]
    have hp : 0 < ‖eval y P‖ := norm_pos_iff.2 hP
    have hl : logAbsSq P y ≠ 0 := by linarith [Real.exp_pos 1]
    rw [abs_of_nonneg (by positivity), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    field_simp
  · simp [Set.indicator_of_notMem hxR]

theorem TubeDeepMass.proof (hR : TubeDeepRankOne.Statement) (hC : TubeDeepAreaCount.Statement)
    (hW : TubeDeepWeightMass.Statement) : TubeDeepMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hc0 : 0 ≤ (2 / Real.pi) ^ (d + 1) := by positivity
  set g : (Fin (d + 1) → ℂ) → ℝ := fun z => (2 / Real.pi) ^ (d + 1) * poincareDeepWeight (z 0) with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z =>
    mul_nonneg hc0 (by unfold poincareDeepWeight; split_ifs <;> positivity)
  have hgm : Measurable g :=
    measurable_const.mul (measurable_poincareDeepWeight.comp (measurable_pi_apply 0))
  have hl : Measurable (logAbsSq P) :=
    ((continuous_norm.comp (MvPolynomial.continuous_eval P)).pow 2).measurable.log
  have hF : ∀ y, {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y =
      sheetSum J A (fun x s => (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y := by
    intro y
    by_cases hy : logAbsSq P y < -Real.exp 1
    · rw [Set.indicator_of_mem (show y ∈ {y | logAbsSq P y < -Real.exp 1} from hy), tubeDens, chartAbsDens, sheetSum, sheetSum]
      refine finsum_congr fun x => finsum_congr fun hx => ?_
      split_ifs with h
      · exact tubeDeep_term hR hx h.choose_spec hy
      · rfl
    · rw [Set.indicator_of_notMem (show y ∉ {y | logAbsSq P y < -Real.exp 1} from hy)]
      have hw0 : ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (I : Fin d → Fin n), g (deepMap P s I y) = 0 := by
        intro s I
        simp only [hg, deepMap, Matrix.cons_val_zero, poincareDeepWeight]
        exact mul_eq_zero_of_right _ (if_neg hy)
      simp [sheetSum, hw0]
  obtain ⟨N, hN⟩ := hC n d J A P R hJ hdim hA
  refine ⟨((measurable_tubeDens hA P R _).indicator (measurableSet_lt hl measurable_const)).aestronglyMeasurable,
    ?_⟩
  have hnn : ∀ y, 0 ≤ {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y :=
    fun y => Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y
  show ∫⁻ y, ‖{y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y‖ₑ < ⊤
  calc _ = ∫⁻ y, ENNReal.ofReal (sheetSum J A (fun x s =>
          (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
            ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y) :=
        lintegral_congr fun y => by rw [Real.enorm_eq_ofReal (hnn y), hF y]
    _ ≤ (N : ℝ≥0∞) * ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (g z) :=
        hN g hgm hg0
    _ = (N : ℝ≥0∞) * (ENNReal.ofReal ((2 / Real.pi) ^ (d + 1)) *
          ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R},
            ENNReal.ofReal (poincareDeepWeight (z 0))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact congrArg _ (lintegral_congr fun z => ENNReal.ofReal_mul hc0)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top N)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hW d R))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegLelongMono

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_annulus_nonneg (hL : RegLogDensNonneg.Statement) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → ℂ) {r s : ℝ} (hr : 0 < r) (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => logDistSq x) y := by
  unfold chartDens sheetSum
  refine finsum_nonneg fun z => finsum_nonneg fun hz => ?_
  split_ifs with h
  · beta_reduce
    by_cases hza : z ∈ euclBall x s \ euclBall x r
    · rw [Set.indicator_of_mem hza, one_mul]
      have := hL n d J A u ε x z h.choose hε (ne_of_mem_euclBall_diff hr hza) h.choose_spec
      rwa [hz.2] at this
    · rw [Set.indicator_of_notMem hza, zero_mul]
  · exact le_rfl

end RegLelongMono


open RegLelongMono in
theorem RegLelongMono.proof (hA : RegLelongAnnulus.Statement) (hL : RegLogDensNonneg.Statement) :
    RegLelongMono.Statement := by
  intro n d J A u ε x r s hJ hdim hAf hε hr hrs
  have heq := hA n d J A u ε x r s hJ hdim hAf hε hr hrs
  have hτ : 0 ≤ ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => logDistSq x) y :=
    integral_nonneg fun y => chartDens_annulus_nonneg hL u hε x hr y
  have hrs0 : 0 ≤ r ^ (2 * d) * s ^ (2 * d) :=
    mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (hr.le.trans hrs) _)
  have := mul_nonneg hrs0 hτ
  linarith

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem NormalCurvePointDVR.proof : NormalCurvePointDVR.Statement := by
  intro σ _ I w hI hic hdim hw
  have : I.IsPrime := hI
  let m : Ideal (MvPolynomial σ ℂ) := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  let S := Localization.AtPrime m
  let T := S ⧸ I.map (algebraMap (MvPolynomial σ ℂ) S)
  let A := MvPolynomial σ ℂ ⧸ I
  have hIm : I ≤ m := fun f hf ↦ RingHom.mem_ker.2 (hw f hf)
  let P : Ideal A := m.map (Ideal.Quotient.mk I)
  have hmem : ∀ f, Ideal.Quotient.mk I f ∈ P ↔ f ∈ m := fun f ↦ Ideal.mem_quotient_iff_mem hIm
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIm)

  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 (by rw [hdim])
  have : Ring.DimensionLEOne A := ⟨fun hp0 hp ↦ hp.isMaximal_of_ne_bot hp0⟩
  have : IsDedekindRing A := { toIsIntegralClosure := hic }

  have hP0 : P ≠ ⊥ := by
    intro h0
    have hmI : m ≤ I := fun f hf ↦ by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h0]
      exact (hmem f).2 hf
    have hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun z ↦ ⟨C z, by simp⟩)
    have hfield : IsField A := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).1 (le_antisymm hIm hmI ▸ hmax)
    have := ringKrullDim_eq_zero_of_isField hfield
    rw [hdim] at this
    exact_mod_cast this

  have hsub : Algebra.algebraMapSubmonoid A m.primeCompl = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact fun h ↦ hf ((hmem f).1 h)
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨f, fun h ↦ hx ((hmem f).2 h), rfl⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid A m.primeCompl) T := inferInstance
  have hlocP : IsLocalization.AtPrime T P := by
    change IsLocalization P.primeCompl T
    rw [← hsub]
    exact hloc
  have hdom : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T (M := P.primeCompl)
    P.primeCompl_le_nonZeroDivisors
  exact ⟨hdom, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 T⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem PlaceBranchExists.proof (h₁ : PlaceOnComponent.Statement) (h₂ : PrimePlaceBranchExists.Statement) :
    PlaceBranchExists.Statement := by
  intro n I q hrad hdim P
  obtain ⟨J, hJ, -, hdimJ, P', hP'⟩ := h₁ n I q hrad hdim P
  obtain ⟨ν, hν⟩ := h₂ n J q hJ.1.1 hdimJ P'

  let ν' : VarBranch I 1 q :=
    { radius := ν.radius, radius_pos := ν.radius_pos, toFun := ν.toFun, differentiableOn := ν.differentiableOn,
      injOn := ν.injOn, map_zero := ν.map_zero,
      mapsTo := fun t ht g hg ↦ ν.mapsTo ht g (hJ.1.2 hg) }
  have hord : ∀ f, branchOrder ν' f = branchOrder ν f := fun _ ↦ rfl
  exact ⟨ν', fun f ↦ (hP' f).trans ((hν f).trans (hord f).symm)⟩

end GroundTheory.Heights₂.Heights
end
