module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticGermsNoetherian
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

open scoped ENNReal

noncomputable section

theorem measurable_sheetJac {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) : Measurable (sheetJac s) := by
  let C₁ : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap
  let C₂ : EuclideanSpace ℂ (Fin d) →L[ℝ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap
  have hΦ : Continuous fun M : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => C₁.comp (M.comp C₂) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have h : sheetJac s = (fun M : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n) =>
      areaJacobian (M : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) ∘
      (fun M : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => C₁.comp (M.comp C₂)) ∘ fderiv ℝ s := by
    funext y
    rfl
  rw [h]
  exact (continuous_areaJacobian.comp hΦ).measurable.comp (measurable_fderiv ℝ s)

theorem SheetImageArea.proof (h : SheetImageAreaSet.Statement) : SheetImageArea.Statement := by
  classical
  intro n d A U s hU hs hA B hB hBU g hg
  let U' : Set (EuclideanSpace ℂ (Fin d)) := WithLp.ofLp ⁻¹' U
  let T : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := fun y => WithLp.toLp 2 (s (WithLp.ofLp y))
  let T' := U'.piecewise T (fun _ => 0)
  have hU' : IsOpen U' := hU.preimage (PiLp.continuous_ofLp 2 _)
  have hT : ContinuousOn T U' :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (hs.continuousOn.comp (PiLp.continuous_ofLp 2 _).continuousOn fun _ hy => hy)
  have hT'm : Measurable T' := hT.measurable_piecewise continuousOn_const hU'.measurableSet
  have hEq : ∀ y ∈ B, T' y = T y := fun y hy => Set.piecewise_eq_of_mem _ _ _ (hBU y hy)
  have hJ : Measurable fun y : EuclideanSpace ℂ (Fin d) => ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) :=
    ENNReal.measurable_ofReal.comp ((measurable_sheetJac s).comp (PiLp.continuous_ofLp 2 _).measurable)
  let ρ := (μH[((2 * d : ℕ) : ℝ)].restrict B).withDensity
    fun y : EuclideanSpace ℂ (Fin d) => ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
  have hmap : ρ.map T' = (μH[((2 * d : ℕ) : ℝ)]).restrict (T '' B) := by
    ext S hS
    have hpre : MeasurableSet (T' ⁻¹' S) := hT'm hS
    rw [Measure.map_apply hT'm hS, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
      Measure.restrict_apply hS,
      ← h n d A U s hU hs hA _ (hpre.inter hB) fun y hy => hBU y hy.2]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hyB⟩, rfl⟩
      exact ⟨by simpa [Set.mem_preimage, hEq y hyB] using hyS, y, hyB, rfl⟩
    · rintro ⟨hzS, y, hyB, rfl⟩
      exact ⟨y, ⟨by simpa [Set.mem_preimage, hEq y hyB] using hzS, hyB⟩, rfl⟩
  calc ∫⁻ y in B, g (WithLp.toLp 2 (s (WithLp.ofLp y))) * ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
          ∂(μH[((2 * d : ℕ) : ℝ)])
      = ∫⁻ y in B, ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) * g (T' y) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        setLIntegral_congr_fun hB fun y hy => by rw [hEq y hy, mul_comm]
    _ = ∫⁻ y, g (T' y) ∂ρ := (lintegral_withDensity_eq_lintegral_mul _ hJ (hg.comp hT'm)).symm
    _ = ∫⁻ z, g z ∂(ρ.map T') := (lintegral_map hg hT'm).symm
    _ = _ := by rw [hmap]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem tubeWeight_nonneg {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : 0 ≤ tubeWeight Q y := by
  unfold tubeWeight
  split_ifs <;> positivity

theorem LogLogCutHess.proof (hC : HessCCompPluri.Statement) : LogLogCutHess.Statement := by
  obtain ⟨K, hK0, hK⟩ := logLogStep_deriv2_bound
  refine ⟨K, hK0, fun m Q k y => ?_⟩
  have hc : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hnn : 0 ≤ K / ((k : ℝ) + 1) * tubeWeight Q y :=
    mul_nonneg (div_nonneg hK0 (by linarith)) (tubeWeight_nonneg Q y)
  have hconst : ∀ c : ℝ, logLogCut Q k =ᶠ[𝓝 y] (fun _ => c) → ∃ a b : ℝ,
      |a| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ |b| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧
      hessC (logLogCut Q k) y = (a : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y ∧
      hessC (fun z => logLogCut Q k z ^ 2 / 2) y = (b : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y := by
    intro c hev
    obtain ⟨e1, e2⟩ := hessC_of_eventually_const hev
    exact ⟨0, 0, by simpa using hnn, by simpa using hnn, by simp [e1], by simp [e2]⟩
  by_cases h1 : ‖eval y Q‖ ^ 2 < cutLevel k
  · exact hconst 0 (logLogCut_eventually_zero Q k h1)
  by_cases h2 : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2
  · exact hconst 1 (logLogCut_eventually_one Q k h2)
  have hw0 : 0 < ‖eval y Q‖ ^ 2 := lt_of_lt_of_le (cutLevel_mem k).1 (not_lt.1 h1)
  have hw1 : ‖eval y Q‖ ^ 2 < 1 :=
    lt_of_le_of_lt (not_lt.1 h2) (Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _)))
  have hLy : logAbsSq Q y ≤ -1 := by
    have e1 : logAbsSq Q y ≤ -Real.exp (((k : ℝ) + 1) / 2) := (Real.log_le_iff_le_exp hw0).2 (not_lt.1 h2)
    have e2 : 1 ≤ Real.exp (((k : ℝ) + 1) / 2) := Real.one_le_exp (by positivity)
    linarith
  have htw : tubeWeight Q y = (logAbsSq Q y ^ 2)⁻¹ := if_pos hLy
  have hg : AnalyticAt ℂ (fun z => eval z Q) y := AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)
  have hgy : eval y Q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw0
    norm_num at hw0
  have hLcd : ContDiffAt ℝ 2 (logAbsSq Q) y :=
    (((contDiff_norm_sq ℝ).contDiffAt).comp y (hg.contDiffAt.restrict_scalars ℝ)).log hw0.ne'
  have hlcd : ContDiffAt ℝ 2 (fun z => Real.log ‖eval z Q‖) y :=
    ((contDiffAt_norm ℝ hgy).comp y (hg.contDiffAt.restrict_scalars ℝ)).log (norm_ne_zero_iff.2 hgy)
  have hLpl : hessC (logAbsSq Q) y = 0 := by
    have e : logAbsSq Q = fun z => Real.log ‖eval z Q‖ + Real.log ‖eval z Q‖ := by
      funext z
      rw [logAbsSq, Real.log_pow]
      push_cast
      ring
    rw [e]
    exact (hessC_add_log_norm _ (fun z => eval z Q) y hlcd hg hgy).trans (hessC_log_norm _ y hg hgy)
  obtain ⟨hFcd, hHcd, hF2, hH2⟩ := hK ((k : ℝ) + 1) hc (logAbsSq Q y) (by linarith)
  have hev := logLogCut_eventually_step Q k hw0 hw1
  have hevsq : (fun z => logLogCut Q k z ^ 2 / 2) =ᶠ[𝓝 y]
      fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) ^ 2 / 2 := by
    filter_upwards [hev] with z hz
    rw [hz]
  have eF := hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1))) (logAbsSq Q) y hFcd hLcd hLpl
  have eH := hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1)) ^ 2 / 2) (logAbsSq Q) y hHcd hLcd hLpl
  rw [← hessC_congr' hev] at eF
  rw [← hessC_congr' hevsq] at eH
  refine ⟨_, _, ?_, ?_, eF, eH⟩
  · rw [htw, ← div_eq_mul_inv, div_div]; exact hF2
  · rw [htw, ← div_eq_mul_inv, div_div]; exact hH2

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Matrix ComplexSets

noncomputable section

theorem measurable_tubeWeight {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) : Measurable (tubeWeight Q) := by
  have hl : Measurable (logAbsSq Q) :=
    Real.measurable_log.comp ((MvPolynomial.continuous_eval Q).norm.pow 2).measurable
  exact Measurable.ite (measurableSet_le hl measurable_const) ((hl.pow_const 2).inv) measurable_const

theorem measurable_tubeDens {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (tubeDens J A P R φ) := by
  have hAm : Measurable fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).continuous.measurable
  have hw : Measurable ((Metric.closedBall (0 : Fin n → ℂ) R).indicator
      fun x => tubeWeight P (A *ᵥ x)) :=
    ((measurable_tubeWeight P).comp hAm).indicator measurableSet_closedBall
  exact SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
    (continuous_abs.comp continuous_mul).measurable hw _

theorem tubeDens_nonneg {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin (d + 1) → ℂ) : 0 ≤ tubeDens J A P R φ y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity

theorem CutOffTube.proof (hC : TubeFormCompare.Statement) (hE : TubeEuclMass.Statement) :
    CutOffTube.Statement := by
  intro n d J A P R φ hJ hdim hA hP hφ
  obtain ⟨C, hCle⟩ := hC n d J A P R φ hJ hdim hA hφ
  refine Integrable.mono' ((hE n d J A P R hJ hdim hA hP).const_mul C)
    (measurable_tubeDens hA P R φ).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (tubeDens_nonneg J A P R φ y)]
  exact hCle y

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def coordGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (i : σ) : holGerms w :=
  ⟨↑(fun z : σ → ℂ => z i), fun z => z i,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w, rfl⟩

def IsFiniteGermProjection {σ : Type} [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) : Prop :=
  (∀ φ : holGerms (A w), germPull A (A.analyticAt w) rfl φ ∈ P → φ = 0) ∧
  (∀ ψ : holGerms w, ∃ F : MvPolynomial σ (holGerms (A w)),
      ψ - MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F ∈ P) ∧
  (∀ i : σ, ∃ q : Polynomial (holGerms (A w)), q.Monic ∧
      q.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w i) ∈ P)

theorem isFiniteGermProjection_bot {σ : Type} [Fintype σ] (w : σ → ℂ) :
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w ⊥ A := by
  classical
  let e : (σ → ℂ) ≃L[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm).toContinuousLinearEquiv
  let A : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ) := e
  have hA : AnalyticAt ℂ (⇑A) w := A.analyticAt w
  have hB : AnalyticAt ℂ (⇑e.symm) (A w) := e.symm.analyticAt _
  have hBe : e.symm (A w) = w := e.symm_apply_apply w
  have back : ∀ φ : holGerms (A w), germPull e.symm hB hBe (germPull A hA rfl φ) = φ := fun φ =>
    germPull_germPull _ _ hA rfl hB hBe (fun y => e.apply_symm_apply y) φ
  have fwd : ∀ ψ : holGerms w, germPull A hA rfl (germPull e.symm hB hBe ψ) = ψ := fun ψ =>
    germPull_germPull _ _ hB hBe hA rfl (fun z => e.symm_apply_apply z) ψ
  refine ⟨Fintype.card σ, A, ?_, ?_, ?_⟩
  · intro φ hφ
    rw [Ideal.mem_bot] at hφ
    rw [← back φ, hφ, map_zero]
  · intro ψ
    refine ⟨MvPolynomial.C (germPull e.symm hB hBe ψ), ?_⟩
    rw [MvPolynomial.eval₂_C, fwd, sub_self]
    exact Ideal.zero_mem _
  · intro i
    have hc : AnalyticAt ℂ (fun y : Fin (Fintype.card σ) → ℂ => e.symm y i) (A w) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).comp
        (e.symm : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))).analyticAt _
    let c : holGerms (A w) := ⟨↑(fun y : Fin (Fintype.card σ) → ℂ => e.symm y i), _, hc, rfl⟩
    refine ⟨Polynomial.X - Polynomial.C c, Polynomial.monic_X_sub_C c, ?_⟩
    rw [Ideal.mem_bot, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]
    apply Subtype.ext
    rw [germPull_coe _ hA rfl c _ rfl]
    show (↑(fun z : σ → ℂ => z i) : Germ (𝓝 w) ℂ) = ↑((fun y => e.symm y i) ∘ ⇑A)
    congr 1
    funext z
    simp [A]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

namespace GoodPointBranch

def consZero (d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cons (α := fun _ => (Fin d → ℂ) →L[ℂ] ℂ) 0
    fun j => ContinuousLinearMap.proj j)

theorem consZero_apply {d : ℕ} (v : Fin d → ℂ) : consZero d v = Fin.cons 0 v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consZero]

theorem consZero_apply_zero {d : ℕ} (v : Fin d → ℂ) : consZero d v 0 = 0 := by
  rw [consZero_apply]
  rfl

theorem consZero_tail {d : ℕ} (t : Fin (d + 1) → ℂ) (ht : t 0 = 0) : consZero d (Fin.tail t) = t := by
  rw [consZero_apply, ← ht]
  exact Fin.cons_self_tail t

theorem consZero_injective {d : ℕ} : Function.Injective (consZero d) := fun a b h => by
  rw [consZero_apply, consZero_apply] at h
  exact Fin.cons_right_injective _ h

theorem consZero_mem_ball {d : ℕ} {s : ℝ} {v : Fin d → ℂ} (hv : v ∈ ball (0 : Fin d → ℂ) s) :
    consZero d v ∈ ball (0 : Fin (d + 1) → ℂ) s := by
  rw [mem_ball_zero_iff] at hv ⊢
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg _) hv
  rw [pi_norm_lt_iff hs]
  intro i
  rw [consZero_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hs
  · simpa using (norm_le_pi_norm v j).trans_lt hv

theorem tail_mem_ball {d : ℕ} {s : ℝ} {t : Fin (d + 1) → ℂ} (ht : t ∈ ball (0 : Fin (d + 1) → ℂ) s) :
    Fin.tail t ∈ ball (0 : Fin d → ℂ) s := by
  rw [mem_ball_zero_iff] at ht ⊢
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg _) ht
  rw [pi_norm_lt_iff hs]
  intro j
  exact (norm_le_pi_norm t j.succ).trans_lt ht

def consCLM (d : ℕ) : (ℂ × (Fin d → ℂ)) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cons (α := fun _ => (ℂ × (Fin d → ℂ)) →L[ℂ] ℂ)
    (ContinuousLinearMap.fst ℂ ℂ (Fin d → ℂ))
    fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin d → ℂ)))

theorem consCLM_apply {d : ℕ} (p : ℂ × (Fin d → ℂ)) : consCLM d p = vecCons p.1 p.2 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consCLM]

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn
    fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem slice_chart {d n : ℕ} {ψ : (Fin (d + 1) → ℂ) → Fin n → ℂ} {D : (Fin (d + 1) → ℂ) →L[ℂ] Fin n → ℂ}
    {q : Fin n → ℂ} {S : Set (Fin n → ℂ)} {A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)} {O : Set (Fin d → ℂ)}
    {V : Set (Fin n → ℂ)} {g : (Fin d → ℂ) → Fin n → ℂ}
    (hψ : HasStrictFDerivAt ψ D 0) (hψ0 : ψ 0 = q) (hD : ∀ v, v 0 = 0 → D v = 0 → v = 0)
    (hV : IsOpen V) (hqV : q ∈ V) (hg : AnalyticOnNhd ℂ g O) (hAg : ∀ y ∈ O, A (g y) = y)
    (hS : S ∩ V = g '' O) (hslice : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), ψ (consZero d v) ∈ S) :
    (∀ v, v 0 = 0 → A (D v) = 0 → v = 0) ∧
    ∃ W ∈ 𝓝 (0 : Fin d → ℂ), Set.InjOn (fun v => ψ (consZero d v)) W ∧
      ∀ W' ∈ 𝓝 (0 : Fin d → ℂ), W' ⊆ W → ∃ N ∈ 𝓝 q, S ∩ N ⊆ (fun v => ψ (consZero d v)) '' W' := by
  set σ : (Fin d → ℂ) → Fin n → ℂ := fun v => ψ (consZero d v) with hσdef
  have hσ : HasStrictFDerivAt σ (D.comp (consZero d)) 0 := by
    have h0 : HasStrictFDerivAt ψ D (consZero d 0) := by rw [map_zero]; exact hψ
    exact h0.comp 0 (consZero d).hasStrictFDerivAt
  have hσ0 : σ 0 = q := by simp [hσdef, hψ0]
  have hev : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), σ v ∈ S ∧ σ v ∈ V :=
    hslice.and (hσ.continuousAt.preimage_mem_nhds (by rw [hσ0]; exact hV.mem_nhds hqV))
  have hgA : ∀ x ∈ S, x ∈ V → g (A x) = x := by
    intro x hxS hxV
    have hx : x ∈ g '' O := by rw [← hS]; exact ⟨hxS, hxV⟩
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hAg y hy]
  have hqS : q ∈ S := hσ0 ▸ hev.self_of_nhds.1
  have hAqO : A q ∈ O := by
    have hq : q ∈ g '' O := by rw [← hS]; exact ⟨hqS, hqV⟩
    obtain ⟨y, hy, hyq⟩ := hq
    rw [← hyq, hAg y hy]
    exact hy
  have hcomp : σ =ᶠ[𝓝 0] fun v => g (A (σ v)) := hev.mono fun v hv => (hgA _ hv.1 hv.2).symm
  have hgd : HasFDerivAt g (fderiv ℂ g (A q)) (A (σ 0)) := by
    rw [hσ0]
    exact (hg _ hAqO).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun v => g (A (σ v))) ((fderiv ℂ g (A q)).comp (A.comp (D.comp (consZero d)))) 0 :=
    hgd.comp 0 (A.hasFDerivAt.comp 0 hσ.hasFDerivAt)
  have heq : D.comp (consZero d) = (fderiv ℂ g (A q)).comp (A.comp (D.comp (consZero d))) :=
    hσ.hasFDerivAt.unique (h2.congr_of_eventuallyEq hcomp)
  have ha : ∀ v, v 0 = 0 → A (D v) = 0 → v = 0 := by
    intro v hv0 hAv
    apply hD v hv0
    have h := congrArg (fun L : (Fin d → ℂ) →L[ℂ] Fin n → ℂ => L (Fin.tail v)) heq
    simp only [ContinuousLinearMap.comp_apply, consZero_tail v hv0, hAv, map_zero] at h
    exact h
  refine ⟨ha, ?_⟩
  have hinj : Function.Injective (A.comp (D.comp (consZero d))) := by
    intro a b hab
    simp only [ContinuousLinearMap.comp_apply] at hab
    have h0 : A (D (consZero d (a - b))) = 0 := by rw [map_sub, map_sub, map_sub, hab, sub_self]
    have h1 := ha _ (consZero_apply_zero _) h0
    exact sub_eq_zero.1 (consZero_injective (by rw [h1, map_zero]))
  let e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ) :=
    (LinearEquiv.ofInjectiveEndo ((A.comp (D.comp (consZero d))) : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
      hinj).toContinuousLinearEquiv
  have he : (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) = A.comp (D.comp (consZero d)) := by
    ext v
    rfl
  have hF : HasStrictFDerivAt (fun v => A (σ v)) (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0 := by
    rw [he]
    exact A.hasStrictFDerivAt.comp 0 hσ
  have hΦ : ⇑(hF.toOpenPartialHomeomorph (fun v => A (σ v))) = fun v => A (σ v) :=
    hF.toOpenPartialHomeomorph_coe
  refine ⟨(hF.toOpenPartialHomeomorph _).source ∩ {v | σ v ∈ S ∧ σ v ∈ V},
    inter_mem ((hF.toOpenPartialHomeomorph _).open_source.mem_nhds hF.mem_toOpenPartialHomeomorph_source) hev,
    ?_, ?_⟩
  · intro a ha' b hb' hab
    exact (hF.toOpenPartialHomeomorph _).injOn ha'.1 hb'.1 (by rw [hΦ]; exact congrArg A hab)
  · intro W' hW' hW'W
    have himg : (fun v => A (σ v)) '' W' ∈ 𝓝 (A q) := by
      have h1 : (fun v => A (σ v)) '' W' ∈ map (fun v => A (σ v)) (𝓝 0) := image_mem_map hW'
      rw [hF.map_nhds_eq_of_equiv] at h1
      simpa only [hσ0] using h1
    refine ⟨V ∩ A ⁻¹' ((fun v => A (σ v)) '' W'),
      inter_mem (hV.mem_nhds hqV) (A.continuous.continuousAt.preimage_mem_nhds himg), ?_⟩
    rintro x ⟨hxS, hxV, hxW⟩
    obtain ⟨v, hv, hvx⟩ := hxW
    have hvx' : A (σ v) = A x := hvx
    have hvW := hW'W hv
    refine ⟨v, hv, ?_⟩
    show σ v = x
    rw [← hgA _ hvW.2.1 hvW.2.2, hvx', hgA x hxS hxV]

end GoodPointBranch

end

end GroundTheory.Heights₂.Heights
end
