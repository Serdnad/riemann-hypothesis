module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle003
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle004
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def cE (E : M2 n) (s : ℝ) : M2 n := NormedSpace.exp (s • E)

set_option backward.isDefEq.respectTransparency false in
theorem cE_entry (E : M2 n) (a b : Fin n ⊕ Fin n) :
    HasDerivAt (fun s : ℝ => cE E s a b) (E a b) 0 := by
  open scoped Matrix.Norms.Operator in
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) E (0 : ℝ)
  open scoped Matrix.Norms.Operator in
  have h2 := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simpa [Function.comp_def, cE] using h2

theorem cE_hasDerivAt0 (E : M2 n) : HasDerivAt (cE E) E 0 := by
  have h : HasDerivAt (fun s : ℝ => (cE E s : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
      (E : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ) 0 :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => cE_entry E a b
  exact h

theorem cE_zero (E : M2 n) : cE E 0 = 1 := by simp [cE]

theorem cE_add (E : M2 n) (s t : ℝ) : cE E (s + t) = cE E s * cE E t := by
  unfold cE
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl E).smul_left s |>.smul_right t)

def mulL (A : M2 n) : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ A)

def mulR (A : M2 n) : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ A)

theorem mulL_apply (A B : M2 n) : mulL A B = A * B := rfl

theorem cE_hasDerivAt (E : M2 n) (s : ℝ) : HasDerivAt (cE E) (cE E s * E) s := by
  have h0 : HasDerivAt (fun t : ℝ => cE E (t - s)) E s := by
    have h : HasDerivAt (cE E) E (s - s) := by simpa using cE_hasDerivAt0 E
    exact HasDerivAt.comp_sub_const s s h
  have h1 : HasDerivAt (fun t : ℝ => cE E s * cE E (t - s)) (cE E s * E) s :=
    (mulL (cE E s)).hasFDerivAt.comp_hasDerivAt s h0
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only
  rw [← cE_add]
  congr 1
  ring

theorem cE_continuous (E : M2 n) : Continuous (cE E) :=
  continuous_iff_continuousAt.2 fun s => (cE_hasDerivAt E s).continuousAt

theorem JJ_conjTranspose : (JJ n)ᴴ = -JJ n := by
  simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]

theorem cE_inK (E : M2 n) (hE : Eᴴ = -E) (hEJ : E * JJ n = JJ n * E) (s : ℝ) : InK (cE E s) := by
  have hct : (cE E s)ᴴ = cE E (-s) := by
    unfold cE
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hE]
    simp [neg_smul, smul_neg]
  have hinv : (cE E s)ᴴ * cE E s = 1 := by
    rw [hct, ← cE_add, neg_add_cancel, cE_zero]
  have hcomm : cE E s * JJ n = JJ n * cE E s := by
    have hc : Commute (s • E) (JJ n) := by
      show s • E * JJ n = JJ n * (s • E)
      rw [Matrix.smul_mul, hEJ, Matrix.mul_smul]
    exact (hc.exp_left).eq
  refine ⟨?_, hinv⟩
  unfold InG
  rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

theorem core {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n)
    (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hKU : KSet n ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (E : M2 n) (hE : Eᴴ = -E) (hEJ : E * JJ n = JJ n * E) :
    Integrable (fun k => fderiv ℝ F (ι k) (E * ι k)) μ ∧ ∫ k, fderiv ℝ F (ι k) (E * ι k) ∂μ = 0 := by
  have hΦc : Continuous (fun p : ℝ × Kg => cE E p.1 * ι p.2) :=
    ((cE_continuous E).comp continuous_fst).matrix_mul (hι.comp continuous_snd)
  have hmem0 : ∀ k, ι k ∈ U := fun k => hKU ((hK (ι k)).2 ⟨k, rfl⟩)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k ∈ (Set.univ : Set Kg), cE E s * ι k ∈ U := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun k _ => ?_
    have h0 : cE E 0 * ι k ∈ U := by rw [cE_zero, Matrix.one_mul]; exact hmem0 k
    exact hΦc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hin : ∀ s : ℝ, |s| ≤ ε / 2 → ∀ k, cE E s * ι k ∈ U := fun s hs k =>
    hball (by rw [Real.dist_eq, sub_zero]; linarith) k (Set.mem_univ _)
  have hfd : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  set S : Set (ℝ × Kg) := Set.Icc (-(ε / 2)) (ε / 2) ×ˢ Set.univ
  have hS : IsCompact S := isCompact_Icc.prod isCompact_univ
  have hmapS : ∀ p ∈ S, cE E p.1 * ι p.2 ∈ U := fun p hp =>
    hin p.1 (abs_le.2 ⟨hp.1.1, hp.1.2⟩) p.2
  have hGc : ContinuousOn (fun p : ℝ × Kg => fderiv ℝ F (cE E p.1 * ι p.2) (cE E p.1 * E * ι p.2)) S := by
    refine ContinuousOn.clm_apply (hfd.comp hΦc.continuousOn hmapS) ?_
    exact ((((cE_continuous E).comp continuous_fst).matrix_mul continuous_const).matrix_mul (hι.comp continuous_snd)).continuousOn
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hGc
  have hdiffF : ∀ y ∈ U, DifferentiableAt ℝ F y := fun y hy =>
    (hF.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hy)
  have hs : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by linarith)
  have hsub : ∀ s ∈ Metric.ball (0 : ℝ) (ε / 2), |s| ≤ ε / 2 := fun s hs' => by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs'; exact hs'.le
  have hcontF : ∀ s : ℝ, |s| ≤ ε / 2 → Continuous (fun k => F (cE E s * ι k)) := fun s hs' =>
    hF.continuousOn.comp_continuous (continuous_const.matrix_mul hι) fun k => hin s hs' k
  have hcontF' : ∀ s : ℝ, |s| ≤ ε / 2 →
      Continuous (fun k => fderiv ℝ F (cE E s * ι k) (cE E s * E * ι k)) := fun s hs' =>
    (hfd.comp_continuous (continuous_const.matrix_mul hι) fun k => hin s hs' k).clm_apply (continuous_const.matrix_mul hι)
  have h0 : |(0 : ℝ)| ≤ ε / 2 := by rw [abs_zero]; linarith
  have hint0 : Integrable (fun k => F (cE E 0 * ι k)) μ := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcontF 0 h0).continuousOn
    exact Integrable.mono' (integrable_const C) (hcontF 0 h0).aestronglyMeasurable
      (Eventually.of_forall fun k => hC k (Set.mem_univ _))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s k => F (cE E s * ι k)) (bound := fun _ => B)
    (F' := fun s k => fderiv ℝ F (cE E s * ι k) (cE E s * E * ι k)) hs
    (by filter_upwards [hs] with s hs' using (hcontF s (hsub s hs')).aestronglyMeasurable)
    hint0 (hcontF' 0 h0).aestronglyMeasurable
    (Eventually.of_forall fun k s hs' => hB (s, k) ⟨⟨(abs_le.1 (hsub s hs')).1, (abs_le.1 (hsub s hs')).2⟩, Set.mem_univ _⟩)
    (integrable_const B)
    (Eventually.of_forall fun k s hs' => by
      have h1 := cE_hasDerivAt E s
      have h2 : HasDerivAt (fun t => cE E t * ι k) (cE E s * E * ι k) s :=
        (mulR (ι k)).hasFDerivAt.comp_hasDerivAt s h1
      exact (hdiffF _ (hin s (hsub s hs') k)).hasFDerivAt.comp_hasDerivAt s h2)
  have hconst : (fun s : ℝ => ∫ k, F (cE E s * ι k) ∂μ) = fun _ => ∫ k, F (ι k) ∂μ := by
    funext s
    obtain ⟨κ, hκ⟩ := (hK (cE E s)).1 (cE_inK E hE hEJ s)
    have : (fun k => F (cE E s * ι k)) = fun k => (fun k' => F (ι k')) (κ * k) := by
      funext k; show F (cE E s * ι k) = F (ι (κ * k)); rw [map_mul, hκ]
    rw [this, integral_mul_left_eq_self (fun k' => F (ι k')) κ]
  have hd0 : HasDerivAt (fun s : ℝ => ∫ k, F (cE E s * ι k) ∂μ) 0 0 := by
    rw [hconst]; exact hasDerivAt_const _ _
  have huniq := key.2.unique hd0
  have hF' : (fun k => fderiv ℝ F (cE E 0 * ι k) (cE E 0 * E * ι k)) = fun k => fderiv ℝ F (ι k) (E * ι k) := by
    funext k; simp [cE_zero]
  rw [hF'] at key huniq
  exact ⟨key.1, huniq⟩

theorem reK_skew (e : M2 n) : (reK e)ᴴ = -reK e := by
  ext i j
  simp only [reK, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem imK_skew (e : M2 n) : (imK e)ᴴ = -imK e := by
  ext i j
  simp only [imK, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem comm_conjT {e : M2 n} (he : e * JJ n = JJ n * e) : eᴴ * JJ n = JJ n * eᴴ := by
  have h := congrArg conjTranspose he
  rw [conjTranspose_mul, conjTranspose_mul, JJ_conjTranspose] at h
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_inj] at h
  exact h.symm

theorem reK_comm {e : M2 n} (he : e * JJ n = JJ n * e) : reK e * JJ n = JJ n * reK e := by
  unfold reK
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, he, comm_conjT he]

theorem imK_comm {e : M2 n} (he : e * JJ n = JJ n * e) : imK e * JJ n = JJ n * imK e := by
  unfold imK
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, he, comm_conjT he]

theorem leftDeriv : LeftDeriv := by
  intro n Kg _ _ _ _ _ _ μ _ ι hι hK F U hU hKU hF e he
  obtain ⟨i1, z1⟩ := core μ ι hι hK F U hU hKU hF (reK e) (reK_skew e) (reK_comm he)
  obtain ⟨i2, z2⟩ := core μ ι hι hK F U hU hKU hF (imK e) (imK_skew e) (imK_comm he)
  refine ⟨i1.add (i2.const_mul Complex.I), ?_⟩
  unfold dK
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, z1, z2]
  simp

end PositivityTheory.Rg.Sw.LVs.II
end
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace STD

variable {n : ℕ}

theorem contDiffOn_dc {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (a : Fin n × Fin n) : ContDiffOn ℝ ∞ (dc a f) U := by
  have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.clm_apply contDiffOn_const).add (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))

theorem contDiffOn_dList {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    ∀ l : List (Fin n × Fin n), ContDiffOn ℝ ∞ (dList l f) U
  | [] => hf
  | a :: l => contDiffOn_dc hU (contDiffOn_dList hU hf l) a

structure IsT (U : Set (Vr n)) (φ : Vr n → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  cpt : HasCompactSupport φ
  sub : tsupport φ ⊆ U

theorem support_dc_subset (f : Vr n → ℂ) (a : Fin n × Fin n) : support (dc a f) ⊆ tsupport f := by
  intro x hx
  by_contra h
  apply hx
  have : fderiv ℝ f x = 0 := by
    by_contra h'
    exact h (support_fderiv_subset (𝕜 := ℝ) h')
  simp [dc, this]

theorem isT_dc {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) (a : Fin n × Fin n) : IsT U (dc a φ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact contDiffOn_univ.mp (contDiffOn_dc isOpen_univ (contDiffOn_univ.mpr h.smooth) a)
  · exact h.cpt.mono' (support_dc_subset φ a)
  · exact (closure_minimal (support_dc_subset φ a) (isClosed_tsupport φ)).trans h.sub

theorem isT_dList {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) : ∀ l : List (Fin n × Fin n), IsT U (dList l φ)
  | [] => h
  | a :: l => isT_dc (isT_dList h l) a

theorem tsupport_dList_subset (φ : Vr n → ℂ) : ∀ l : List (Fin n × Fin n), tsupport (dList l φ) ⊆ tsupport φ
  | [] => le_rfl
  | a :: l => (closure_minimal ((support_dc_subset _ a).trans (tsupport_dList_subset φ l))
      (isClosed_tsupport φ))

theorem integrable_mul_of_contOn {U : Set (Vr n)} (hU : IsOpen U) {h φ : Vr n → ℂ} (hh : ContinuousOn h U)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (fun x => h x * φ x) := by
  have hc' : Continuous (fun x => h x * φ x) :=
    (hh.mul hφ.continuousOn).continuous_of_tsupport_subset hU ((tsupport_mul_subset_right).trans hs)
  exact hc'.integrable_of_hasCompactSupport hc.mul_left

theorem ibp_dc {U : Set (Vr n)} (hU : IsOpen U) {F φ : Vr n → ℂ} (hF : ContDiffOn ℝ ∞ F U)
    (hφ : IsT U φ) (a : Fin n × Fin n) :
    ∫ x, F x * dc a φ x = - ∫ x, dc a F x * φ x := by
  have hFd : ∀ x ∈ tsupport φ, DifferentiableAt ℝ F x := fun x hx =>
    (hF.contDiffAt (hU.mem_nhds (hφ.sub hx))).differentiableAt (by simp)
  have hφd : ∀ x ∈ tsupport F, DifferentiableAt ℝ φ x := fun x _ =>
    (hφ.smooth.differentiable (by simp)) x
  have hFc : ContinuousOn (fun x => fderiv ℝ F x) U := hF.continuousOn_fderiv_of_isOpen hU (by simp)
  have hφc : Continuous (fun x => fderiv ℝ φ x) := hφ.smooth.continuous_fderiv (by simp)
  have hA : ∀ v : Vr n, Integrable (fun x => fderiv ℝ F x v * φ x) := fun v =>
    integrable_mul_of_contOn hU (hFc.clm_apply continuousOn_const) hφ.smooth.continuous hφ.cpt hφ.sub
  have hB : ∀ v : Vr n, Integrable (fun x => F x * fderiv ℝ φ x v) := fun v =>
    integrable_mul_of_contOn hU hF.continuousOn (hφc.clm_apply continuous_const)
      (hφ.cpt.fderiv_apply ℝ v)
      ((closure_minimal (fun x hx => support_fderiv_subset ℝ
        (fun h0 => (Function.mem_support.mp hx) (by simp [h0])))
        (isClosed_tsupport φ)).trans hφ.sub)
  have key : ∀ v : Vr n, ∫ x, F x * fderiv ℝ φ x v = - ∫ x, fderiv ℝ F x v * φ x := fun v =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hA v) (hB v)
      (integrable_mul_of_contOn hU hF.continuousOn hφ.smooth.continuous hφ.cpt hφ.sub) hFd hφd
  have e1 : ∫ x, F x * dc a φ x
      = (∫ x, F x * fderiv ℝ φ x (v1 a.1 a.2)) + Complex.I * ∫ x, F x * fderiv ℝ φ x (v2 a.1 a.2) := by
    rw [← integral_const_mul, ← integral_add (hB _) ((hB _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  have e2 : ∫ x, dc a F x * φ x
      = (∫ x, fderiv ℝ F x (v1 a.1 a.2) * φ x) + Complex.I * ∫ x, fderiv ℝ F x (v2 a.1 a.2) * φ x := by
    rw [← integral_const_mul, ← integral_add (hA _) ((hA _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  rw [e1, e2, key, key]
  ring

theorem ibp_dList {U : Set (Vr n)} (hU : IsOpen U) :
    ∀ (l : List (Fin n × Fin n)) {F φ : Vr n → ℂ}, ContDiffOn ℝ ∞ F U → IsT U φ →
      ∫ x, F x * dList l φ x = (-1) ^ l.length * ∫ x, dList l.reverse F x * φ x := by
  intro l
  match l with
  | [] => intro F φ _ _; simp [dList]
  | a :: l =>
    intro F φ hF hφ
    have happ : ∀ (l m : List (Fin n × Fin n)) (f : Vr n → ℂ), dList (l ++ m) f = dList l (dList m f) := by
      intro l m f
      induction l with
      | nil => simp [dList]
      | cons b l ih => simp [dList, ih]
    have h1 := ibp_dc hU hF (isT_dList hφ l) a
    have h2 := ibp_dList hU l (contDiffOn_dc hU hF a) hφ
    rw [dList, h1, h2, List.reverse_cons, happ]
    simp only [dList, List.length_cons, pow_succ]
    ring

end STD

end PositivityTheory.Rg.Sw.LVs
end
end
