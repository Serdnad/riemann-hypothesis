module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

@[expose] public section

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem yF_gram_entry (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {R : ℝ}
    (hR : ∀ w ∈ Metric.ball (0 : V (nd X)) R, cpt X x w ∈ X.dom) {w : V (nd X)}
    (hw : w ∈ Metric.ball (0 : V (nd X)) R) (τ : X.Ψ) (a b : Fin r) :
    ∑ k, yF X w τ k a * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) * conj (yF X w τ k b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
  have h1 := FrameDegreeData.ortho_bOf X (hR w hw) τ
  rw [bOf_cpt X hx w] at h1
  have h2 : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [h2, FrameDegreeData.gram_mul, hx τ] at h1
  have h3 := congrFun (congrFun h1 a) b
  rw [Matrix.mul_apply] at h3
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply] at h3
  rw [← h3]
  rfl

theorem dY_skew (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    dY X z τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (dY X z τ a b) = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  obtain ⟨R, hR, hdom⟩ := exists_ball X hx
  set ε : Fin r → ℂ := fun k => ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) with hε
  have hY : HasFDerivAt (yF X) (dY X) 0 := hd.hasFDerivAt
  let P : Fin r → Fin r → (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ := fun k c =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) c).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) k).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : ∀ k c, HasFDerivAt (fun w => yF X w τ k c) ((P k c).comp (dY X)) 0 :=
    fun k c => (P k c).hasFDerivAt.comp 0 hY
  have hcc : ∀ k c, HasFDerivAt (fun w => conj (yF X w τ k c))
      ((Complex.conjCLE.toContinuousLinearMap).comp ((P k c).comp (dY X))) 0 :=
    fun k c => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp 0 (hc k c)
  have hf := HasFDerivAt.sum (u := Finset.univ) fun k _ => ((hc k a).mul_const (ε k)).mul (hcc k b)
  have hconst : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b))
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    refine (hasFDerivAt_const (if a = b then ε a else 0) (0 : V (nd X))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with w hw
    exact yF_gram_entry X hx hdom hw τ a b
  have hf' : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b)) _ 0 :=
    hf.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [Finset.sum_apply])
  have key := congrArg (fun L => L z) (hf'.unique hconst)
  have h0 : ∀ k c, yF X 0 τ k c = if k = c then 1 else 0 := by
    intro k c
    show yM X 0 τ k c = _
    rw [yM_zero, Matrix.one_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, h0] at key
  simp only [ite_mul, one_mul, zero_mul, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_smul, zero_smul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, P, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at key
  linear_combination key

end GlobalTheory.SUChartSection
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem yF_expand {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (w : V (nd X)) (τ : X.Ψ) (k j : Fin r) :
    yF X w τ k j = (∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m j) + gsB X w τ k j := by
  simp only [yF, yM, Matrix.mul_apply, mat, Matrix.of_apply]
  have hk : gsB X w τ k j = ∑ m, if k = m then gsB X w τ m j else 0 := by simp
  rw [Finset.sum_filter, hk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases lt_trichotomy m k with h | h | h
  · simp [h, h.ne']
  · subst h; simp [nmat]
  · have h1 : ¬ m < k := not_lt.2 h.le
    have h2 : k ≠ m := h.ne
    simp [nmat, h1, h2]

theorem diagreal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (_hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    (dY X z τ a a).im = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  have hY : ∀ k j : Fin r, DifferentiableAt ℝ (fun w => yF X w τ k j) 0 := by
    intro k j
    exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hd τ) k) j
  have hN : ∀ k m : Fin r, DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ k m) 0 := fun k m =>
    ((PoinPf.diff_nmat X τ k m) 0).restrictScalars ℝ
  have hB : ∀ n : ℕ, ∀ k : Fin r, k.val = n → DifferentiableAt ℝ (fun w => gsB X w τ k a) 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk
      have hrepr : (fun w => gsB X w τ k a) = fun w => yF X w τ k a -
          ∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m a := by
        funext w; rw [yF_expand]; ring
      rw [hrepr]
      refine (hY k a).sub (DifferentiableAt.fun_sum fun m hm => (hN k m).mul (ih m.val ?_ m rfl))
      have := (Finset.mem_filter.1 hm).2
      rw [Fin.lt_def] at this
      omega
  have hN0 : ∀ m : Fin r, m < a → nmat X 0 τ a m = 0 := by
    intro m hm
    have := congrFun (congrFun (PoinPf.nmat_zero X τ) a) m
    simp only [mat, Matrix.of_apply, Matrix.one_apply, hm.ne', if_false] at this
    exact this
  have hB0 : ∀ m : Fin r, m < a → gsB X 0 τ m a = 0 := by
    intro m hm
    rw [gsB_zero, Matrix.one_apply, if_neg hm.ne]
  have hsum : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    have h : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
        (∑ m ∈ Finset.univ.filter (· < a), (nmat X 0 τ a m • fderiv ℝ (fun w => gsB X w τ m a) 0 +
          gsB X 0 τ m a • fderiv ℝ (fun w : V (nd X) => nmat X w τ a m) 0)) 0 :=
      HasFDerivAt.fun_sum (fun m _ => (hN a m).hasFDerivAt.mul (hB m.val m rfl).hasFDerivAt)
    convert h using 1
    symm
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' := (Finset.mem_filter.1 hm).2
    rw [hN0 m hm', hB0 m hm', zero_smul, zero_smul, add_zero]
  have him : HasFDerivAt (fun w => (yF X w τ a a).im) (0 : V (nd X) →L[ℝ] ℝ) 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) hsum
    rw [ContinuousLinearMap.comp_zero] at h
    have hf : (fun w => (yF X w τ a a).im) =
        ⇑Complex.imCLM ∘ fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a := by
      funext w
      simp only [Function.comp_apply, Complex.imCLM_apply]
      rw [yF_expand, Complex.add_im, gsB_diag, Complex.ofReal_im, add_zero]
    rw [hf]; exact h
  let L : (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : HasFDerivAt (fun w => (yF X w τ a a).im) (Complex.imCLM.comp (L.comp (dY X))) 0 :=
    Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) (L.hasFDerivAt.comp (0 : V (nd X)) hd.hasFDerivAt)
  have := congrArg (fun L => L z) (hc.unique him)
  simpa [L] using this

end GlobalTheory.SUChartSection
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection.GSSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Mat

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : Set W}

theorem cdo_det {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) : ContDiffOn ℝ ∞ (fun w => (f w).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

theorem cdo_inv {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hd : ∀ w ∈ s, (f w).det ≠ 0) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine ((cdo_det f hf).inv hd).mul (cdo_det _ fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf _ _

theorem cdo_mul {m : Type} [Fintype m] (f g : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun w => g w i j) s) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w * g w) i j) s := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)

end Mat

theorem contDiff_nmat (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => mat (nmat X w) τ a b := by
  show ContDiff ℝ ∞ fun w : V (nd X) => nmat X w τ a b
  unfold nmat
  split_ifs
  · exact ((EuclideanSpace.proj _ : V (nd X) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  · exact contDiff_const
  · exact contDiff_const

theorem contDiff_Gw (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => PoinPf.Gw X w τ a b := by
  simp only [PoinPf.Gw, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul
    (ContDiff.sum fun l _ => (contDiff_nmat X τ l a).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_nmat X τ k b)

theorem blk_det_on (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (c : Fin r) :
    ∀ w ∈ {w : V (nd X) | cpt X x w ∈ X.dom}, (FrameDegreeData.blk (PoinPf.Gw X w τ) c).det ≠ 0 := by
  intro w hw
  have h := FrameDegreeData.blk_det X hw τ c
  rwa [gram_cpt X hx] at h

theorem cdo_gsU (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (j c : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsU X w τ j c) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  simp only [gsU, FrameDegreeData.uMat, Matrix.of_apply]
  split_ifs with h1 h2
  · exact contDiffOn_const
  · refine ContDiffOn.neg ?_
    simp only [Matrix.vecMul, dotProduct]
    refine ContDiffOn.sum fun m _ => ContDiffOn.mul ?_ ?_
    · exact (contDiff_Gw X τ c (Fin.castLE c.isLt.le m)).contDiffOn
    · exact cdo_inv (fun w => FrameDegreeData.blk (PoinPf.Gw X w τ) c)
        (fun a b => (contDiff_Gw X τ (Fin.castLE c.isLt.le a) (Fin.castLE c.isLt.le b)).contDiffOn)
        (blk_det_on X hx τ c) _ _
  · exact contDiffOn_const

theorem cdo_q (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (i j : Fin r) :
    ContDiffOn ℝ ∞ (fun w => ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) i j)
      {w : V (nd X) | cpt X x w ∈ X.dom} := by
  refine cdo_mul _ _ (fun a b => cdo_mul _ _ (fun a' b' => ?_) (fun a' b' => (contDiff_Gw X τ a' b').contDiffOn) a b)
    (fun a b => ?_) i j
  · exact cdo_gsU X hx τ b' a'
  · exact Complex.conjCLE.contDiff.comp_contDiffOn (cdo_gsU X hx τ a b)

theorem q_eq_dOf (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ) (k : Fin r) :
    ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k = FrameDegreeData.dOf X (cpt X x w) τ k := by
  simp only [FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsU]

theorem cdo_gsS (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (k : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsS X w τ k) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  set S := {w : V (nd X) | cpt X x w ∈ X.dom}
  have hpos : ∀ w ∈ S, 0 < sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re := by
    intro w hw
    rw [q_eq_dOf X hx w τ k]
    exact FrameDegreeData.sgn_dOf_pos X hw τ k
  have hf : ContDiffOn ℝ ∞ (fun w => sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re) S :=
    contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn (cdo_q X hx τ k k))
  refine ContDiffOn.congr (ContDiffOn.inv (hf.sqrt fun w hw => (hpos w hw).ne')
    fun w hw => (Real.sqrt_pos.2 (hpos w hw)).ne') fun w hw => ?_
  have h := hpos w hw
  simp only [gsS]
  congr 2
  rcases FrameDegreeData.sgn_sq X.p0 k with hs | hs <;> rw [hs] at h ⊢
  · rw [one_mul] at h ⊢
    exact abs_of_pos h
  · rw [neg_one_mul] at h ⊢
    exact abs_of_neg (neg_pos.1 h)

theorem gsB_contDiffOn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r},
    IsOrth X x → ∀ (τ : X.Ψ) (a b : Fin r),
      ContDiffOn ℝ ∞ (fun w => gsB X w τ a b) {w | cpt X x w ∈ X.dom} := by
  intro E _ _ _ r X x hx τ a b
  have e : (fun w => gsB X w τ a b) = fun w => gsU X w τ a b * ((gsS X w τ b : ℝ) : ℂ) := by
    funext w
    simp only [gsB, Matrix.mul_diagonal]
  rw [e]
  exact (cdo_gsU X hx τ a b).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (cdo_gsS X hx τ b))

end GlobalTheory.SUChartSection.GSSmooth
end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreLine

theorem cancel_left {O : Type} [CommRing O] {a b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => hA ?_
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem cancel_left₂ {O : Type} [CommRing O] {a a' b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    {A' : Matrix (Fin a') (Fin b) O} (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) (h' : A' * X = A' * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  refine sub_eq_zero.mp (hA _ ?_ ?_)
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, sub_self]
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h', sub_self]

theorem solve {O : Type} [CommRing O] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) O) (B : Matrix (Fin a) (Fin c) O)
    (h : ∀ v, ∃ w, A *ᵥ w = B *ᵥ v) : ∃ S : Matrix (Fin b) (Fin c) O, B = A * S := by
  choose w hw using h
  refine ⟨Matrix.of fun i j => w (Pi.single j 1) i, Matrix.ext_of_mulVec_single fun j => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← hw]
  congr 1
  rw [Matrix.mulVec_single_one]
  rfl

theorem mkRep {Γ O : Type} [Group Γ] [CommRing O] {a a' m : ℕ} (A : Matrix (Fin a) (Fin m) O)
    (A' : Matrix (Fin a') (Fin m) O) (ρ : Γ →* GL (Fin a) O) (ρ' : Γ →* GL (Fin a') O)
    (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    (hst : ∀ g v, ∃ w, A *ᵥ w = (ρ g : Matrix (Fin a) (Fin a) O) *ᵥ (A *ᵥ v) ∧
      A' *ᵥ w = (ρ' g : Matrix (Fin a') (Fin a') O) *ᵥ (A' *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin m) O, Tw r' ρ A ∧ Tw r' ρ' A' := by
  choose w hw using hst
  let M : Γ → Matrix (Fin m) (Fin m) O := fun g => Matrix.of fun i j => w g (Pi.single j 1) i
  have hM : ∀ g j, M g *ᵥ Pi.single j 1 = w g (Pi.single j 1) := fun g j => by
    rw [Matrix.mulVec_single_one]
    rfl
  have k1 : ∀ g, A * M g = (ρ g : Matrix (Fin a) (Fin a) O) * A := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).1]
  have k2 : ∀ g, A' * M g = (ρ' g : Matrix (Fin a') (Fin a') O) * A' := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).2]
  let f : Γ →* Matrix (Fin m) (Fin m) O :=
    { toFun := M
      map_one' := cancel_left₂ hA (by rw [k1, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
        (by rw [k2, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left₂ hA
        (by rw [k1, ← Matrix.mul_assoc, k1, Matrix.mul_assoc, k1, ← Matrix.mul_assoc, map_mul, Units.val_mul])
        (by rw [k2, ← Matrix.mul_assoc, k2, Matrix.mul_assoc, k2, ← Matrix.mul_assoc, map_mul, Units.val_mul]) }
  refine ⟨f.toHomUnits, fun g => ?_, fun g => ?_⟩
  · rw [MonoidHom.coe_toHomUnits]
    exact k1 g
  · rw [MonoidHom.coe_toHomUnits]
    exact k2 g

theorem rank_map {O F : Type} [CommRing O] [Field F] (f : O →+* F) {a b : ℕ} (A : Matrix (Fin a) (Fin b) O)
    (B : Matrix (Fin b) (Fin a) O) (h : A * B = 1) : (A.map f).rank = a ∧ (B.map f).rank = a :=
  rank_of_mul_eq_one _ _ (by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)])

theorem fibre_line : ∀ {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) (Ac As : Matrix (Fin n) (Fin n) O) (ρc ρs : Γ →* GL (Fin n) O) (x : Fin n → O), Function.Injective Ac.mulVec → Function.Injective As.mulVec → Tw ρc r Ac → Tw ρs r As → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (∀ g, ∃ u, Ac *ᵥ u = (r g : Matrix (Fin n) (Fin n) O) *ᵥ x - fun a => (χ g : O) * x a) → ∃ (r2 : Γ →* GL (Fin (n + 1)) O) (B B' : Matrix (Fin n) (Fin (n + 1)) O) (C : Matrix (Fin 1) (Fin (n + 1)) O) (E : Matrix (Fin (n + 1)) (Fin n) O), Tw r2 r B ∧ Tw r2 ρs B' ∧ Tw r2 (GlobalTheory.TripleGal.rk1 χ) C ∧ Tw ρc r2 E ∧ B * E = Ac ∧ C * E = 0 ∧ B = As * B' ∧ (E.map (residue O)).rank = n ∧ (C.map (residue O)).rank = 1 ∧ (B'.map (residue O)).rank = n ∧ ∀ v, B *ᵥ v = 0 → C *ᵥ v = 0 → v = 0 := by
  intro Γ O _ _ _ _ n r χ Ac As ρc ρs x hAc hAs htc hts h1 h2 h3 h4
  let B : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (x i) (fun j => Ac i j) j
  let Cm : Matrix (Fin 1) (Fin (n + 1)) O := Matrix.of fun _ j => Fin.lastCases (1 : O) (fun _ => 0) j
  let E : Matrix (Fin (n + 1)) (Fin n) O := Matrix.of fun i j => if i = j.castSucc then 1 else 0
  let P : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (0 : O) (fun j => if i = j then 1 else 0) j
  let e : Matrix (Fin (n + 1)) (Fin 1) O := Matrix.of fun _ _ => 1
  have hB : ∀ v, B *ᵥ v = Ac *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • x := fun v => by
    funext i
    simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  have hC : ∀ v, Cm *ᵥ v = fun _ => v (Fin.last n) := fun v => by
    funext i
    simp [Cm, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have hBs : ∀ (u : Fin n → O) (c : O), B *ᵥ (Fin.snoc u c : Fin (n + 1) → O) = Ac *ᵥ u + c • x := fun u c => by
    rw [hB]
    simp
  have hBE : B * E = Ac := by
    ext i k
    simp [B, E, Matrix.mul_apply]
  have hCE : Cm * E = 0 := by
    ext i k
    simp [Cm, E, Matrix.mul_apply]
  have hPE : P * E = 1 := by
    ext i k
    simp [P, E, Matrix.mul_apply, Matrix.one_apply]
  have hCe : Cm * e = 1 := by
    ext i k
    rw [Subsingleton.elim i k]
    simp [Cm, e, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hinj : ∀ v, B *ᵥ v = 0 → Cm *ᵥ v = 0 → v = 0 := fun v hb hc => by
    have hl : v (Fin.last n) = 0 := by
      rw [hC] at hc
      exact congrFun hc 0
    rw [hB, hl, zero_smul, add_zero] at hb
    have h0 : (fun j : Fin n => v j.castSucc) = 0 := hAc (by rw [hb, Matrix.mulVec_zero])
    funext j
    refine Fin.lastCases hl (fun j => congrFun h0 j) j
  have hr : ∀ g, (GlobalTheory.TripleGal.rk1 χ g : Matrix (Fin 1) (Fin 1) O) = Matrix.scalar (Fin 1) (χ g : O) := fun _ => rfl
  obtain ⟨r2, hr2B, hr2C⟩ := mkRep B Cm r (GlobalTheory.TripleGal.rk1 χ) hinj (fun g v => by
    obtain ⟨u, hu⟩ := h4 g
    have hu' : (r g : Matrix (Fin n) (Fin n) O) *ᵥ x = Ac *ᵥ u + (χ g : O) • x := by
      rw [hu]
      exact (sub_add_cancel _ _).symm
    refine ⟨Fin.snoc ((ρc g : Matrix (Fin n) (Fin n) O) *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • u)
      ((χ g : O) * v (Fin.last n)), ?_, ?_⟩
    · rw [hBs, hB, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htc g,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hu', smul_add, smul_smul, mul_comm, add_assoc]
    · rw [hC, hC, hr]
      funext i
      simp [Matrix.mulVec_diagonal])
  obtain ⟨B', hB'⟩ := solve As B (fun v => by
    obtain ⟨w0, hw0⟩ := h2
    obtain ⟨w1, hw1⟩ := h3 (fun j => v j.castSucc)
    exact ⟨w1 + v (Fin.last n) • w0, by rw [hB, Matrix.mulVec_add, Matrix.mulVec_smul, hw0, hw1]⟩)
  obtain ⟨S, hS⟩ := solve B' (1 : Matrix (Fin n) (Fin n) O) (fun v => by
    obtain ⟨u, c, huc⟩ := h1 v
    refine ⟨Fin.snoc u c, hAs ?_⟩
    rw [Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hB', hBs, huc]
    rfl)
  refine ⟨r2, B, B', Cm, E, hr2B, fun g => cancel_left hAs ?_, hr2C, fun g => cancel_left₂ hinj ?_ ?_, hBE, hCE, hB',
    (rank_map _ P E hPE).2, (rank_map _ Cm e hCe).1, (rank_map _ B' S hS.symm).1, hinj⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hB', hr2B g, hts g, Matrix.mul_assoc, ← hB']
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBE, hr2B g, Matrix.mul_assoc, hBE, htc g]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCE, hr2C g, Matrix.mul_assoc, hCE, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.FibreLine
end
end

section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.PartSupp

open Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

theorem zeroAt_mul_left (D : Formalism.BasicNotions.D7) {q : ℕ} {e z : AE D} (he : e ∈ OhE D) (hz : ZeroAt D q z) :
    ZeroAt D q (e * z) := by
  intro k
  obtain ⟨m, hm, hc, s, hs, h⟩ := hz k
  exact ⟨m, hm, hc, e * s, mul_mem he hs, by linear_combination e * h⟩

theorem trivAt_part_of_trivAt (D : Formalism.BasicNotions.D7) {N : ℕ} (P : ℕ → Prop) (g : GA D N) {q : ℕ}
    (h : TrivAt D q (g : GL (Fin N) (AE D))) : TrivAt D q (part D P g : GL (Fin N) (AE D)) := by
  intro i j
  have := zeroAt_mul_left D (e := eps D.host.E P) (eps_mem P) (h i j)
  convert this using 1
  show cutM _ _ _ i j - _ = _
  rw [cutM_apply]
  ring

theorem suppInert_part_of_suppInert : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N),
    Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :=
  fun {D} {_} P y hy q hq h => trivAt_part_of_trivAt D P y (hy q hq h)

end GlobalTheory.NormSum.PartSupp
end
