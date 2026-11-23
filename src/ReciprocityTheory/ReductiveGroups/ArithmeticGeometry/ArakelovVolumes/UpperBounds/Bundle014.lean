module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Lemmata.GeneralBFactVersion.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
public import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle007
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lactDom (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X hγ x).2 hx

theorem rmulDom (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X hx hb

theorem isOpenDom (X : Data E r) : IsOpen X.dom := FourierCoefficientDomain.isOpen_dom X

theorem lact_mul' {Ψ : Finset (E →+* ℂ)} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) := by
  funext τ
  simp only [lact, mat, Units.val_mul, Matrix.map_mul]
  rw [Matrix.mul_assoc]
  rfl

theorem lact_rmul' {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

theorem norm_chi (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h1 := congrArg norm (h γ hγ)
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1

theorem chi_ne (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  intro h
  have := norm_chi X la hγ
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem poin_mul (X : Data E r) (la la' : Wt X.Ψ r) (P g : Frame X.Ψ r → ℂ) (hg : X.IsSec la' g)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  dsimp only
  rw [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]
  have h1 := chi_ne X la' γ.2
  have h2 := chi_ne X la γ.2
  field_simp

theorem poin_rmul (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    poin X la P (rmul x b) = bchar la b * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  rw [lact_rmul', hP _ (lactDom X γ.2 hx) b hb]
  ring

theorem poin_lact (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {γ' : GL (Fin r) E}
    (hγ' : γ' ∈ X.Γ) (x : Frame X.Ψ r) :
    poin X la P (lact γ' x) = X.χ la γ' * poin X la P x := by
  unfold poin
  set g : X.Γ := ⟨γ', hγ'⟩
  have key : ∀ γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 (lact γ' x)) =
      X.χ la γ' * ((X.χ la (γ * g).1)⁻¹ * P (lact (γ * g).1 x)) := by
    intro γ
    have hm : ((γ * g : X.Γ) : GL (Fin r) E) = γ.1 * γ' := rfl
    rw [hm, lact_mul', X.χ_mul la γ.1 γ.2 γ' hγ']
    have h1 := chi_ne X la hγ'
    have h2 := chi_ne X la γ.2
    field_simp
  rw [tsum_congr key, tsum_mul_left]
  congr 1
  exact (Equiv.mulRight g).tsum_eq (fun δ : X.Γ => (X.χ la δ.1)⁻¹ * P (lact δ.1 x))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open Metric

theorem fderiv_bound_ball {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {g : Y → ℂ} {y : Y}
    {R M : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball y (2 * R)))
    (hM : ∀ v ∈ ball y (2 * R), ‖g v‖ ≤ M) : ‖fderiv ℂ g y‖ ≤ M / R := by
  first | exact Bl.general_b_fact_version.goal1 .. | (apply Bl.general_b_fact_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_version.goal1 <;> assumption)

theorem differentiableOn_tsum_loc {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {U : Set Y}
    (hU : IsOpen U) (f : ι → Y → ℂ) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hb : ∀ y ∈ U, ∃ ε > 0, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ v ∈ ball y ε, ‖f i v‖ ≤ u i) :
    DifferentiableOn ℂ (fun y => ∑' i, f i y) U := by
  intro y0 hy0
  obtain ⟨ε, hε, u, hu, hub⟩ := hb y0 hy0
  obtain ⟨δ, hδ, hδU⟩ := isOpen_iff.1 hU y0 hy0
  set m := min ε δ with hm
  have hm0 : 0 < m := lt_min hε hδ
  set R := m / 4 with hR
  have hR0 : 0 < R := by positivity
  have hsub : ∀ y ∈ ball y0 R, ball y (2 * R) ⊆ ball y0 m := by
    intro y hy v hv
    rw [mem_ball] at *
    calc dist v y0 ≤ dist v y + dist y y0 := dist_triangle _ _ _
      _ < 2 * R + R := add_lt_add hv hy
      _ ≤ m := by rw [hR]; linarith
  have hε' : ball y0 m ⊆ ball y0 ε := ball_subset_ball (min_le_left _ _)
  have hδ' : ball y0 m ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hδU
  have hin : ∀ y ∈ ball y0 R, y ∈ U := fun y hy => hδ' (hsub y hy (mem_ball_self (by linarith)))
  have hder : ∀ i, ∀ y ∈ ball y0 R, HasFDerivAt (f i) (fderiv ℂ (f i) y) y := fun i y hy =>
    ((hf i y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))).hasFDerivAt
  have hbd : ∀ i, ∀ y ∈ ball y0 R, ‖fderiv ℂ (f i) y‖ ≤ u i / R := fun i y hy =>
    fderiv_bound_ball hR0 ((hf i).mono ((hsub y hy).trans hδ')) (fun v hv => hub i v (hε' (hsub y hy hv)))
  have hs := hasFDerivAt_tsum_of_isPreconnected (hu.div_const R) isOpen_ball
    (convex_ball y0 R).isPreconnected hder hbd (mem_ball_self hR0)
    (Summable.of_norm_bounded hu fun i => hub i y0 (mem_ball_self hε)) (mem_ball_self hR0)
  exact hs.differentiableAt.differentiableWithinAt

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

variable {n : ℕ}

theorem leviV_const (c : ℝ) (x : V n) (ξ : Fin n → ℂ) :
    leviV n (fun _ => (c : ℂ)) x ξ = 0 := by
  have h : ∀ k, wdb n k (fun _ : V n => (c : ℂ)) = fun _ => 0 := by
    intro k; funext y; simp [wdb]
  simp [leviV, h, wd]

theorem quad_contDiff {r s : ℕ} (τ : ℝ) (ℓ : Fin r → Fin s → V n → ℂ)
    (hℓ : ∀ a b, ContDiff ℂ ∞ (ℓ a b)) :
    ContDiff ℝ ∞ (fun y => τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y)) := by
  refine contDiff_const.sub (ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_)
  simp only [Complex.normSq_eq_norm_sq]
  exact (contDiff_norm_sq ℝ).comp ((hℓ a b).restrict_scalars ℝ)

theorem levi_quad_nonpos {r s : ℕ} (τ : ℝ) (ℓ : Fin r → Fin s → V n → ℂ)
    (hℓ : ∀ a b, ContDiff ℂ ∞ (ℓ a b)) (x : V n) (ξ : Fin n → ℂ) :
    (leviV n (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) x ξ).re ≤ 0 := by
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun y => Complex.normSq (ℓ a b y)) x := by
    intro a b
    have h := quad_contDiff (r := 1) (s := 1) 0 (fun _ _ => ℓ a b) (fun _ _ => hℓ a b)
    have h2 : ContDiff ℝ ∞ (fun y => Complex.normSq (ℓ a b y)) := by
      have := h.neg
      simpa using this
    exact h2.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  have hca : ∀ a, ContDiffAt ℝ 2 (fun y => ∑ b, Complex.normSq (ℓ a b y)) x := fun a =>
    ContDiffAt.sum fun b _ => hc a b
  have hS : ContDiffAt ℝ 2 (fun y => ∑ a, ∑ b, Complex.normSq (ℓ a b y)) x :=
    ContDiffAt.sum fun a _ => hca a
  have e1 : (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) =
      fun y => ((τ + (-1) * ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ) := by
    funext y; push_cast; ring
  rw [e1, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add contDiffAt_const (contDiffAt_const.mul hS) ξ,
    leviV_const, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hS ξ,
    ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum hca ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum (fun b => hc _ b) ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.H.leviV_normSq_comp ((hℓ _ _).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)) ξ]
  simp only [zero_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum,
    Complex.im_sum, zero_mul, sub_zero]
  have : 0 ≤ ∑ a : Fin r, ∑ b : Fin s, Complex.normSq (∑ j, wd n j (ℓ a b) x * ξ j) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _
  nlinarith

theorem trace_mul_conjTranspose_re {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℂ) :
    (B * Bᴴ).trace.re = ∑ a, ∑ b, Complex.normSq (B a b) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem Q_formula {r s : ℕ} (Z : Matrix (Fin r) (Fin s) ℂ) (y : Matrix (Fin r) (Fin r) ℂ) :
    ((1 - Z * Zᴴ) * (yᴴ * y)).trace.re =
      (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq ((y * Z) a b) := by
  rw [← trace_mul_conjTranspose_re, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    Complex.sub_re]
  congr 2
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem posDef_swap {r s : ℕ} {Z : Matrix (Fin r) (Fin s) ℂ} (h : (1 - Z * Zᴴ).PosDef) :
    (1 - Zᴴ * Z).PosDef := by
  have hu : IsUnit (1 - Z * Zᴴ).det := isUnit_iff_ne_zero.2 h.det_pos.ne'
  set S := (1 - Z * Zᴴ)⁻¹ with hS
  have hAS : (1 - Z * Zᴴ) * S = 1 := Matrix.mul_nonsing_inv _ hu
  have key : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 := by
    have e : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 + Zᴴ * ((1 - Z * Zᴴ) * S - 1) * Z := by
      simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e, hAS, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hinv : (1 - Zᴴ * Z)⁻¹ = 1 + Zᴴ * S * Z := Matrix.inv_eq_right_inv key
  have hP : (1 + Zᴴ * S * Z).PosDef :=
    PosDef.one.add_posSemidef ((h.inv).posSemidef.conjTranspose_mul_mul_same Z)
  rw [← hinv] at hP
  exact Matrix.posDef_inv_iff.1 hP

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgD

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

variable {f p q : ℕ}

theorem block (hm : 0 < min p q) {v0 : V (nD f p q)} (hv0 : v0 ∈ Dset f p q) (k : Fin f) :
    ∃ Q : V (nD f p q) → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ ξ, (leviV (nD f p q) (fun y => (Q y : ℂ)) v0 ξ).re ≤ 0) ∧
      Q v0 = (min p q : ℕ) ∧
      ∀ v ∈ Dset f p q, dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) ≤
        dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q v / (min p q : ℕ)) := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq] at hm ⊢
    have hA0 := hv0 k
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - Zof v k * (Zof v k)ᴴ) * (1 - Zof v0 k * (Zof v0 k)ᴴ)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞ (fun v : V (nD f p q) => (y * Zof v k) a b) := by
      intro a b
      simp only [Matrix.mul_apply, Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re -
        ∑ a, ∑ b, Complex.normSq ((fun a b (v : V (nD f p q)) => (y * Zof v k) a b) a b v) := by
      funext v; simp only [hQdef]; rw [hy, Q_formula]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      exact RgB.amgm hm (hv k) hA0
  · rw [min_eq_right hqp] at hm ⊢
    have hA0 := posDef_swap (hv0 k)
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - (Zof v k)ᴴ * Zof v k) * (1 - (Zof v0 k)ᴴ * Zof v0 k)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞
        (fun v : V (nD f p q) => ∑ c, star (y a c) * Zof v k b c) := by
      intro a b
      simp only [Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq
        ((fun a b (v : V (nD f p q)) => ∑ c, star (y a c) * Zof v k b c) a b v) := by
      funext v
      simp only [hQdef]
      have h1 := Q_formula (Zof v k)ᴴ y
      rw [Matrix.conjTranspose_conjTranspose] at h1
      rw [hy, h1]
      congr 1
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← Complex.normSq_conj]
      congr 1

      simp [Matrix.mul_apply, conjTranspose_apply, map_sum, Complex.star_def, mul_comm]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      have h := RgB.amgm hm (posDef_swap (hv k)) hA0
      simp only [dk]
      rw [Matrix.det_one_sub_mul_comm, Matrix.det_one_sub_mul_comm (Zof v0 k)]
      exact h

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgD
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def eLE : LoI X.Ψ r ≃ Ent X where
  toFun i := ⟨i.1.1, ⟨(i.1.2.1, i.1.2.2), i.2⟩⟩
  invFun e := ⟨(e.1, e.2.1.1, e.2.1.2), e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def eL : LoI X.Ψ r ≃ Fin (nd X) := (eLE X).trans (Fintype.equivFin (Ent X))

def ΦL : V (nd X) ≃ₗ[ℂ] (LoI X.Ψ r → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).trans (LinearEquiv.funCongrLeft ℂ ℂ (eL X))

lemma NF_ΦL (z : V (nd X)) : NF X (ΦL X z) = nmat X z := by
  funext τ a b
  simp only [NF, Nmat, nmat, Matrix.of_apply]
  split_ifs <;> rfl

def muX (x0 : Frame X.Ψ r) : Measure (V (nd X)) :=
  (volume.restrict {z | cpt X x0 z ∈ X.dom}).withDensity fun z => ENNReal.ofReal (densY X (cpt X x0 z))

def ΦC : V (nd X) ≃L[ℂ] (LoI X.Ψ r → ℂ) := (ΦL X).toContinuousLinearEquiv

lemma lintegral_ΦC (F : (LoI X.Ψ r → ℂ) → ENNReal) :
    ∫⁻ z, F (ΦC X z) = Measure.addHaarScalarFactor (volume.map (ΦC X)) volume * ∫⁻ x, F x := by
  have h1 : (∫⁻ z, F (ΦC X z)) = ∫⁻ x, F x ∂(volume.map (ΦC X)) :=
    (lintegral_map_equiv F (ΦC X).toHomeomorph.toMeasurableEquiv).symm
  calc (∫⁻ z, F (ΦC X z)) = ∫⁻ x, F x ∂(volume.map (ΦC X)) := h1
    _ = ∫⁻ x, F x ∂(Measure.addHaarScalarFactor (volume.map (ΦC X)) volume • volume) := by
        rw [← Measure.isAddLeftInvariant_eq_smul]
    _ = _ := lintegral_smul_measure _ _

lemma continuous_dmin (τ : X.Ψ) (i : Fin (r + 1)) : Continuous fun y : Frame X.Ψ r => dmin X.Gm y τ i := by
  unfold dmin lminor
  apply Continuous.matrix_det
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC,
    ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat]
  fun_prop

lemma measurable_densY : Measurable (densY X) := by
  have h : densY X = fun y => (∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2)⁻¹ :=
    funext fun y => densY_eq X
  rw [h]
  refine Measurable.inv ?_
  refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
  exact ((continuous_dmin X τ _).measurable.norm).pow_const 2

lemma continuous_NF : Continuous (NF X) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : b < a
  · have e : (fun x : LoI X.Ψ r → ℂ => NF X x τ a b) = fun x => x ⟨(τ, a, b), h⟩ := by
      funext x
      simp [NF, Nmat, h]
    rw [e]
    exact continuous_apply _
  · have e : (fun x : LoI X.Ψ r → ℂ => NF X x τ a b) = fun _ => if a = b then 1 else 0 := by
      funext x
      simp [NF, Nmat, h]
    rw [e]
    exact continuous_const

lemma cpt_eq (x0 : Frame X.Ψ r) (z : V (nd X)) : cpt X x0 z = rmul x0 (NF X (ΦC X z)) := by
  show rmul x0 (nmat X z) = rmul x0 (NF X (ΦC X z))
  rw [← NF_ΦL]
  rfl

lemma continuous_cpt (x0 : Frame X.Ψ r) : Continuous (cpt X x0) := by
  rw [show cpt X x0 = fun z => rmul x0 (NF X (ΦC X z)) from funext (cpt_eq X x0)]
  refine continuous_pi fun τ => ?_
  show Continuous fun z => mat x0 τ * mat (NF X (ΦC X z)) τ
  exact continuous_const.matrix_mul (((continuous_apply τ).comp (continuous_NF X)).comp (ΦC X).continuous)

theorem lintegral_muX {x0 : Frame X.Ψ r} {φ : Frame X.Ψ r → ENNReal} (hφm : Measurable φ) :
    ∫⁻ z, φ (cpt X x0 z) ∂muX X x0 =
      Measure.addHaarScalarFactor (volume.map (ΦC X)) volume * ∫⁻ x, GLo X x0 φ x := by
  have hdom : MeasurableSet X.dom := by
    have ho : IsOpen X.dom := by
      show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
      simp only [Set.setOf_forall, Set.setOf_and]
      refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
      · exact isOpen_ne_fun (continuous_apply τ).matrix_det continuous_const
      · exact isOpen_lt continuous_const
          (continuous_const.mul (Complex.continuous_re.comp (continuous_dmin X τ i)))
    exact ho.measurableSet
  have hS : MeasurableSet {z : V (nd X) | cpt X x0 z ∈ X.dom} :=
    hdom.preimage (continuous_cpt X x0).measurable
  have hdens : Measurable fun z => ENNReal.ofReal (densY X (cpt X x0 z)) :=
    ENNReal.measurable_ofReal.comp ((measurable_densY X).comp (continuous_cpt X x0).measurable)
  unfold muX
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens
      (show Measurable fun z => φ (cpt X x0 z) from hφm.comp (continuous_cpt X x0).measurable),
    ← lintegral_indicator hS, ← lintegral_ΦC]
  congr 1
  funext z
  simp [GLo, Set.indicator, cpt_eq, mul_comm]

theorem lintegral_cpt_muX_indep_of_isOrtho {x0 x0' : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (hx0' : X.IsOrtho x0') {φ : Frame X.Ψ r → ENNReal}
    (hφm : Measurable φ) (hφ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    ∫⁻ z, φ (cpt X x0 z) ∂muX X x0 = ∫⁻ z, φ (cpt X x0' z) ∂muX X x0' := by
  rw [lintegral_muX X hφm, lintegral_muX X hφm]
  congr 1
  have h1 := core X hx0 hφm hφ
  have h2 := core X hx0' hφm hφ
  have hK0 : K0 X.Ψ r ≠ 0 := (finrank_maxUnramifiedSubfield_padicFinExt_pos (ι := X.Ψ) (r := r)).ne'
  have hK0' : K0 X.Ψ r ≠ ⊤ := (measureConstant_lt_top (ι := X.Ψ) (r := r)).ne
  exact (ENNReal.mul_left_inj hK0 hK0').mp (h1.trans h2.symm)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end
