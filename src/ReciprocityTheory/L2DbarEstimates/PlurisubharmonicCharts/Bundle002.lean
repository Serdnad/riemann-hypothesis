module

public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

theorem leviV_smul_real {n : ℕ} (g : V n → ℂ) (u : V n) (r : ℝ) (ζ : V n) :
    leviV n g u (r • ζ).ofLp = ((r ^ 2 : ℝ) : ℂ) * leviV n g u ζ.ofLp := by
  unfold leviV
  simp only [WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

private theorem contDiffOn_infty_wd_wdb {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) :
    ContDiffOn ℝ ∞ (wd n j g) U ∧ ContDiffOn ℝ ∞ (wdb n j g) U := by
  have hF : ∀ v : V n, ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y v) U := fun v =>
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2.clm_apply contDiffOn_const
  constructor
  · unfold wd
    exact ((hF _).sub (contDiffOn_const.mul (hF _))).div_const 2
  · unfold wdb
    exact ((hF _).add (contDiffOn_const.mul (hF _))).div_const 2

theorem continuousOn_wd_wdb {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (j k : Fin n) : ContinuousOn (wd n j (wdb n k g)) U := ((contDiffOn_infty_wd_wdb hU (contDiffOn_infty_wd_wdb hU hg k).2 j).1).continuousOn

theorem levi_pos_compact {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) {K0 : Set (V n)} (hK0 : IsCompact K0) (hK0U : K0 ⊆ U)
    (hpos : ∀ u ∈ K0, ∀ ζ : V n, ζ ≠ 0 → 0 < (leviV n g u ζ.ofLp).re) :
    ∃ m > 0, ∀ u ∈ K0, ∀ ζ : V n, m * ‖ζ‖ ^ 2 ≤ (leviV n g u ζ.ofLp).re := by
  have hcont : ContinuousOn (fun q : V n × V n => (leviV n g q.1 q.2.ofLp).re)
      (K0 ×ˢ Metric.sphere (0 : V n) 1) := by
    unfold leviV
    refine Complex.continuous_re.comp_continuousOn ?_
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
    have hfst : Set.MapsTo Prod.fst (K0 ×ˢ Metric.sphere (0 : V n) 1) U :=
      fun _ hq => hK0U hq.1
    refine (((continuousOn_wd_wdb hU hg j k).comp continuousOn_fst hfst).mul
      ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).continuous.comp continuous_snd).continuousOn).mul
      (Complex.continuous_conj.comp
        ((EuclideanSpace.proj k : V n →L[ℂ] ℂ).continuous.comp continuous_snd)).continuousOn
  by_cases hne : (K0 ×ˢ Metric.sphere (0 : V n) 1).Nonempty
  · obtain ⟨q0, hq0, hmin⟩ := (hK0.prod (isCompact_sphere 0 1)).exists_isMinOn hne hcont
    have hq0ne : q0.2 ≠ 0 := by
      intro h
      have := mem_sphere_zero_iff_norm.1 hq0.2
      rw [h, norm_zero] at this
      exact zero_ne_one this
    refine ⟨(leviV n g q0.1 q0.2.ofLp).re, hpos _ hq0.1 _ hq0ne, fun u hu ζ => ?_⟩
    rcases eq_or_ne ζ 0 with rfl | hζ
    · simp [leviV]
    · have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
      have h1 : (‖ζ‖⁻¹ : ℝ) • ζ ∈ Metric.sphere (0 : V n) 1 := by
        simp [norm_smul, hn.ne']
      have hmin' : (leviV n g q0.1 q0.2.ofLp).re ≤ (leviV n g u ((‖ζ‖⁻¹ : ℝ) • ζ).ofLp).re :=
        isMinOn_iff.1 hmin (u, (‖ζ‖⁻¹ : ℝ) • ζ) ⟨hu, h1⟩
      have hζ' : ζ = ‖ζ‖ • ((‖ζ‖⁻¹ : ℝ) • ζ) := by
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      conv_rhs => rw [hζ', leviV_smul_real, Complex.re_ofReal_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hmin' (sq_nonneg _)
  · refine ⟨1, one_pos, fun u hu ζ => ?_⟩
    rcases eq_or_ne ζ 0 with rfl | hζ
    · simp [leviV]
    · exfalso
      apply hne
      refine ⟨(u, (‖ζ‖⁻¹ : ℝ) • ζ), hu, ?_⟩
      simp [norm_smul, (norm_pos_iff.2 hζ).ne']

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

variable {n : ℕ}

lemma rm_wdb_ofReal_eventually (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (k : Fin n) :
    wdb n k (fun x => (F x : ℂ)) =ᶠ[𝓝 y] fun x =>
      (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2 := by
  filter_upwards [hF.eventually (by simp)] with x hx
  have hd : HasFDerivAt (fun x => (F x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hx.differentiableAt (by norm_num)).hasFDerivAt
  unfold wdb
  rw [hd.fderiv]
  simp

lemma rm_hasFDerivAt_fderiv_apply_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y)
    (w : V n) :
    HasFDerivAt (fun x => ((fderiv ℝ F x w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ F) y).flip w)) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) y := hF.fderiv_right (by norm_num)
  have h2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  have h3 : HasFDerivAt (fun x => fderiv ℝ F x w) ((fderiv ℝ (fderiv ℝ F) y).flip w) y := by
    have := h2.clm_apply (hasFDerivAt_const w y)
    rw [ContinuousLinearMap.comp_zero, zero_add] at this
    exact this
  exact Complex.ofRealCLM.hasFDerivAt.comp y h3

lemma rm_wd_wdb_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (j k : Fin n) :
    wd n j (wdb n k (fun x => (F x : ℂ))) y =
      (((fderiv ℝ (fderiv ℝ F) y (bas n j) (bas n k) : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ (fderiv ℝ F) y (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
        - Complex.I * ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (bas n k) : ℝ) : ℂ)
        + ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)) / 4 := by
  have hS := (rm_hasFDerivAt_fderiv_apply_ofReal F y hF (bas n k)).add
    ((rm_hasFDerivAt_fderiv_apply_ofReal F y hF (Complex.I • bas n k)).const_mul Complex.I)
  have hG := HasFDerivAt.const_mul (𝔸 := ℂ) hS ((2 : ℂ)⁻¹)
  have hfd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (rm_wdb_ofReal_eventually F y hF k)
  have hfun : (fun x => (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2) =
      fun x => (2 : ℂ)⁻¹ * (((fun x => ((fderiv ℝ F x (bas n k) : ℝ) : ℂ)) +
        fun y => Complex.I * ((fderiv ℝ F y (Complex.I • bas n k) : ℝ) : ℂ)) x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  unfold wd
  rw [hfd, hfun, hG.fderiv]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

def rmVec (ξ : Fin n → ℂ) : V n := ∑ j, ξ j • bas n j

lemma rm_cplx_smul_eq (z : ℂ) (x : V n) : z • x = z.re • x + z.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

lemma rm_bil_expand (B : V n →L[ℝ] V n →L[ℝ] ℝ) (z w : ℂ) (a b : V n) :
    B (z • a) (w • b) = z.re * w.re * B a b + z.re * w.im * B a (Complex.I • b)
      + z.im * w.re * B (Complex.I • a) b + z.im * w.im * B (Complex.I • a) (Complex.I • b) := by
  rw [rm_cplx_smul_eq z a, rm_cplx_smul_eq w b]
  simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma rm_bil_sum (B : V n →L[ℝ] V n →L[ℝ] ℝ) (c : Fin n → ℂ) :
    B (∑ j, c j • bas n j) (∑ k, c k • bas n k) = ∑ j, ∑ k, B (c j • bas n j) (c k • bas n k) := by

  simp only [map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_comm

lemma rm_I_smul_vec (ξ : Fin n → ℂ) : Complex.I • rmVec ξ = ∑ j, (Complex.I * ξ j) • bas n j := by
  unfold rmVec
  rw [Finset.smul_sum]
  simp_rw [smul_smul]

theorem rm_levi_re_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (ξ : Fin n → ℂ) :
    4 * (leviV n (fun x => (F x : ℂ)) y ξ).re =
      fderiv ℝ (fderiv ℝ F) y (rmVec ξ) (rmVec ξ) +
        fderiv ℝ (fderiv ℝ F) y (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec]
  unfold rmVec
  rw [rm_bil_sum, rm_bil_sum, ← Finset.sum_add_distrib]
  unfold leviV
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_wd_wdb_ofReal F y hF j k, rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (ξ j) (ξ k),
    rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (Complex.I * ξ j) (Complex.I * ξ k)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

def ovl {n : ℕ} {Y ι : Type*} [TopologicalSpace Y] (chart : ι → OpenPartialHomeomorph Y (V n))
    (i j : ι) : Set (V n) :=
  (chart i).target ∩ (chart i).symm ⁻¹' (chart j).source

structure WeightedAtlas (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (ι : Type*) (La : Type*) [AddCommGroup La] where

  chart : ι → OpenPartialHomeomorph Y (V n)

  pick : Y → ι
  mem_pick : ∀ y, y ∈ (chart (pick y)).source

  holo_trans : ∀ i j, DifferentiableOn ℂ (chart j ∘ (chart i).symm) (ovl chart i j)

  g : La → ι → ι → Y → ℂ
  holo_g : ∀ la i j, DifferentiableOn ℂ (g la i j ∘ (chart i).symm) (ovl chart i j)
  g_ne : ∀ la i j y, y ∈ (chart i).source → y ∈ (chart j).source → g la i j y ≠ 0
  g_cocycle : ∀ la i j k y, y ∈ (chart i).source → y ∈ (chart j).source →
    y ∈ (chart k).source → g la i k y = g la i j y * g la j k y
  g_add : ∀ la mu i j y, y ∈ (chart i).source → y ∈ (chart j).source →
    g (la + mu) i j y = g la i j y * g mu i j y

  ph : La → ι → Y → ℝ
  smooth_ph : ∀ la i, ContDiffOn ℝ ∞ (ph la i ∘ (chart i).symm) (chart i).target
  ph_add : ∀ la mu i y, y ∈ (chart i).source → ph (la + mu) i y = ph la i y + ph mu i y
  ph_trans : ∀ la i j y, y ∈ (chart i).source → y ∈ (chart j).source →
    ph la j y = ph la i y - Real.log (‖g la i j y‖ ^ 2)

  kap : La
  g_kap : ∀ i j y, y ∈ (chart i).source → y ∈ (chart j).source →
    g kap i j y = (fderiv ℂ (chart j ∘ (chart i).symm) (chart i y)).det

  mu : Measure Y
  mu_chart : ∀ i (A : Set Y), MeasurableSet A → A ⊆ (chart i).source →
    mu A = ∫⁻ v in chart i '' A, ENNReal.ofReal (Real.exp (ph kap i ((chart i).symm v)))

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def IsSecOn (A : WeightedAtlas n Y ι La) (la : La) (U : Set Y) (s : ι → Y → ℂ) : Prop :=
  (∀ i, DifferentiableOn ℂ (s i ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) ∧
  ∀ i j y, y ∈ U → y ∈ (A.chart i).source → y ∈ (A.chart j).source → s i y = A.g la i j y * s j y

def IsSec (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) : Prop :=
  A.IsSecOn la Set.univ s

def IsSSec (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (s i ∘ (A.chart i).symm) (A.chart i).target) ∧
  ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → s i y = A.g la i j y * s j y

def IsFrameOn (A : WeightedAtlas n Y ι La) (la : La) (U : Set Y) (s : ι → Y → ℂ) : Prop :=
  A.IsSecOn la U s ∧ ∀ y ∈ U, s (A.pick y) y ≠ 0

def SmoothFn (A : WeightedAtlas n Y ι La) (f : Y → ℝ) : Prop :=
  ∀ i, ContDiffOn ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i).target

def nsq (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (y : Y) : ℝ :=
  ‖s (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y) y)

def sqn {N : ℕ} (A : WeightedAtlas n Y ι La) (la : La) (w : Fin N → ι → Y → ℂ) (y : Y) : ℝ :=
  ∑ k, A.nsq la (w k) y

def leviAt (A : WeightedAtlas n Y ι La) (i : ι) (f : Y → ℝ) (y : Y) (ξ : Fin n → ℂ) : ℝ :=
  (leviV n (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ)) (A.chart i y) ξ).re

def Pos (A : WeightedAtlas n Y ι La) (la : La) (ps : Y → ℝ) : Prop :=
  ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
    0 ≤ A.leviAt i (fun x => A.ph la i x + ps x) y ξ

def dbarAt (A : WeightedAtlas n Y ι La) (i : ι) (F : ι → Y → ℂ) (y : Y) (ξ : Fin n → ℂ) : ℂ :=
  ∑ j, wdb n j (F i ∘ (A.chart i).symm) (A.chart i y) * (starRingEnd ℂ) (ξ j)

def zeroSet {N : ℕ} (A : WeightedAtlas n Y ι La) (s : Fin N → ι → Y → ℂ) : Set Y :=
  {y | ∀ k, s k (A.pick y) y = 0}

def zLoc (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (i : ι) :
    V n → V n :=
  fun v => WithLp.toLp 2 (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v))

def zmap (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (y : Y) : V n :=
  WithLp.toLp 2 (fun k => s k (A.pick y) y / w0 (A.pick y) y)

def IsCoordAt (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (P : Y) :
    Prop :=
  (fderiv ℂ (A.zLoc w0 s (A.pick P)) (A.chart (A.pick P) P)).det ≠ 0

def VanishOrd (A : WeightedAtlas n Y ι La) (s : ι → Y → ℂ) (P : Y) (k : ℕ) : Prop :=
  ∃ C : ℝ, ∀ᶠ v in 𝓝 (A.chart (A.pick P) P),
    ‖s (A.pick P) ((A.chart (A.pick P)).symm v)‖ ≤ C * ‖v - A.chart (A.pick P) P‖ ^ k

def Mset (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (De : MvPolynomial (Fin n) ℂ) : Set Y :=
  {y | w0 (A.pick y) y ≠ 0 ∧ MvPolynomial.eval (fun k => A.zmap w0 s y k) De ≠ 0}

structure D0 {N : ℕ} (A : WeightedAtlas n Y ι La) (L : La) (w : Fin N → ι → Y → ℂ)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) : Prop where
  sec_w : ∀ k, A.IsSec L (w k)
  isSection_denom : A.IsSec L w0
  sec_s : ∀ k, A.IsSec L (s k)
  no_common_zero : ∀ y, ∃ k, w k (A.pick y) y ≠ 0
  finite_S : (A.zeroSet s).Finite
  w0_ne : ∀ P ∈ A.zeroSet s, w0 (A.pick P) P ≠ 0
  coord : ∀ P ∈ A.zeroSet s, A.IsCoordAt w0 s P
  meets : ∀ y, ∃ P ∈ A.zeroSet s, P ∈ connectedComponent y
  family_le_coords : ∀ U : Set Y, IsOpen U → A.zeroSet s ⊆ U → ∃ C : ℝ, ∀ y ∉ U, A.sqn L w y ≤ C * A.sqn L s y
  s_le_w : ∃ C : ℝ, ∀ y, A.sqn L s y ≤ C * A.sqn L w y
  denom_le_family : ∃ C : ℝ, ∀ y, A.nsq L w0 y ≤ C * A.sqn L w y

structure Flat (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (De : MvPolynomial (Fin n) ℂ) : Prop where
  De_ne : De ≠ 0
  deriv_ne : ∀ y ∈ A.Mset w0 s De, (fderiv ℂ (A.zLoc w0 s (A.pick y)) (A.chart (A.pick y) y)).det ≠ 0
  localHomeo : IsLocalHomeomorph (fun y : A.Mset w0 s De => A.zmap w0 s y)
  proper : ∀ K : Set (V n), IsCompact K → (∀ v ∈ K, MvPolynomial.eval (fun k => v k) De ≠ 0) →
    IsCompact (A.Mset w0 s De ∩ A.zmap w0 s ⁻¹' K)

def flatE (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (De : MvPolynomial (Fin n) ℂ) (y : Y) : ℝ :=
  ((De.totalDegree : ℝ) + 1) * Real.log (1 + ‖A.zmap w0 s y‖ ^ 2) -
    Real.log (‖MvPolynomial.eval (fun k => A.zmap w0 s y k) De‖ ^ 2)

end WeightedAtlas

def multiLe (n j : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.range (j + 1)).biUnion (fun d => Finset.Nat.antidiagonalTuple n d)

end

end ReciprocityTheory.L2DbarEstimates.Y
end
