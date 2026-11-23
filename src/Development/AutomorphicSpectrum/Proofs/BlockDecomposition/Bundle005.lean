module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.ColimLift

variable {G : ℕ → Type} [∀ n, CommRing (G n)] (f : ∀ n, G n →+* G (n + 1))
  {L : Type} [CommRing L] (ι : ∀ n, G n →+* L)
  (t : ∀ n k, G n → G (n + k))

theorem apply_iter {T : Type} (y : ∀ n, G n → T)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n k : ℕ) (x : G n) :
    y (n + k) (t n k x) = y n x := by
  induction k with
  | zero => exact congrArg (y n) (t0 n x)
  | succ k ih =>
    have h : y (n + (k + 1)) (t n (k + 1) x) = y (n + k + 1) (f (n + k) (t n k x)) :=
      congrArg (y (n + k + 1)) (tS n k x)
    rw [h, hy, ih]

theorem eq_of_same_stage {T : Type} [CommRing T] (y : ∀ n, G n →+* T)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n : ℕ) (a b : G n) (h : ι n a = ι n b) :
    y n a = y n b := by
  obtain ⟨k, hk⟩ := ker n (a - b) (by rw [map_sub, h, sub_self])
  have h1 := apply_iter f t (fun n => (y n : G n → T)) t0 tS hy n k (a - b)
  simp only [hk, map_zero, map_sub] at h1
  exact sub_eq_zero.mp h1.symm

theorem eq_of_iota_eq {T : Type} [CommRing T] (y : ∀ n, G n →+* T)
    (hι : ∀ n x, ι (n + 1) (f n x) = ι n x)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n m : ℕ) (a : G n) (b : G m)
    (h : ι n a = ι m b) : y n a = y m b := by
  have up : ∀ (n m : ℕ), n ≤ m → ∀ a : G n, ∃ a' : G m, ι m a' = ι n a ∧ y m a' = y n a := by
    intro n m hnm a
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact ⟨t n k a, apply_iter f t (fun n => (ι n : G n → L)) t0 tS hι n k a,
      apply_iter f t (fun n => (y n : G n → T)) t0 tS hy n k a⟩
  obtain ⟨a', ha, hya⟩ := up n (max n m) (le_max_left _ _) a
  obtain ⟨b', hb, hyb⟩ := up m (max n m) (le_max_right _ _) b
  rw [← hya, ← hyb]
  exact eq_of_same_stage f ι t y t0 tS ker hy _ a' b' (by rw [ha, hb, h])

theorem exists_lift_of_surj_ker
    (hι : ∀ n x, ι (n + 1) (f n x) = ι n x)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (surj : ∀ (m : ℕ) (v : Fin m → L), ∃ n, ∃ w : Fin m → G n, ∀ i, ι n (w i) = v i)
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    {T : Type} [CommRing T] (y : ∀ n, G n →+* T) (hy : ∀ n x, y (n + 1) (f n x) = y n x) :
    ∃ z : L →+* T, ∀ n x, z (ι n x) = y n x := by
  classical
  have key := eq_of_iota_eq f ι t y hι t0 tS ker hy
  have rep : ∀ l : L, ∃ n, ∃ a : G n, ι n a = l := fun l => by
    obtain ⟨n, w, hw⟩ := surj 1 (fun _ => l)
    exact ⟨n, w 0, hw 0⟩
  choose r s hs using rep
  let z : L → T := fun l => y (r l) (s l)
  have hz : ∀ n x, z (ι n x) = y n x := fun n x => key _ _ _ _ (hs _)
  have two : ∀ l₁ l₂ : L, ∃ n, ∃ a b : G n, ι n a = l₁ ∧ ι n b = l₂ := fun l₁ l₂ => by
    obtain ⟨n, w, hw⟩ := surj 2 ![l₁, l₂]
    exact ⟨n, w 0, w 1, hw 0, hw 1⟩
  refine ⟨{ toFun := z, map_one' := ?_, map_zero' := ?_, map_mul' := ?_, map_add' := ?_ }, hz⟩
  · have := hz 0 1
    simpa using this
  · intro l₁ l₂
    obtain ⟨n, a, b, rfl, rfl⟩ := two l₁ l₂
    rw [← map_mul, hz, hz, hz, map_mul]
  · have := hz 0 0
    simpa using this
  · intro l₁ l₂
    obtain ⟨n, a, b, rfl, rfl⟩ := two l₁ l₂
    rw [← map_add (f := _), hz, hz, hz, map_add (f := _)]

end GlobalTheory.CompanionTheory.ColimLift
end

section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.LatticeCount

theorem summable_inv_one_add_sq_int :
    Summable (fun m : ℤ => ((1 : ℝ) + (m : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually h ?_
  have hfin : ({0} : Set ℤ).Finite := Set.finite_singleton 0
  refine Filter.mem_cofinite.2 (hfin.subset ?_)
  intro m hm
  by_contra h0
  have h0' : m ≠ 0 := by simpa using h0
  apply hm
  have hm0 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast h0'
    positivity
  have hpos : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
  show ‖((1 : ℝ) + (m : ℝ) ^ 2)⁻¹‖ ≤ 1 / (m : ℝ) ^ 2
  rw [Real.norm_of_nonneg (inv_nonneg.2 hpos.le), one_div]
  exact inv_anti₀ hm0 (by linarith)

theorem summable_prod_inv_one_add_sq (d : ℕ) :
    Summable (fun n : Fin d → ℤ => ∏ k, ((1 : ℝ) + (n k : ℝ) ^ 2)⁻¹) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
    have h2 := summable_inv_one_add_sq_int.mul_of_nonneg ih
      (fun m => by positivity) (fun n => Finset.prod_nonneg (fun k _ => by positivity))
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff]
    refine h2.congr ?_
    intro x
    simp [Fin.prod_univ_succ, Fin.consEquiv]
    exact mul_comm _ _

theorem summable_of_lattice_decay (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ)
    (hf : Function.Injective f) (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hC : ∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C)
    (hint : ∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) : Summable w := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let S := {i // w i ≠ 0}
  choose n hn using fun i : S => hint i.1 i.2
  have hinj : Function.Injective n := by
    intro a b hab
    apply Subtype.ext
    apply hf
    funext k
    have h1 := hn a k
    have h2 := hn b k
    rw [hab] at h1
    exact mul_left_cancel₀ hNpos.ne' (h1.trans h2.symm)
  have hg := ((summable_prod_inv_one_add_sq d).comp_injective hinj).mul_left (((N : ℝ) ^ 2) ^ d * C)
  have hbound : ∀ a : S, ‖w a.1‖ ≤ ((N : ℝ) ^ 2) ^ d * C *
      ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)⁻¹ := by
    intro a
    have hle : ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) ≤
        ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) := by
      have : ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) =
          ∏ k : Fin d, ((N : ℝ) ^ 2 * (1 + f a.1 k ^ 2)) := by
        rw [Finset.prod_mul_distrib]; simp
      rw [this]
      refine Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => ?_)
      rw [← hn a k]
      have : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hpos : (0 : ℝ) < ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) :=
      Finset.prod_pos (fun k _ => by positivity)
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖w a.1‖ * ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)
        ≤ ‖w a.1‖ * (((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ((N : ℝ) ^ 2) ^ d * (‖w a.1‖ * ∏ k, (1 + f a.1 k ^ 2)) := by ring
      _ ≤ ((N : ℝ) ^ 2) ^ d * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hsub : Summable (w ∘ (Subtype.val : S → ι)) :=
    Summable.of_norm_bounded hg hbound
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).1 hsub
  intro x hx
  by_contra h0
  exact hx ⟨⟨x, h0⟩, rfl⟩

end GlobalTheory.CompanionTheory.LatticeCount
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothParam

variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def pderiv (H : P × Y → F) : P × Y → (P →L[ℝ] F) :=
  fun z => fderiv ℝ (fun q => H (q, z.2)) z.1

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
lemma hasFDerivAt_partial {H : P × Y → F} (hH : Differentiable ℝ H) (p : P) (y : Y) :
    HasFDerivAt (fun q => H (q, y))
      ((fderiv ℝ H (p, y)).comp (ContinuousLinearMap.inl ℝ P Y)) p :=
  (hH (p, y)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p y)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
lemma pderiv_eq {H : P × Y → F} (hH : Differentiable ℝ H) :
    pderiv H = fun z => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P Y) := by
  funext z
  exact (hasFDerivAt_partial hH z.1 z.2).fderiv

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
lemma contDiff_pderiv {H : P × Y → F} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (pderiv H) := by
  rw [pderiv_eq (hH.differentiable (by simp))]
  have h1 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  exact h1.clm_comp contDiff_const

omit [FiniteDimensional ℝ P] [NormedSpace ℝ P] [FiniteDimensional ℝ Y] [NormedSpace ℝ Y] in
lemma integrable_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) {H : P × Y → F} (hH : Continuous H) (p : P) :
    Integrable (fun x => u x • H (p, ψ x)) ν := by
  obtain ⟨C, hC⟩ := (isCompact_singleton.prod hK).exists_bound_of_continuousOn
    (f := H) (s := {p} ×ˢ K) hH.continuousOn
  have hc : Continuous fun y => H (p, y) := hH.comp (by fun_prop)
  have meas : AEStronglyMeasurable (fun x => u x • H (p, ψ x)) ν :=
    hu.aestronglyMeasurable.smul (hc.comp_aestronglyMeasurable hψ)
  refine (hu.norm.mul_const C).mono' meas ?_
  filter_upwards [hψK] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC _ ⟨rfl, hx⟩) (norm_nonneg _)

theorem hasFDerivAt_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) [CompleteSpace F] {H : P × Y → F} (hH : ContDiff ℝ ∞ H) (p₀ : P) :
    HasFDerivAt (fun p => ∫ x, u x • H (p, ψ x) ∂ν)
      (∫ x, u x • pderiv H (p₀, ψ x) ∂ν) p₀ := by
  have hd : Differentiable ℝ H := hH.differentiable (by simp)
  have hc' : Continuous (pderiv H) := (contDiff_pderiv hH).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hK).exists_bound_of_continuousOn
    (f := pderiv H) hc'.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p x => u x • H (p, ψ x)) (F' := fun p x => u x • pderiv H (p, ψ x))
    (bound := fun x => ‖u x‖ * C) (s := Metric.closedBall p₀ 1)
    (Metric.closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun p =>
      (integrable_weight hu hψ hK hψK hH.continuous p).aestronglyMeasurable
  · exact integrable_weight hu hψ hK hψK hH.continuous p₀
  · exact (integrable_weight hu hψ hK hψK hc' p₀).aestronglyMeasurable
  · filter_upwards [hψK] with x hx p hp
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ ⟨hp, hx⟩) (norm_nonneg _)
  · exact hu.norm.mul_const C
  · refine Eventually.of_forall fun x p _ => ?_
    have h1 : HasFDerivAt (fun q => H (q, ψ x)) (pderiv H (p, ψ x)) p :=
      ((hasFDerivAt_partial hd p (ψ x)).differentiableAt).hasFDerivAt
    exact h1.const_smul (u x)

theorem contDiff_weight_nat {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (H : P × Y → F),
      ContDiff ℝ ∞ H → ContDiff ℝ n (fun p => ∫ x, u x • H (p, ψ x) ∂ν) := by
  induction n with
  | zero =>
    intro F _ _ _ H hH
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun p =>
      (hasFDerivAt_weight hu hψ hK hψK hH p).continuousAt
  | succ n ih =>
    intro F _ _ _ H hH
    have hfd : fderiv ℝ (fun p => ∫ x, u x • H (p, ψ x) ∂ν)
        = fun p => ∫ x, u x • pderiv H (p, ψ x) ∂ν := by
      funext p
      exact (hasFDerivAt_weight hu hψ hK hψK hH p).fderiv
    have : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [this, contDiff_succ_iff_fderiv]
    refine ⟨fun p => (hasFDerivAt_weight hu hψ hK hψK hH p).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih (P →L[ℝ] F) (pderiv H) (contDiff_pderiv hH)

theorem contDiff_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) [CompleteSpace F] {H : P × Y → F} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p => ∫ x, u x • H (p, ψ x) ∂ν) :=
  contDiff_infty.2 fun n => contDiff_weight_nat hu hψ hK hψK n F H hH

theorem contDiff_integral_density (Ω P Y : Type) [MeasurableSpace Ω] [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (ν : Measure Ω) (w : Ω → ℂ) (ψ : Ω → Y) (K : Set Y)
    (hw : Integrable w ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (h : P × Y → ℂ) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p => ∫ x, h (p, ψ x) * w x ∂ν) ∧
      ∀ p v, fderiv ℝ (fun q => ∫ x, h (q, ψ x) * w x ∂ν) p v
        = ∫ x, fderiv ℝ (fun q => h (q, ψ x)) p v * w x ∂ν := by
  have hu₁ : Integrable (fun x => (w x).re) ν := hw.re
  have hu₂ : Integrable (fun x => (w x).im) ν := hw.im
  set h₂ : P × Y → ℂ := fun z => Complex.I * h z with hh₂def
  have hh₂ : ContDiff ℝ ∞ h₂ := contDiff_const.mul hh
  have hdec : ∀ (a b : ℂ), a * b = b.re • a + b.im • (Complex.I * a) := by
    intro a b
    apply Complex.ext <;> simp <;> ring
  have hsplit : (fun p => ∫ x, h (p, ψ x) * w x ∂ν)
      = fun p => (∫ x, (w x).re • h (p, ψ x) ∂ν) + ∫ x, (w x).im • h₂ (p, ψ x) ∂ν := by
    funext p
    rw [← integral_add (integrable_weight hu₁ hψ hK hψK hh.continuous p)
      (integrable_weight hu₂ hψ hK hψK hh₂.continuous p)]
    exact integral_congr_ae (Eventually.of_forall fun x => hdec _ _)
  refine ⟨?_, fun p v => ?_⟩
  · rw [hsplit]
    exact (contDiff_weight hu₁ hψ hK hψK hh).add (contDiff_weight hu₂ hψ hK hψK hh₂)
  · have hd : Differentiable ℝ h := hh.differentiable (by simp)
    have hD := (hasFDerivAt_weight hu₁ hψ hK hψK hh p).add
      (hasFDerivAt_weight hu₂ hψ hK hψK hh₂ p)
    have hfd := hD.fderiv
    have hi₁ := integrable_weight hu₁ hψ hK hψK (contDiff_pderiv hh).continuous p
    have hi₂ := integrable_weight hu₂ hψ hK hψK (contDiff_pderiv hh₂).continuous p
    have hp₂ : ∀ y, pderiv h₂ (p, y) v = Complex.I * pderiv h (p, y) v := by
      intro y
      have h1 : HasFDerivAt (fun q => h (q, y)) (pderiv h (p, y)) p :=
        ((hasFDerivAt_partial hd p y).differentiableAt).hasFDerivAt
      have h2 : HasFDerivAt (fun q => h₂ (q, y)) (Complex.I • pderiv h (p, y)) p := by
        exact h1.const_smul Complex.I
      have : pderiv h₂ (p, y) = Complex.I • pderiv h (p, y) := h2.fderiv
      rw [this]; simp
    rw [hsplit]
    change fderiv ℝ ((fun p => ∫ x, (w x).re • h (p, ψ x) ∂ν) +
      (fun p => ∫ x, (w x).im • h₂ (p, ψ x) ∂ν)) p v = _
    rw [hfd, ContinuousLinearMap.add_apply, ContinuousLinearMap.integral_apply hi₁,
      ContinuousLinearMap.integral_apply hi₂,
      ← integral_add (hi₁.apply_continuousLinearMap v) (hi₂.apply_continuousLinearMap v)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.smul_apply]
    rw [hp₂]
    exact (hdec _ _).symm

end GlobalTheory.CompanionTheory.SmoothParam
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.HolFamily

theorem continuousOn_deriv_family (P : Type) [TopologicalSpace P] (U : Set ℂ) (hU : IsOpen U)
    (H : P → ℂ → ℂ) (hc : ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U))
    (hd : ∀ p, DifferentiableOn ℂ (H p) U) :
    ContinuousOn (fun q : P × ℂ => deriv (H q.1) q.2) (Set.univ ×ˢ U) := by
  rintro ⟨p0, z0⟩ ⟨-, hz0⟩
  simp only at hz0
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 hU z0 hz0
  have hR : 0 < e / 3 := by positivity
  set R := e / 3 with hRdef
  have hKU : Metric.closedBall z0 (2 * R) ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hball
    rw [hRdef]; linarith
  let K : Set ℂ := Metric.closedBall z0 (2 * R)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall z0 (2 * R))
  have hFc : Continuous (fun x : P × K => H x.1 x.2) := by
    have : Continuous (fun x : P × K => ((x.1, (x.2 : ℂ)) : P × ℂ)) := by fun_prop
    exact hc.comp_continuous this (fun x => ⟨Set.mem_univ _, hKU x.2.2⟩)
  let F : C(P × K, ℂ) := ⟨fun x => H x.1 x.2, hFc⟩
  let G : C(P, C(K, ℂ)) := F.curry
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hGc : Tendsto G (𝓝 p0) (𝓝 (G p0)) := G.continuous.tendsto p0
  have h1 : ∀ᶠ p in 𝓝 p0, dist (G p) (G p0) < ε / 2 * R / 2 :=
    (Metric.tendsto_nhds.1 hGc) _ (by positivity)
  have hdc : ContinuousAt (deriv (H p0)) z0 :=
    ((hd p0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)
  have h2 : ∀ᶠ z in 𝓝 z0, dist (deriv (H p0) z) (deriv (H p0) z0) < ε / 2 :=
    (Metric.tendsto_nhds.1 hdc) _ (by positivity)
  have h3 : ∀ᶠ z in 𝓝 z0, z ∈ Metric.ball z0 R := Metric.ball_mem_nhds z0 hR
  have h4 := h1.prod_nhds (h2.and h3)
  filter_upwards [nhdsWithin_le_nhds h4]
  rintro ⟨p, z⟩ ⟨hp, hz, hzR⟩
  simp only at hp hz hzR ⊢
  have hsub : Metric.closedBall z R ⊆ K := by
    intro w hw
    rw [Metric.mem_closedBall] at hw ⊢
    rw [Metric.mem_ball] at hzR
    have := dist_triangle w z z0
    linarith
  have hfd : DifferentiableOn ℂ (fun w => H p w - H p0 w) U := (hd p).sub (hd p0)
  have hzU : z ∈ U := hKU (hsub (Metric.mem_closedBall_self hR.le))
  have hnh : U ∈ 𝓝 z := hU.mem_nhds hzU
  have hderiv : deriv (fun w => H p w - H p0 w) z = deriv (H p) z - deriv (H p0) z :=
    deriv_fun_sub ((hd p).differentiableAt hnh) ((hd p0).differentiableAt hnh)
  have hbound : ∀ w ∈ Metric.sphere z R, ‖H p w - H p0 w‖ ≤ ε / 2 * R / 2 := by
    intro w hw
    have hwK : w ∈ K := hsub (Metric.sphere_subset_closedBall hw)
    have := ContinuousMap.dist_apply_le_dist (f := G p) (g := G p0) (⟨w, hwK⟩ : K)
    have h5 : dist (G p ⟨w, hwK⟩) (G p0 ⟨w, hwK⟩) = ‖H p w - H p0 w‖ := by
      rw [dist_eq_norm]; rfl
    rw [← h5]
    exact this.trans hp.le
  have hcauchy : ‖deriv (fun w => H p w - H p0 w) z‖ ≤ ε / 2 * R / 2 / R :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
      (hfd.diffContOnCl_ball (hsub.trans hKU)) hbound
  have hval : ε / 2 * R / 2 / R = ε / 4 := by field_simp; ring
  rw [hval, hderiv] at hcauchy
  calc dist (deriv (H p) z) (deriv (H p0) z0)
      ≤ dist (deriv (H p) z) (deriv (H p0) z) + dist (deriv (H p0) z) (deriv (H p0) z0) :=
        dist_triangle _ _ _
    _ < ε := by
        rw [dist_eq_norm (deriv (H p) z)]
        linarith

theorem continuousOn_iteratedDeriv_family :
    ∀ (P : Type) [TopologicalSpace P] (U : Set ℂ), IsOpen U → ∀ H : P → ℂ → ℂ,
      ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U) →
      (∀ p, DifferentiableOn ℂ (H p) U) →
        ∀ r : ℕ, ContinuousOn (fun q : P × ℂ => iteratedDeriv r (H q.1) q.2) (Set.univ ×ˢ U) := by
  intro P _ U hU H hc hd r
  have hdiff : ∀ (r : ℕ) (p : P), DifferentiableOn ℂ (iteratedDeriv r (H p)) U := by
    intro r p
    induction r with
    | zero => simpa [iteratedDeriv_zero] using hd p
    | succ r ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hU
  induction r with
  | zero => simpa [iteratedDeriv_zero] using hc
  | succ r ih =>
    simp only [iteratedDeriv_succ]
    exact continuousOn_deriv_family P U hU (fun p => iteratedDeriv r (H p)) ih (hdiff r)

end GlobalTheory.CompanionTheory.HolFamily
end
