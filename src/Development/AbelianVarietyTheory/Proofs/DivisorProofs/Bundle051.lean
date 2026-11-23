module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory

theorem integral_hasSum_eq_integral_indicator_hasSum :
    ∀ {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) (k : ι → X → ℂ),
      (∀ i, Integrable (k i) μ) → {i | ∫ x, ‖k i x‖ ∂μ ≠ 0}.Finite →
      ∀ (p : Set ι) (K Kp : X → ℂ), (∀ x, HasSum (fun i => k i x) (K x)) →
      (∀ x, HasSum (fun i => p.indicator (fun i => k i x) i) (Kp x)) →
      (∀ i ∉ p, ∫ x, k i x ∂μ = 0) → ∫ x, K x ∂μ = ∫ x, Kp x ∂μ := by
  intro X ι _ _ μ k hk hfin p K Kp hK hKp h0
  classical
  set s := hfin.toFinset with hs
  have hnull : ∀ i ∉ s, k i =ᵐ[μ] 0 := by
    intro i hi
    have hi' : ∫ x, ‖k i x‖ ∂μ = 0 := by
      by_contra h
      exact hi (by simpa [hs] using h)
    have := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (k i x)) (hk i).norm).1 hi'
    filter_upwards [this] with x hx
    simpa using hx
  have hall : ∀ᵐ x ∂μ, ∀ i, i ∉ s → k i x = 0 := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ∈ s
    · exact Filter.Eventually.of_forall (fun x h => absurd hi h)
    · filter_upwards [hnull i hi] with x hx _
      exact hx
  have hKae : K =ᵐ[μ] fun x => ∑ i ∈ s, k i x := by
    filter_upwards [hall] with x hx
    exact (hK x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => hx i hi))
  have hKpae : Kp =ᵐ[μ] fun x => ∑ i ∈ s, p.indicator (fun i => k i x) i := by
    filter_upwards [hall] with x hx
    refine (hKp x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => ?_))
    by_cases hp : i ∈ p
    · simp [Set.indicator_of_mem hp, hx i hi]
    · simp [Set.indicator_of_notMem hp]
  have hind : ∀ i, (fun x => p.indicator (fun i => k i x) i) =
      if i ∈ p then k i else fun _ => 0 := by
    intro i
    by_cases hp : i ∈ p
    · funext x; simp [Set.indicator_of_mem hp, hp]
    · funext x; simp [Set.indicator_of_notMem hp, hp]
  rw [integral_congr_ae hKae, integral_congr_ae hKpae,
    MeasureTheory.integral_finsetSum s (fun i _ => hk i),
    MeasureTheory.integral_finsetSum s (fun i _ => by
      rw [hind i]; split_ifs
      · exact hk i
      · exact integrable_zero _ _ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hind i]
  split_ifs with hp
  · rfl
  · simp [h0 i hp]

end GlobalTheory
end

section

open MeasureTheory
open scoped ContDiff

namespace GlobalTheory


open MeasureTheory in
open scoped ContDiff in
theorem _root_.GlobalTheory.exists_average_fixed_approx_of_fixed :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (H U : Subgroup G), IsOpen (U : Set G) → (∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H) → ∀ v : K, (∀ k ∈ H, ρ k v = v) → ∀ ε : ℝ, 0 < ε → ∃ η : G → ℂ, Continuous η ∧ HasCompactSupport η ∧ (∀ k ∈ H, ρ k (∫ y, η y • ρ y v ∂μ) = ∫ y, η y • ρ y v ∂μ) ∧ ‖v - ∫ y, η y • ρ y v ∂μ‖ < ε := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ρ _ hcont H U hU hconj v hv ε hε
  set W : Set G := (U : Set G) ∩ {y | ‖ρ y v - v‖ < ε / 2} with hW
  have hWo : IsOpen W :=
    hU.inter (isOpen_lt ((hcont v).sub continuous_const).norm continuous_const)
  have h1W : (1 : G) ∈ W := ⟨U.one_mem, by simp [half_pos hε]⟩
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hWo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1W)
  have hf1' : f 1 = 1 := by simpa using hf1 (Set.mem_singleton (1 : G))
  have hfpos : 0 < ∫ y, f y ∂μ :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc (fun x => (hfI x).1)
      (x := 1) (by rw [hf1']; norm_num)
  set c := ∫ y, f y ∂μ with hc
  set η : G → ℂ := fun y => ((c⁻¹ * f y : ℝ) : ℂ) with hηdef
  have hηc : Continuous η :=
    Complex.continuous_ofReal.comp (continuous_const.mul f.continuous)
  have hηs : HasCompactSupport η :=
    hfc.comp_left (g := fun r : ℝ => ((c⁻¹ * r : ℝ) : ℂ)) (by simp)
  have hηW : ∀ y, η y ≠ 0 → y ∈ W := by
    intro y hy
    by_contra hyW
    exact hy (by simp [hηdef, hf0 hyW])
  have hηI : Integrable η μ := hηc.integrable_of_hasCompactSupport hηs
  have hint : Integrable (fun y => η y • ρ y v) μ :=
    (hηc.smul (hcont v)).integrable_of_hasCompactSupport hηs.smul_right
  have hnormη : (fun y => ‖η y‖) = fun y => c⁻¹ * f y := by
    funext y
    simp only [hηdef, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (inv_nonneg.2 hfpos.le) (hfI y).1)
  have hη1 : ∫ y, η y ∂μ = 1 := by
    simp only [hηdef]
    rw [integral_complex_ofReal, integral_const_mul, inv_mul_cancel₀ hfpos.ne', Complex.ofReal_one]
  refine ⟨η, hηc, hηs, ?_, ?_⟩
  · intro k hk
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [map_smul]
    by_cases hy : η y = 0
    · simp [hy]
    have hyU : y ∈ U := (hηW y hy).1
    congr 1
    have hky : k * y = y * (y⁻¹ * k * y) := by group
    calc ρ k (ρ y v) = ρ (k * y) v := by rw [map_mul]; rfl
      _ = ρ (y * (y⁻¹ * k * y)) v := by rw [hky]
      _ = ρ y (ρ (y⁻¹ * k * y) v) := by rw [map_mul]; rfl
      _ = ρ y v := by rw [hv _ (hconj y hyU k hk)]
  · have hsplit : v - ∫ y, η y • ρ y v ∂μ = ∫ y, η y • (v - ρ y v) ∂μ := by
      simp_rw [smul_sub]
      rw [integral_sub (hηI.smul_const v) hint, integral_smul_const, hη1, one_smul]
    rw [hsplit]
    calc ‖∫ y, η y • (v - ρ y v) ∂μ‖ ≤ ∫ y, ‖η y‖ * (ε / 2) ∂μ := by
          refine norm_integral_le_of_norm_le (hηI.norm.mul_const _)
            (Filter.Eventually.of_forall fun y => ?_)
          rw [norm_smul]
          by_cases hy : η y = 0
          · simp [hy]
          exact mul_le_mul_of_nonneg_left
            (by rw [norm_sub_rev]; exact (hηW y hy).2.le) (norm_nonneg _)
      _ = ε / 2 := by
          rw [integral_mul_const, hnormη, integral_const_mul, inv_mul_cancel₀ hfpos.ne', one_mul]
      _ < ε := half_lt_self hε

end GlobalTheory
end

section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_equiv_euclidean_pi_mul_norm_sq_eq_re (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) :
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  classical
  let B : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ (fun x y => (Q x y).re)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  let q : QuadraticForm ℝ V := B.toQuadraticMap
  have hq : ∀ x, q x = (Q x x).re := fun x => rfl
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares q
  have he : ∀ x, ∑ i, w i * (e x i * e x i) = (Q x x).re := by
    intro x
    have := e.map_app x
    rw [QuadraticMap.weightedSumSquares_apply] at this
    simpa [hq] using this
  have hw : ∀ i, 0 < w i := by
    intro i
    have h1 := he (e.symm (Pi.single i 1))
    have h2 : e (e.symm (Pi.single i 1)) = Pi.single i 1 := e.toLinearEquiv.apply_symm_apply _
    have hne : e.symm (Pi.single i 1) ≠ 0 := by
      intro h
      rw [h, map_zero] at h2
      have := congrFun h2 i
      simp at this
    rw [h2, Finset.sum_eq_single i (by intro j _ hj; simp [hj]) (by simp)] at h1
    have h3 := hQ (e.symm (Pi.single i 1))
    have h4 : 0 < c * ‖e.symm (Pi.single i 1)‖ ^ 2 := by
      have := norm_pos_iff.mpr hne
      positivity
    simp at h1
    linarith
  have hs : ∀ i, Real.sqrt (w i / Real.pi) ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (div_pos (hw i) Real.pi_pos)).ne'
  let D : (Fin (Module.finrank ℝ V) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearEquiv.piCongrRight fun i =>
      LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (w i / Real.pi)) (hs i)
  let A : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    (e.toLinearEquiv.trans D).trans (WithLp.linearEquiv 2 ℝ _).symm
  have hA : ∀ x i, A x i = Real.sqrt (w i / Real.pi) * e x i := fun x i => rfl
  refine ⟨A.toContinuousLinearEquiv, fun x => ?_⟩
  rw [← he, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (A.toContinuousLinearEquiv x) i = Real.sqrt (w i / Real.pi) * e x i := hA x i
  rw [this, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (div_pos (hw i) Real.pi_pos).le]
  have := Real.pi_pos.ne'
  field_simp

end GlobalTheory
end

section

noncomputable section

open NumberField

namespace GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

def hmon (n : ℤ) (z : ℂ) : ℂ := if 0 ≤ n then (starRingEnd ℂ z) ^ n.toNat else z ^ (-n).toNat

def gauss (n : I → ℤ) (w : I → ℂ) : ℂ :=
  ∏ i, hmon (n i) (w i) * Complex.exp ((-2 * Real.pi * ‖w i‖ ^ 2 : ℝ) : ℂ)

def dil (y : I → ℝ) (v : I → ℂ) : I → ℂ := fun i => (Real.exp (y i / 2) : ℂ) * v i

def theta {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (y : I → ℝ) : ℂ :=
  ∑' j, a j * gauss n (dil y (e j))

def emb {K : Type} [Field K] (φ : I → K →+* ℂ) (α : K) : I → ℂ := fun i => φ i α

def ulog {K : Type} [Field K] [NumberField K] (φ : I → K →+* ℂ) (u : (𝓞 K)ˣ) : I → ℝ :=
  fun i => Real.log (‖φ i ((u : 𝓞 K) : K)‖ ^ 2)

theorem hmon_zero {n : ℤ} (hn : n ≠ 0) : hmon n 0 = 0 := by
  unfold hmon
  split_ifs with h
  · rw [map_zero]; exact zero_pow (by omega)
  · exact zero_pow (by omega)

theorem gauss_zero {n : I → ℤ} (hn : ∃ i, n i ≠ 0) : gauss n 0 = 0 := by
  obtain ⟨i, hi⟩ := hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hmon_zero hi])

theorem norm_hmon (n : ℤ) (z : ℂ) : ‖hmon n z‖ = ‖z‖ ^ n.natAbs := by
  unfold hmon
  split_ifs with h
  · rw [norm_pow, Complex.norm_conj]; congr 1; omega
  · rw [norm_pow]; congr 1; omega

end GlobalTheory.HeckeTheta
end
end

section

noncomputable section

open NumberField

namespace GlobalTheory.HeckeStrip

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

def wt (φ : I → K →+* ℂ) (n : I → ℤ) (α : K) : ℂ :=
  ∏ i, (φ i α / ((‖φ i α‖ : ℝ) : ℂ)) ^ (-n i)

def pval (F : 𝓞 K → ℂ) (φ : I → K →+* ℂ) (n : I → ℤ) (J : Ideal (𝓞 K)) [J.IsPrincipal] : ℂ :=
  F (Submodule.IsPrincipal.generator J) * wt φ n ((Submodule.IsPrincipal.generator J : 𝓞 K) : K)

def pSeries (F : 𝓞 K → ℂ) (φ : I → K →+* ℂ) (n : I → ℤ) (s : ℂ) : ℂ :=
  ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal},
    (haveI := J.2.2; pval F φ n J.1) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)

theorem wt_mul (φ : I → K →+* ℂ) (n : I → ℤ) (a b : K) : wt φ n (a * b) = wt φ n a * wt φ n b := by
  unfold wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_zpow]

theorem norm_wt (φ : I → K →+* ℂ) (n : I → ℤ) {a : K} (ha : a ≠ 0) : ‖wt φ n a‖ = 1 := by
  unfold wt
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  have h : φ i a ≠ 0 := (map_ne_zero _).2 ha
  rw [norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 h), one_zpow]

end GlobalTheory.HeckeStrip
end
end

section

open Filter Topology

namespace GlobalTheory

lemma intMatrix_smul_sum_norm_le {m g : ℕ} (M : Fin m → Fin m → ℤ) (x y : Fin m → Fin g → ℂ)
    (h : ∀ j, y j = ∑ i, M j i • x i) :
    ‖y‖ ≤ (∑ j, ∑ i, ‖M j i‖) * ‖x‖ := by
  have hS : 0 ≤ ∑ j, ∑ i, ‖M j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hS (norm_nonneg x))).2 fun j => ?_
  rw [h j]
  calc ‖∑ i, M j i • x i‖ ≤ ∑ i, ‖M j i • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖M j i‖ * ‖x‖ := Finset.sum_le_sum fun i _ =>
        (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _))
    _ = (∑ i, ‖M j i‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j, ∑ i, ‖M j i‖) * ‖x‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun j => ∑ i, ‖M j i‖)
          (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _) (Finset.mem_univ j)) (norm_nonneg x)

theorem polyGrowth_spread_of_integral_monodromy : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ) (P Q : Fin m → Fin m → ℤ), (∀ s : ℂ, s.re < 0 → ∀ j, lam (s + 2 * Real.pi * Complex.I) j = ∑ i, P j i • lam s i) → (∀ s : ℂ, s.re < 0 → ∀ j, lam s j = ∑ i, Q j i • lam (s + 2 * Real.pi * Complex.I) i) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  intro g m lam C k P Q h1 h2 h3 R
  set τ : ℂ := 2 * Real.pi * Complex.I with hτ
  have hτre : τ.re = 0 := by simp [hτ]
  have hτim : τ.im = 2 * Real.pi := by simp [hτ]
  have hτn : ‖τ‖ = 2 * Real.pi := by simp [hτ, abs_of_pos Real.pi_pos]
  have hexp : ∀ s, Complex.exp (s + τ) = Complex.exp s := by
    intro s; rw [Complex.exp_add, hτ, Complex.exp_two_pi_mul_I, mul_one]
  have hSP : 0 ≤ ∑ j, ∑ i, ‖P j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  have hSQ : 0 ≤ ∑ j, ∑ i, ‖Q j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  set A : ℝ := 1 + ∑ j, ∑ i, ‖P j i‖ + ∑ j, ∑ i, ‖Q j i‖ with hA
  have hA1 : 1 ≤ A := by linarith
  have hPA : ∀ s : ℂ, s.re < 0 → ‖lam (s + τ)‖ ≤ A * ‖lam s‖ := fun s hs =>
    (intMatrix_smul_sum_norm_le P _ _ (h1 s hs)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hQA : ∀ s : ℂ, s.re < 0 → ‖lam s‖ ≤ A * ‖lam (s + τ)‖ := fun s hs =>
    (intMatrix_smul_sum_norm_le Q _ _ (h2 s hs)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  set B : ℝ := A * (1 + 2 * Real.pi) ^ k with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ (by linarith [Real.pi_pos]))
  have hgrow : ∀ s t : ℂ, ‖t‖ ≤ ‖s‖ + 2 * Real.pi →
      (1 + ‖t‖) ^ k ≤ (1 + 2 * Real.pi) ^ k * (1 + ‖s‖) ^ k := by
    intro s t h
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [norm_nonneg s, Real.pi_pos]
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have key : ∀ n : ℕ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 →
      |s.im| ≤ Real.pi + 2 * Real.pi * n → ‖lam s‖ ≤ max C 0 * B ^ n * (1 + ‖s‖) ^ k := by
    intro n
    induction n with
    | zero =>
      intro s hs he hi
      have hX : 0 ≤ (1 + ‖s‖) ^ k := by positivity
      calc ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := h3 s hs he (by simpa using hi)
        _ ≤ max C 0 * B ^ 0 * (1 + ‖s‖) ^ k := by
          rw [pow_zero, mul_one]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    | succ n ih =>
      intro s hs he hi
      have hX : 0 ≤ (1 + ‖s‖) ^ k := by positivity
      have hBn : 1 ≤ B ^ (n + 1) := one_le_pow₀ hB1
      by_cases hsm : |s.im| ≤ Real.pi
      · calc ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := h3 s hs he hsm
          _ ≤ max C 0 * B ^ (n + 1) * (1 + ‖s‖) ^ k := by
            apply mul_le_mul_of_nonneg_right _ hX
            calc C ≤ max C 0 := le_max_left _ _
              _ = max C 0 * 1 := (mul_one _).symm
              _ ≤ max C 0 * B ^ (n + 1) := mul_le_mul_of_nonneg_left hBn hM
      · push_neg at hsm
        have hn0 : (0 : ℝ) ≤ 2 * Real.pi * n := by positivity
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hi
        obtain ⟨hi1, hi2⟩ := abs_le.mp hi
        obtain ⟨t, hlt, htre, hte, htn, hti⟩ : ∃ t : ℂ, ‖lam s‖ ≤ A * ‖lam t‖ ∧ t.re = s.re ∧
            Complex.exp t = Complex.exp s ∧ ‖t‖ ≤ ‖s‖ + 2 * Real.pi ∧
            |t.im| ≤ Real.pi + 2 * Real.pi * n := by
          rcases lt_abs.mp hsm with hpos | hneg
          · refine ⟨s - τ, ?_, ?_, ?_, ?_, ?_⟩
            · have := hPA (s - τ) (by simp [Complex.sub_re, hτre, hs])
              rwa [sub_add_cancel] at this
            · simp [hτre]
            · have := hexp (s - τ); rw [sub_add_cancel] at this; exact this.symm
            · calc ‖s - τ‖ ≤ ‖s‖ + ‖τ‖ := norm_sub_le _ _
                _ = ‖s‖ + 2 * Real.pi := by rw [hτn]
            · rw [Complex.sub_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]
          · refine ⟨s + τ, hQA s hs, ?_, hexp s, ?_, ?_⟩
            · simp [hτre]
            · calc ‖s + τ‖ ≤ ‖s‖ + ‖τ‖ := norm_add_le _ _
                _ = ‖s‖ + 2 * Real.pi := by rw [hτn]
            · rw [Complex.add_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]
        have hIH := ih t (by rw [htre]; exact hs) (by rw [hte]; exact he) hti
        calc ‖lam s‖ ≤ A * ‖lam t‖ := hlt
          _ ≤ A * (max C 0 * B ^ n * (1 + ‖t‖) ^ k) :=
            mul_le_mul_of_nonneg_left hIH (by linarith)
          _ ≤ A * (max C 0 * B ^ n * ((1 + 2 * Real.pi) ^ k * (1 + ‖s‖) ^ k)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hgrow s t htn)
                (mul_nonneg hM (pow_nonneg (by linarith) n))) (by linarith)
          _ = max C 0 * B ^ (n + 1) * (1 + ‖s‖) ^ k := by rw [hB]; ring
  refine ⟨max C 0 * B ^ ⌈R / (2 * Real.pi)⌉₊, fun s hs he hi => key _ s hs he (hi.trans ?_)⟩
  have hc : R / (2 * Real.pi) ≤ (⌈R / (2 * Real.pi)⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ (by positivity)] at hc
  linarith [Real.pi_pos]

end GlobalTheory
end

section

open MeasureTheory

noncomputable section

namespace GlobalTheory.ConvSeries

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def wt (b c : ℝ) (h : E → ℂ) (a : E) : ℂ :=
  Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖a‖ ^ 2 : ℝ) : ℂ))

def innerC (a : E) : E →L[ℝ] ℂ := Complex.ofRealCLM ∘L innerSL ℝ a

def powForm (k : ℕ) (a : E) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ).compContinuousLinearMap fun _ => innerC a

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def coef (b c : ℝ) (h : E → ℂ) (k : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
  ∫ a, wt b c h a • powForm k a

def term (b c : ℝ) (h : E → ℂ) (k : ℕ) (y : E) : ℂ :=
  Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * (((2 * c) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
    coef b c h k (fun _ => y)

end GlobalTheory.ConvSeries
end
end
