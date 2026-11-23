module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.LocallyUniformLimit
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory

theorem continuous_of_map_add_mul_of_continuousAt_zero (ν : ℝ → ℂ)
    (hm : ∀ s t, ν (s + t) = ν s * ν t) (hc : ContinuousAt ν 0) : Continuous ν := by
  rw [continuous_iff_continuousAt]
  intro x
  have h1 : ν = fun y => ν x * ν (y - x) := by
    funext y
    rw [← hm]
    congr 1
    ring
  rw [h1]
  refine continuousAt_const.mul ?_
  have h2 : ContinuousAt (fun y : ℝ => y - x) x := by fun_prop
  exact ContinuousAt.comp (f := fun y : ℝ => y - x) (by simpa using hc) h2

theorem exists_hasDerivAt_zero_of_map_add_mul :
    ∀ ν : ℝ → ℂ, ν 0 = 1 → (∀ s t, ν (s + t) = ν s * ν t) → ContinuousAt ν 0 →
      ∃ a : ℂ, HasDerivAt ν a 0 := by
  intro ν h0 hm hc0
  have hc := continuous_of_map_add_mul_of_continuousAt_zero ν hm hc0
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, ν x with hF
  have hd : ∀ u, HasDerivAt F (ν u) u := fun u => (hc.deriv_integral ν 0 u ▸
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt.hasDerivAt)
  have hex : ∃ δ, F δ ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hz : F = fun _ => 0 := funext hne
    have h1 := hd 0
    rw [hz, h0] at h1
    exact one_ne_zero (h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ)))
  obtain ⟨δ, hδ⟩ := hex
  have key : ∀ t, ν t = (F (t + δ) - F t) / F δ := by
    intro t
    rw [eq_div_iff hδ]
    have e1 : F (t + δ) - F t = ∫ x in t..(t + δ), ν x := by
      simp only [hF]
      exact intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
    have e2 : ∫ x in t..(t + δ), ν x = ∫ x in (0:ℝ)..δ, ν (t + x) := by
      rw [intervalIntegral.integral_comp_add_left ν t, add_zero]
    rw [e1, e2]
    simp only [hm, hF]
    rw [intervalIntegral.integral_const_mul]
  have h1 : HasDerivAt (fun t => F (t + δ)) (ν (0 + δ)) 0 := (hd (0 + δ)).comp_add_const 0 δ
  refine ⟨(ν (0 + δ) - ν 0) / F δ, ?_⟩
  have h2 := (h1.sub (hd 0)).div_const (F δ)
  have h3 : ν = fun t => (F (t + δ) - F t) / F δ := funext key
  conv => arg 1; rw [h3]
  exact h2

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem hasDerivAt_diag_sum_prod_pairing
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hβ : ∀ q, (∀ x, β x q = 0) → q = 0)
    (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hM : ∀ x y, DifferentiableAt ℝ (fun t => M t x y) 0) :
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
      HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  classical
  set d := Module.finrank ℝ V
  let e : Module.Basis (Fin d) ℝ V := Module.finBasis ℝ V

  have hinj : Function.Injective β.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    exact hβ q (fun x => by simpa using LinearMap.congr_fun hq x)
  have hsurj : Function.Surjective β.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  choose q hq using fun i : Fin d => hsurj (e.coord i)
  have hqx : ∀ x i, β x (q i) = e.repr x i := by
    intro x i
    have := LinearMap.congr_fun (hq i) x
    simpa using this

  have hexp : ∀ x t, M t x x =
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := by
    intro x t
    conv_lhs => rw [← e.sum_repr x]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.mul_sum,
    Complex.real_smul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  let c : Fin d × Fin d → ℂ := fun p => deriv (fun t => M t (e p.1) (e p.2)) 0
  refine ⟨d * d, fun k => q (finProdFinEquiv.symm k).1, fun k => q (finProdFinEquiv.symm k).2,
    fun k => c (finProdFinEquiv.symm k), fun x => ?_⟩
  have hfun : (fun t => M t x x) = fun t =>
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := funext (hexp x)
  rw [hfun]
  have hd : HasDerivAt (fun t => ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j))
      (∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * c (i, j)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hM (e i) (e j)).hasDerivAt).const_mul _
  convert hd using 1
  simp only [hqx]
  rw [← Fintype.sum_prod_type']
  rw [← (finProdFinEquiv (m := d) (n := d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

theorem summable_nonneg_family_of_differentiableOn {ι : Type} (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ) (hc : ∀ i, 0 ≤ c i) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hser : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => (c i : ℂ) * z ^ n i) (R z))
    (x : ℝ) (hx0 : 0 ≤ x) (hxr : x < r) : Summable (fun i => c i * x ^ n i) := by
  have hr : 0 < r := lt_of_le_of_lt hx0 hxr
  set t0 : ℝ := ε / 2 with ht0
  have ht0pos : 0 < t0 := by positivity
  have ht0ε : t0 < ε := by linarith
  have hnt0 : ‖(t0 : ℂ)‖ = t0 := by simp [abs_of_pos ht0pos]
  have hsum0 : Summable (fun i => c i * t0 ^ n i) := by
    have h := (hser (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable
    have e : (fun i => (c i : ℂ) * (t0 : ℂ) ^ n i) = fun i => ((c i * t0 ^ n i : ℝ) : ℂ) := by
      funext i; push_cast; rfl
    rw [e] at h
    exact Complex.summable_ofReal.mp h
  have hfib : ∀ m : ℕ, Summable (fun i : n ⁻¹' {m} => c i) := by
    intro m
    have h1 := (hsum0.subtype (fun i => n i = m)).mul_right (t0 ^ m)⁻¹
    refine h1.congr fun i => ?_
    have hi : n i.val = m := i.2
    simp only [Function.comp_apply]
    rw [hi, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0pos.ne'), mul_one]
  set C : ℕ → ℝ := fun m => ∑' i : n ⁻¹' {m}, c i with hC
  have hCnn : ∀ m, 0 ≤ C m := fun m => tsum_nonneg (fun i => hc i)
  have hgroup : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun m => (C m : ℂ) * z ^ m) (R z) := by
    intro z hz1 hz2
    refine ((hser z hz1 hz2).tsum_fiberwise n).congr_fun fun m => ?_
    have e1 : (∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ n i) = ∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ m :=
      tsum_congr fun i => by rw [show n i = m from i.2]
    rw [e1, tsum_mul_right, hC, Complex.ofReal_tsum]
  have hCt0 : Summable (fun m => C m * t0 ^ m) := by
    have h := (hgroup (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable
    have e : (fun m => (C m : ℂ) * (t0 : ℂ) ^ m) = fun m => ((C m * t0 ^ m : ℝ) : ℂ) := by
      funext m; push_cast; rfl
    rw [e] at h
    exact Complex.summable_ofReal.mp h
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => (C m : ℂ)) with hq
  have hqapply : ∀ (m : ℕ) (z : ℂ), q m (fun _ => z) = (C m : ℂ) * z ^ m := by
    intro m z; rw [hq, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  set t0n : NNReal := ⟨t0, ht0pos.le⟩ with ht0n
  have hrad : (t0n : ENNReal) ≤ q.radius := by
    refine q.le_radius_of_bound (∑' m, C m * t0 ^ m) fun m => ?_
    rw [show ((t0n : ℝ)) = t0 from rfl]
    have hn : ‖q m‖ = C m := by
      rw [hq, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hCnn m)]
    rw [hn]
    exact hCt0.le_tsum m (fun j _ => mul_nonneg (hCnn j) (pow_nonneg ht0pos.le _))
  have hradpos : 0 < q.radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (NNReal.coe_pos.mp (show (0:ℝ) < (t0n : ℝ) from ht0pos))) hrad
  have hqball := q.hasFPowerSeriesOnBall hradpos
  have hRan : AnalyticAt ℂ R 0 := hR.analyticAt (Metric.ball_mem_nhds 0 hr)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), R z = q.sum z := by
    apply Eventually.frequently
    have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) ε :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hb, self_mem_nhdsWithin] with z hz hz0
    have hz0' : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [mem_ball_zero_iff] at hz
    rw [FormalMultilinearSeries.sum]
    simp_rw [hqapply]
    exact ((hgroup z hz0' hz).tsum_eq).symm
  have hev := (hRan.frequently_eq_iff_eventually_eq hqball.analyticAt).mp hfreq
  have hRq : HasFPowerSeriesAt R q 0 := hqball.hasFPowerSeriesAt.congr (hev.mono fun z h => h.symm)
  set ρ : ℝ := (x + r) / 2 with hρ
  have hρpos : 0 < ρ := by linarith
  set ρn : NNReal := ⟨ρ, hρpos.le⟩ with hρn
  have hcl : DifferentiableOn ℂ R (Metric.closedBall 0 (ρn : ℝ)) :=
    hR.mono (Metric.closedBall_subset_ball (by show ρ < r; linarith))
  have hp := hcl.hasFPowerSeriesOnBall (by exact_mod_cast hρpos)
  have hpq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hRq
  rw [hpq] at hp
  have hxn : ‖(x : ℂ)‖₊ < ρn := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    show x < ρ
    linarith
  have hxmem : (x : ℂ) ∈ Metric.eball (0 : ℂ) (ρn : ENNReal) := by
    show edist (x : ℂ) 0 < ρn
    rw [edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast hxn
  have hsx := (hp.hasSum hxmem).summable
  simp_rw [hqapply] at hsx
  have hCx : Summable (fun m => C m * x ^ m) := by
    have e : (fun m => (C m : ℂ) * (x : ℂ) ^ m) = fun m => ((C m * x ^ m : ℝ) : ℂ) := by
      funext m; push_cast; rfl
    rw [e] at hsx
    exact Complex.summable_ofReal.mp hsx
  rw [← (Equiv.sigmaFiberEquiv n).summable_iff]
  refine (summable_sigma_of_nonneg fun p => ?_).mpr ⟨fun m => ?_, ?_⟩
  · exact mul_nonneg (hc _) (pow_nonneg hx0 _)
  · refine ((hfib m).mul_right (x ^ m)).congr fun i => ?_
    simp [Equiv.sigmaFiberEquiv, show n i = m from i.2]
  · refine hCx.congr fun m => ?_
    have e1 : (∑' i : {i // n i = m}, ((fun i => c i * x ^ n i) ∘ (Equiv.sigmaFiberEquiv n))
        ⟨m, i⟩) = ∑' i : n ⁻¹' {m}, c i * x ^ m :=
      tsum_congr fun i => by simp [Equiv.sigmaFiberEquiv, show n i = m from i.2]
    rw [e1, tsum_mul_right]

end GlobalTheory
end

section

open Metric Filter Topology

namespace GlobalTheory

theorem hasSum_of_dominated_of_eq_near_zero {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ)
    (hbc : ∀ i, ‖b i‖ ≤ c i)
    (hc : ∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hnear : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) :
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) := by
  intro z hz
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hbound : ∀ i (w : ℂ), ‖b i * w ^ n i‖ ≤ c i * ‖w‖ ^ n i := by
    intro i w
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hbc i) (pow_nonneg (norm_nonneg w) _)
  have hsum : ∀ w : ℂ, ‖w‖ < r → Summable (fun i => b i * w ^ n i) := by
    intro w hw
    exact Summable.of_norm_bounded (hc ‖w‖ (norm_nonneg w) hw) (fun i => hbound i w)
  let F : ℂ → ℂ := fun w => ∑' i, b i * w ^ n i
  have hFd : DifferentiableOn ℂ F (ball 0 r) := by
    intro w hw
    have hw' : ‖w‖ < r := by simpa using hw
    obtain ⟨s, hws, hsr⟩ := exists_between hw'
    have hs0 : 0 ≤ s := le_trans (norm_nonneg w) hws.le
    have hd : DifferentiableOn ℂ F (ball 0 s) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (u := fun i => c i * s ^ n i) (hc s hs0 hsr)
        (fun i => ?_) isOpen_ball (fun i v hv => ?_)
      · exact ((differentiable_const _).mul (differentiable_id.pow _)).differentiableOn
      · refine (hbound i v).trans ?_
        have hv' : ‖v‖ < s := by simpa using hv
        have hci : 0 ≤ c i := (norm_nonneg _).trans (hbc i)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hv'.le _) hci
    exact (hd.differentiableAt (isOpen_ball.mem_nhds (by simpa using hws))).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F (ball 0 r) := hFd.analyticOnNhd isOpen_ball
  have hRa : AnalyticOnNhd ℂ R (ball 0 r) := hR.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ w in 𝓝[≠] (0:ℂ), F w = R w := by
    apply Eventually.frequently
    have h1 : ∀ᶠ w in 𝓝 (0:ℂ), w ∈ ball (0:ℂ) ε := isOpen_ball.mem_nhds (mem_ball_self hε)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with w hw hw0
    have hw0' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hwε : ‖w‖ < ε := by simpa using hw
    exact (hnear w hw0' hwε).tsum_eq
  have heq := hFa.eqOn_of_preconnected_of_frequently_eq hRa (convex_ball (0:ℂ) r).isPreconnected
    (mem_ball_self hr) hfreq
  have hzb : z ∈ ball (0:ℂ) r := by simpa using hz
  rw [← heq hzb]
  exact (hsum z hz).hasSum

theorem hasSum_of_dominated_of_eq_near_zero' : ∀ {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ) (R : ℂ → ℂ) (r ε : ℝ), (∀ i, ‖b i‖ ≤ c i) →
    (∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) → 0 < ε →
    DifferentiableOn ℂ R (Metric.ball 0 r) →
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) →
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) :=
  fun b c n R r ε h1 h2 h3 h4 h5 => hasSum_of_dominated_of_eq_near_zero b c n R r ε h1 h2 h3 h4 h5

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem schwartz_gaussian_form_re_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ) (hg : g ≠ 0)
    (hform : ∀ x, g x = g 0 * Complex.exp (M x x)) (v : V) (hv : v ≠ 0) : (M v v).re < 0 := by
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    ext x
    rw [hform x, h0]; simp
  by_contra hre
  push_neg at hre
  obtain ⟨C, hC, hdec⟩ := g.decay 1 0
  have hgn : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set s : ℝ := (C + 1) / (‖v‖ * ‖g 0‖) with hs
  have hspos : 0 < s := by positivity
  have key := hdec (s • v)
  rw [norm_iteratedFDeriv_zero, pow_one, hform (s • v)] at key
  have hM : M (s • v) (s • v) = ((s ^ 2 : ℝ) : ℂ) * M v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [Complex.real_smul]; push_cast; ring
  rw [hM, norm_mul, Complex.norm_exp] at key
  have hexp : 1 ≤ Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re) := by
    apply Real.one_le_exp
    rw [Complex.re_ofReal_mul]
    positivity
  have hnorm : ‖s • v‖ = s * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  rw [hnorm] at key
  have h1 : s * ‖v‖ * ‖g 0‖ = C + 1 := by
    rw [hs]; field_simp
  have h2 : s * ‖v‖ * ‖g 0‖ ≤ s * ‖v‖ * (‖g 0‖ * Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  linarith

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem complex_mul_conj_eq_polarization (a b : ℂ) :
    a * starRingEnd ℂ b = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * ((‖a + Complex.I ^ k * b‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Complex.sq_norm]
  apply Complex.ext <;>
    simp [Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem schwartz_integrable_sq_norm_of_addHaar {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (h : SchwartzMap V ℂ) :
    Integrable (fun x => ‖h x‖ ^ 2) μ := by
  have := (h.memLp 2 μ).integrable_norm_pow (by norm_num)
  simpa using this

theorem schwartz_integral_mul_conj_eq_polarization {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (u v : SchwartzMap V ℂ) :
    ∫ x, u x * starRingEnd ℂ (v x) ∂μ = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * ((∫ x, ‖(u + (Complex.I ^ k) • v) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp_rw [complex_mul_conj_eq_polarization (u _)]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    rw [← integral_complex_ofReal]
    simp [smul_eq_mul]
  · intro k _
    refine Integrable.const_mul ?_ _
    have := (schwartz_integrable_sq_norm_of_addHaar μ (u + (Complex.I ^ k) • v)).ofReal (𝕜 := ℂ)
    simpa using this

theorem schwartz_L2_isometry_preserves_inner {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ) :
    (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ f g : SchwartzMap V ℂ, ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  intro hT f g
  rw [schwartz_integral_mul_conj_eq_polarization, schwartz_integral_mul_conj_eq_polarization]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul, ← map_add (f := _), hT]

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem conv_right_continuous {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (m : Measure H) (α : H → ℂ) (hα : Integrable α m) (φ : G → ℂ) (hφ : Continuous φ)
    (B : ℝ) (hB : ∀ g, ‖φ g‖ ≤ B) :
    Continuous (fun x => ∫ h, α h * φ (x * (h : G)) ∂m) := by
  refine continuous_of_dominated (bound := fun h => B * ‖α h‖) ?_ ?_ ?_ ?_
  · intro x
    refine hα.aestronglyMeasurable.mul ?_
    exact (hφ.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall (fun h => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · exact hα.norm.const_mul B
  · refine Filter.Eventually.of_forall (fun h => ?_)
    exact continuous_const.mul (hφ.comp (continuous_id.mul continuous_const))

end GlobalTheory
end
