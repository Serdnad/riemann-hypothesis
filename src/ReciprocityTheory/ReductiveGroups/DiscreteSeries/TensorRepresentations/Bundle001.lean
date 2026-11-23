module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Degree
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def antiE (E : Fin n → Fin n → Module.End ℂ M) : Fin n → Fin n → Module.End ℂ M :=
  fun a b => -E (Fin.rev b) (Fin.rev a)

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS

theorem moment_poly {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (Q : ℂ[X]) :
    ∑ i, u i * Q.eval (b i) = ∑ s, r s * Q.eval (a s) := by
  simp only [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc ∑ i, u i * (Q.coeff k * b i ^ k) = Q.coeff k * ∑ i, u i * b i ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = Q.coeff k * ∑ s, r s * a s ^ k := by rw [h k]
    _ = ∑ s, r s * (Q.coeff k * a s ^ k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem moment_fibre {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (p : ℂ) :
    ∑ i ∈ univ.filter (fun i => b i = p), u i = ∑ s ∈ univ.filter (fun s => a s = p), r s := by
  classical
  set S : Finset ℂ := (univ.image b ∪ univ.image a).erase p with hS
  have hne : (∏ s ∈ S, (p - s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  let Q : ℂ[X] := C (∏ s ∈ S, (p - s))⁻¹ * ∏ s ∈ S, (X - C s)
  have hQ : ∀ x, x ∈ univ.image b ∪ univ.image a → Q.eval x = if x = p then 1 else 0 := by
    intro x hx
    simp only [Q, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with hxp
    · subst hxp
      exact inv_mul_cancel₀ hne
    · rw [Finset.prod_eq_zero (i := x) (Finset.mem_erase.mpr ⟨hxp, hx⟩) (sub_self x), mul_zero]
  have e := moment_poly b u a r h Q
  rw [Finset.sum_filter, Finset.sum_filter]
  calc ∑ i, (if b i = p then u i else 0) = ∑ i, u i * Q.eval (b i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [hQ (b i) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp
    _ = ∑ s, r s * Q.eval (a s) := e
    _ = _ := Finset.sum_congr rfl fun s _ => by
          rw [hQ (a s) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp

variable {n : ℕ}

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

theorem tf_ge_abstract {n : ℕ} {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (HP H' : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))) (hH'c : IsClosed (H' : Set (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))))
    (hH'P : H' ≤ HP) (hH'st : ∀ g, ∀ v ∈ H', ρ g v ∈ H') (hH'0 : H' ≠ ⊥)
    (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (hrep : ∀ v ∈ HP, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v))
    {d' : ℝ} (hd' : 0 < d')
    (hschur : ∀ x ∈ H', ∀ v ∈ H', ∫ g, ‖inner ℂ x (ρ g v)‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖v‖ ^ 2 / d') :
    d' ≤ ∑ c, ‖w c‖ ^ 2 ∧ (∑ c, ‖w c‖ ^ 2 = d' → HP ≤ H') := by
  have : CompleteSpace H' := hH'c.completeSpace_coe
  set Pw : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) := fun c => H'.starProjection (w c) with hPw
  have hPwm : ∀ c, Pw c ∈ H' := fun c => H'.starProjection_apply_mem (w c)
  have horth : ∀ c, ∀ y ∈ H', inner ℂ (w c - Pw c) y = 0 := fun c y hy =>
    H'.starProjection_inner_eq_zero (w c) y hy
  have hinnerP : ∀ c, ∀ y ∈ H', inner ℂ (w c) y = inner ℂ (Pw c) y := fun c y hy => by
    have := horth c y hy
    rwa [inner_sub_left, sub_eq_zero] at this
  have hpyth : ∀ c, ‖w c‖ ^ 2 = ‖Pw c‖ ^ 2 + ‖w c - Pw c‖ ^ 2 := fun c => by
    have h0 : inner ℂ (Pw c) (w c - Pw c) = 0 := by
      rw [← inner_conj_symm, horth c _ (hPwm c), map_zero]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Pw c) (w c - Pw c) h0
    rw [add_sub_cancel] at this
    simp only [sq]; linarith
  have hL2 : ∀ f : Lp ℂ 2 μ, ‖f‖ ^ 2 = ∫ g, ‖(f : G → ℂ) g‖ ^ 2 ∂μ := fun f => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def,
      ← integral_re (MeasureTheory.L2.integrable_inner f f)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ((f : G → ℂ) g)
  have hcomp : ∀ v ∈ H', ∀ c, ‖v c‖ ^ 2 = ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := fun v hv c => by
    rw [hL2, ← hschur (Pw c) (hPwm c) v hv]
    refine integral_congr_ae ?_
    filter_upwards [hrep v (hH'P hv) c] with g hg
    rw [hg, hinnerP c _ (hH'st g v hv)]
  have hkey : ∀ v ∈ H', ‖v‖ ^ 2 = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := fun v hv => by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Lp ℂ 2 μ) v
    calc ‖v‖ ^ 2 = ∑ c, ‖v c‖ ^ 2 := h
      _ = ∑ c, ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := Finset.sum_congr rfl fun c _ => hcomp v hv c
      _ = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := by rw [Finset.sum_mul, Finset.sum_div]
  obtain ⟨v0, hv0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH'0
  have hsum : ∑ c, ‖Pw c‖ ^ 2 = d' := by
    have h := hkey v0 hv0
    have hn : ‖v0‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
    field_simp at h
    nlinarith [h, hn, sq_nonneg ‖v0‖]
  refine ⟨hsum ▸ Finset.sum_le_sum fun c _ => by rw [hpyth c]; nlinarith [sq_nonneg ‖w c - Pw c‖], fun heq => ?_⟩
  have hwc : ∀ c, w c ∈ H' := by
    have h0 : ∑ c, ‖w c - Pw c‖ ^ 2 = 0 := by
      have := congrArg (fun t => t - d') heq
      simp only [sub_self] at this
      rw [← this, ← hsum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [hpyth c]; ring
    intro c
    have := (Finset.sum_eq_zero_iff_of_nonneg fun c _ => sq_nonneg ‖w c - Pw c‖).mp h0 c (Finset.mem_univ c)
    have h1 : w c - Pw c = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    rw [sub_eq_zero.mp h1]; exact hPwm c
  have hadj : ∀ g (a b : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), inner ℂ a (ρ g b) = inner ℂ (ρ g⁻¹ a) b := fun g a b => by
    let L : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗᵢ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) :=
      ⟨(ρ g : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), hiso g⟩
    have e : ρ g (ρ g⁻¹ a) = a := by
      rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
    conv_lhs => rw [← e]
    exact L.inner_map_map _ _
  intro v hv
  set u := v - H'.starProjection v with hu
  have huP : u ∈ HP := HP.sub_mem hv (hH'P (H'.starProjection_apply_mem v))
  have hu0 : ∀ c, ((u c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] 0 := fun c => by
    filter_upwards [hrep u huP c] with g hg
    rw [hg, hadj, Pi.zero_apply]
    have := H'.starProjection_inner_eq_zero v _ (hH'st g⁻¹ _ (hwc c))
    rw [← inner_conj_symm, this, map_zero]
  have hu' : u = 0 := by
    refine (WithLp.ofLp_injective 2).eq_iff.mp ?_
    funext c
    exact Lp.eq_zero_iff_ae_eq_zero.mpr (hu0 c)
  have : v = H'.starProjection v := sub_eq_zero.mp hu'
  rw [this]; exact H'.starProjection_apply_mem v

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

theorem tf_rep_closure {n : ℕ} {G : Type*} [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hρ : ∀ g x, ‖ρ g x‖ ≤ ‖x‖) (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (S : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hS : ∀ v ∈ S, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v)) :
    ∀ v ∈ S.topologicalClosure, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v) := by
  intro v hv c
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hv
  have huc : Tendsto (fun k => u k c) atTop (𝓝 (v c)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun k => PiLp.dist_apply_le _ _ c) (tendsto_iff_dist_tendsto_zero.1 hu))
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp huc).exists_seq_tendsto_ae
  have hall : ∀ᵐ g ∂μ, ∀ k, ((u k c : Lp ℂ 2 μ) : G → ℂ) g = inner ℂ (w c) (ρ g (u k)) :=
    ae_all_iff.2 (fun k => hS (u k) (huS k) c)
  filter_upwards [hns, hall] with g hg hgall
  have h2 : Tendsto (fun i => inner ℂ (w c) (ρ g (u (ns i)))) atTop (𝓝 (inner ℂ (w c) (ρ g v))) := by
    have h3 : Tendsto (fun i => u (ns i)) atTop (𝓝 v) :=
      hu.comp (hmono.tendsto_atTop)
    exact ((continuous_const.inner continuous_id).tendsto _).comp ((ρ g).continuous.tendsto v |>.comp h3)
  simp only [hgall] at hg
  exact tendsto_nhds_unique hg h2

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def gx (l : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0, _ => 1
  | k + 1, r => l r * gx l k r - ∑ s ∈ univ.filter (fun s => r < s), gx l k s

def gelfandSeries (l : Fin n → ℂ) : PowerSeries ℂ :=
  1 - ∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹)

def gval (l : Fin n → ℂ) (k : ℕ) : ℂ := PowerSeries.coeff (k + 1) (gelfandSeries l)

def icShift (μ : Fin n → ℝ) : Fin n → ℂ := fun r => ((μ r + ((n : ℝ) - 1) / 2 : ℝ) : ℂ)

def gxSeries (l : Fin n → ℂ) (r : Fin n) : PowerSeries ℂ := PowerSeries.mk fun k => gx l k r

theorem gxSeries_mul (l : Fin n → ℂ) (r : Fin n) :
    gxSeries l r * (1 - PowerSeries.C (l r) * PowerSeries.X) =
      1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s => r < s), gxSeries l s := by
  ext k
  rcases k with _ | k
  · simp [gxSeries, gx]
  · rw [show gxSeries l r * (1 - PowerSeries.C (l r) * PowerSeries.X) =
        gxSeries l r - PowerSeries.C (l r) * (gxSeries l r * PowerSeries.X) by ring,
      map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, map_sub,
      PowerSeries.coeff_succ_X_mul, map_sum]
    simp [gxSeries, gx, PowerSeries.coeff_one]

theorem oneSubCX_const_ne (a : ℂ) : PowerSeries.constantCoeff (1 - PowerSeries.C a * PowerSeries.X) ≠ 0 := by
  simp

theorem gxSeries_eq (l : Fin n → ℂ) (r : Fin n) :
    gxSeries l r = (1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s => r < s), gxSeries l s) *
      (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹ := by
  rw [← gxSeries_mul, mul_assoc, PowerSeries.mul_inv_cancel _ (oneSubCX_const_ne _), mul_one]

theorem gxSeries_tele (l : Fin n → ℂ) (d : ℕ) : ∀ r : ℕ, n - r = d →
    1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s : Fin n => r ≤ s.val), gxSeries l s =
      ∏ s ∈ univ.filter (fun s : Fin n => r ≤ s.val),
        (1 - PowerSeries.X * (1 - PowerSeries.C (l s) * PowerSeries.X)⁻¹) := by
  induction d with
  | zero =>
    intro r hr
    have : univ.filter (fun s : Fin n => r ≤ s.val) = ∅ := by
      ext s; simp; omega
    simp [this]
  | succ d ih =>
    intro r hr
    have hrn : r < n := by omega
    have hins : univ.filter (fun s : Fin n => r ≤ s.val) =
        insert ⟨r, hrn⟩ (univ.filter (fun s : Fin n => r + 1 ≤ s.val)) := by
      ext s; simp [Fin.ext_iff]; omega
    have hgt : univ.filter (fun s : Fin n => (⟨r, hrn⟩ : Fin n) < s) =
        univ.filter (fun s : Fin n => r + 1 ≤ s.val) := by
      ext s; simp only [mem_filter, mem_univ, true_and, Fin.lt_def]; omega
    have hnot : (⟨r, hrn⟩ : Fin n) ∉ univ.filter (fun s : Fin n => r + 1 ≤ s.val) := by simp
    rw [hins, sum_insert hnot, prod_insert hnot, ← ih (r + 1) (by omega), gxSeries_eq l ⟨r, hrn⟩,
      hgt]
    ring

theorem gelfandSeries_eq (l : Fin n → ℂ) :
    gelfandSeries l = PowerSeries.X * ∑ r, gxSeries l r := by
  have h := gxSeries_tele l n 0 (by simp)
  have e : univ.filter (fun s : Fin n => 0 ≤ s.val) = univ := by ext; simp
  rw [e] at h
  rw [gelfandSeries, ← h]
  ring

theorem sum_gx_eq_gval (l : Fin n → ℂ) (k : ℕ) : ∑ r, gx l k r = gval l k := by

  rw [gval, gelfandSeries_eq, PowerSeries.coeff_succ_X_mul, map_sum]
  simp [gxSeries]

end ReciprocityTheory.ChartRestriction.DS
end
end
