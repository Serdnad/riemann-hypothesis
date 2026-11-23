module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle005
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def uMap {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Vsp dim →ₗ[ℝ] Vsp dim :=
  (IR I).starProjection.toLinearMap ∘ₗ
    (((-Complex.I) • LinearMap.id : Vsp dim →ₗ[ℂ] Vsp dim).restrictScalars ℝ)

theorem tof_re_inner_negI {ι : Type} [Fintype ι] (a x : EuclideanSpace ℂ ι) :
    inner ℝ a ((-Complex.I) • x) = (Hf x a).im := by
  simp only [real_inner_eq_re_inner ℂ, PiLp.inner_apply, Hf, Complex.re_sum, Complex.im_sum,
    PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, Complex.mul_im]

theorem isU_uMap {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (x : Vsp dim) :
    IsU I x (uMap I x) := by
  refine ⟨(IR I).starProjection_apply_mem _, fun a ha => ?_⟩
  show inner ℝ ((IR I).starProjection ((-Complex.I) • x)) a = (Hf x a).im
  have h0 := Submodule.starProjection_inner_eq_zero (K := IR I) ((-Complex.I) • x) a ha
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [← h0, real_inner_comm]
  exact tof_re_inner_negI a x

theorem tof_act_add {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  ext i
  simp [act, mul_add]

theorem tof_act_smul {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (c : ℂ) (v : Vsp dim) :
    act α (c • v) = c • act α v := by
  ext i
  simp [act]
  ring

theorem tof_fg_div_eq_bot {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (M : Submodule ℤ Q) (hM : M.FG)
    (r : ℕ) (hr : 2 ≤ r) (hdiv : ∀ m ∈ M, ∃ m' ∈ M, m = r • m') : M = ⊥ := by
  obtain ⟨a, ha1, ha⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {(r : ℤ)}) M hM (by
      intro m hm
      obtain ⟨m', hm', rfl⟩ := hdiv m hm
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm')
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.mem_span_singleton] at ha1
    have h1 : (r : ℤ) ∣ 1 := by simpa using ha1
    have h2 := Int.eq_one_of_dvd_one (by positivity) h1
    omega
  rw [eq_bot_iff]
  intro m hm
  have h := ha m hm
  rw [← Int.cast_smul_eq_zsmul ℝ] at h
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast ha0)

theorem tof_span_condition [IsCMField E] {X : PT E} (I : Submodule ℤ (Vsp X.dim)) (r1 : ℕ) (hr1 : 2 ≤ r1)
    (a yb : Fin X.r → Vsp X.dim) (hyb : ∀ j, yb j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) :
    Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E,
      IsU I (act α (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) w} = IR I := by
  have huniq : ∀ x w, IsU I x w → w = uMap I x := by
    rintro x w ⟨hw, hwa⟩
    have hu := isU_uMap I x
    have hd : w - uMap I x ∈ IR I := (IR I).sub_mem hw hu.1
    have horth : ∀ b ∈ IR I, inner ℝ (w - uMap I x) b = 0 := fun b hb => by
      rw [inner_sub_left, hwa b hb, hu.2 b hb, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero (𝕜 := ℝ).mp (horth _ hd))
  have hset : {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) w} =
      Set.range (fun p : Fin X.r × 𝓞 E =>
        uMap I (act p.2 (((r1 : ℂ) ^ 2) • a p.1 - ((r1 : ℂ) ^ 2) • yb p.1))) := by
    ext w
    constructor
    · rintro ⟨j, α, h⟩
      exact ⟨(j, α), (huniq _ _ h).symm⟩
    · rintro ⟨⟨j, α⟩, rfl⟩
      exact ⟨j, α, isU_uMap I _⟩
  set T : Submodule ℝ (Vsp X.dim) := Submodule.span ℝ (Set.range fun p : Fin X.r × 𝓞 E =>
    act p.2 (((r1 : ℂ) ^ 2) • a p.1 - ((r1 : ℂ) ^ 2) • yb p.1)) with hT
  let f0 : Vsp X.dim →ₗ[ℝ] Vsp X.dim := LinearMap.id - (T.starProjection : Vsp X.dim →ₗ[ℝ] Vsp X.dim)
  have hf0T : ∀ v ∈ T, f0 v = 0 := fun v hv => by
    have h := Submodule.starProjection_mem_subspace_eq_self (K := T) ⟨v, hv⟩
    show v - T.starProjection v = 0
    rw [show ((⟨v, hv⟩ : T) : Vsp X.dim) = v from rfl] at h
    rw [h, sub_self]
  have hf0inv : ∀ v, f0 v = 0 → v ∈ T := fun v hv => by
    have h : v - T.starProjection v = 0 := hv
    rw [sub_eq_zero.mp h]
    exact T.starProjection_apply_mem v
  let f : Vsp X.dim →ₗ[ℤ] Vsp X.dim := f0.toAddMonoidHom.toIntLinearMap
  have hsq : ∀ z : Vsp X.dim, ((r1 : ℂ) ^ 2) • z = r1 • r1 • z := fun z => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul ℂ, sq, mul_smul]
  have hLfg : X.L.FG := Submodule.fg_span (Set.finite_range X.b)
  have hM := tof_fg_div_eq_bot (X.L.map f) (hLfg.map f) r1 hr1 (by
    rintro m ⟨x, hx, rfl⟩
    obtain ⟨c, y, hy, hxe⟩ := hgen x hx
    refine ⟨f (y + ∑ j, r1 • act (c j) (yb j)),
      ⟨_, X.L.add_mem hy (X.L.sum_mem fun j _ => nsmul_mem (X.stable _ _ (hyb j)) r1), rfl⟩, ?_⟩
    have e1 : ∀ j, act (c j) (((r1 : ℂ) ^ 2) • a j) =
        act (c j) (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j) + r1 • r1 • act (c j) (yb j) := by
      intro j
      rw [← hsq, ← tof_act_smul, ← tof_act_add, sub_add_cancel]
    have hz : ∀ j, f (act (c j) (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) = 0 := fun j =>
      hf0T _ (Submodule.subset_span ⟨(j, c j), rfl⟩)
    rw [hxe]
    simp_rw [e1]
    rw [Finset.sum_add_distrib, Nat.cast_smul_eq_nsmul ℂ]

    simp only [map_add (f := _), map_sum, map_nsmul, hz, Finset.sum_const_zero, zero_add, smul_add, Finset.smul_sum]
    abel)
  have hLT : ∀ x ∈ X.L, x ∈ T := fun x hx => hf0inv x (by
    have h : f x ∈ X.L.map f := ⟨x, hx, rfl⟩
    rw [hM] at h
    exact (Submodule.mem_bot ℤ).mp h)
  have hTtop : T = ⊤ := by
    rw [eq_top_iff, ← X.b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hLT _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hset]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact (isU_uMap I _).1
  · intro v hv
    have hv' : uMap I (Complex.I • v) = v := by
      show (IR I).starProjection ((-Complex.I) • Complex.I • v) = v
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      exact Submodule.starProjection_mem_subspace_eq_self (K := IR I) ⟨v, hv⟩
    rw [← hv']
    have hIv : Complex.I • v ∈ T := by rw [hTtop]; exact Submodule.mem_top
    have h2 : uMap I (Complex.I • v) ∈ T.map (uMap I) := ⟨_, hIv, rfl⟩
    rw [hT, Submodule.map_span, ← Set.range_comp] at h2
    exact h2

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem sq_le_Qy_of_le_firstMinimum (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (hne : x ≠ 0) : X.la1 ≤ ‖x‖ := by
  unfold PT.la1
  apply csInf_le
  · exact ⟨0, fun t ht => by obtain ⟨y, -, -, rfl⟩ := ht; exact norm_nonneg y⟩
  · exact ⟨x, hx, hne, rfl⟩

theorem exists_short (X : PT E) (hne : ∃ x ∈ X.L, x ≠ 0) {t : ℝ} (h : X.la1 < t) :
    ∃ x ∈ X.L, x ≠ 0 ∧ ‖x‖ < t := by
  unfold PT.la1 at h
  obtain ⟨x, hx, hne'⟩ := hne
  obtain ⟨s, ⟨y, hy, hy0, rfl⟩, hs⟩ := exists_lt_of_csInf_lt (s := {t : ℝ | ∃ x ∈ X.L, x ≠ 0 ∧ t = ‖x‖}) ⟨‖x‖, x, hx, hne', rfl⟩ h
  exact ⟨y, hy, hy0, hs⟩

theorem first_minimum_pos (X : PT E) (hne : ∃ x ∈ X.L, x ≠ 0) : 0 < X.la1 := by
  obtain ⟨x0, hx0, hx0ne⟩ := hne
  have hfin : Set.Finite {y : Vsp X.dim | y ∈ X.L ∧ y ≠ 0 ∧ ‖y‖ ≤ ‖x0‖} := by
    apply (ZSpan.setFinite_inter X.b (Metric.isBounded_closedBall (x := (0 : Vsp X.dim))
      (r := ‖x0‖))).subset
    rintro y ⟨hy, -, hyn⟩
    exact ⟨mem_closedBall_zero_iff.2 hyn, hy⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image hfin.toFinset (fun y => ‖y‖)
    ⟨x0, (Set.Finite.mem_toFinset hfin).2 ⟨hx0, hx0ne, le_rfl⟩⟩
  rw [Set.Finite.mem_toFinset] at hm
  obtain ⟨-, hm0, hmle⟩ := hm
  have hpos : 0 < ‖m‖ := norm_pos_iff.2 hm0
  refine lt_of_lt_of_le hpos ?_
  unfold PT.la1
  refine le_csInf ⟨‖x0‖, x0, hx0, hx0ne, rfl⟩ ?_
  rintro t ⟨y, hy, hy0, rfl⟩
  by_cases hyle : ‖y‖ ≤ ‖x0‖
  · exact hmin y ((Set.Finite.mem_toFinset hfin).2 ⟨hy, hy0, hyle⟩)
  · exact le_trans hmle (le_of_lt (not_le.1 hyle))

theorem L_ne_zero (X : PT E) (hr : 1 ≤ X.r) (τ : E →+* ℂ) : ∃ x ∈ X.L, x ≠ 0 := by
  have hpos : 0 < Fintype.card (Idx X.dim) := by
    have h := X.dim_conj τ
    rw [Fintype.card_pos_iff]
    by_cases h0 : 0 < X.dim τ
    · exact ⟨⟨τ, ⟨0, h0⟩⟩⟩
    · exact ⟨⟨NumberField.ComplexEmbedding.conjugate τ, ⟨0, by omega⟩⟩⟩
  exact ⟨X.b ⟨0, by omega⟩, Submodule.subset_span (Set.mem_range_self _), X.b.ne_zero _⟩

theorem sat_of_IR {X : PT E} {I : Submodule ℤ (Vsp X.dim)} (hs : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) :
    ∀ x ∈ X.L, ∀ k : ℤ, k ≠ 0 → k • x ∈ I → x ∈ I := by
  intro x hx k hk hkx
  apply hs x hx
  have h1 : (k • x : Vsp X.dim) ∈ IR I := Submodule.subset_span hkx
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have h2 : x = (k : ℝ)⁻¹ • (k • x) := by
    rw [← Int.cast_smul_eq_zsmul ℝ, inv_smul_smul₀ hk']
  rw [h2]
  exact Submodule.smul_mem _ _ h1

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

theorem epsilon_le_half {E : Type} [Field E] [NumberField E] {X : PT E} {DF : ℕ} (P : Par X DF) :
    P.eps1 ≤ 1 / 2 := by
  have h6 := P.C6
  have hr0 : (0:ℝ) ≤ X.r := Nat.cast_nonneg _
  have hr : 0 ≤ (X.r : ℝ) * Real.log X.r := mul_nonneg hr0 (Real.log_natCast_nonneg _)
  have hrest : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) :=
    mul_nonneg (by positivity) (by linarith)
  have e1 := Real.exp_one_gt_d9
  have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have p2 : (2.7:ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by gcongr; linarith
  have p3 : (2.7:ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by gcongr; linarith
  have hl43 : Real.log 4.3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num), e2]
    norm_num at p2
    linarith
  have hl14 : Real.log 7 + Real.log 2 ≤ 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), Real.log_le_iff_le_exp (by norm_num), e3]
    norm_num at p3
    linarith
  have hds : (dstar (E := E) P.m : ℝ) * Real.log 4.3 ≤ 2 * dstar (E := E) P.m := by
    have h := mul_le_mul_of_nonneg_left hl43 (Nat.cast_nonneg (α := ℝ) (dstar (E := E) P.m))
    linarith
  have key : (7:ℝ) * 2 ^ X.gA * (4.3:ℝ) ^ dstar (E := E) P.m =
      Real.exp (Real.log 7 + X.gA * Real.log 2 + dstar (E := E) P.m * Real.log 4.3) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
  unfold Par.eps1
  rw [key, ← Real.exp_add]
  have half : (1:ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [half, Real.exp_le_exp]
  linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

lemma Hf_eq_inner {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  unfold Hf
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, mul_comm]

lemma Hf_add_left {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

lemma Hf_zero_left {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) : Hf 0 v = 0 := by
  simp [Hf]

open Classical in
def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' c v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

open Classical in
lemma prj_apply {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) (i : Idx dim) :
    prj σ v i = if i.1 = σ then v i else 0 := rfl

lemma prj_inPart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : InPart σ (prj σ v) := by
  intro j hj
  rw [prj_apply, if_neg hj]

lemma Hf_prj_right {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {v : Vsp dim} (hv : InPart σ v) (x : Vsp dim) :
    Hf v (prj σ x) = Hf v x := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prj_apply]
  split_ifs with h
  · rfl
  · rw [hv i h, zero_mul, zero_mul]

lemma norm_prj_le {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : ‖prj σ v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [prj_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_pow two_ne_zero]
    positivity

lemma ne_conj [IsCMField E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hc := NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk σ)
  rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
  exact hc (ComplexEmbedding.isReal_iff.mpr h)

open Classical in
def Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then c * v i else
    if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> ring
  map_smul' a v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

open Classical in
lemma Mc_apply {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) (i : Idx dim) :
    Mc σ c v i = if i.1 = σ then c * v i else
      if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0 := rfl

lemma real_inner_Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v w : Vsp dim) :
    inner ℝ (Mc σ c v) w = inner ℝ v (Mc σ ((starRingEnd ℂ) c) w) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Mc_apply, Mc_apply]
  split_ifs <;> simp only [Complex.inner, map_mul, Complex.conj_conj, mul_zero, zero_mul,
    map_zero] <;> ring_nf

lemma prj_Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) :
    prj σ (Mc σ c v) = c • prj σ v := by
  ext i
  rw [prj_apply, PiLp.smul_apply, prj_apply, Mc_apply, smul_eq_mul]
  split_ifs <;> simp

lemma prj_eq_Mc [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) :
    prj σ v = (1 / 2 : ℂ) • (Mc σ 1 v - Complex.I • Mc σ Complex.I v) := by
  ext i
  simp only [prj_apply, PiLp.smul_apply, PiLp.sub_apply, Mc_apply, smul_eq_mul, map_one,
    Complex.conj_I]
  split_ifs
  · ring_nf
    rw [Complex.I_sq]
    ring
  · ring_nf
    rw [Complex.I_sq]
    ring
  · ring

lemma isU_add {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim}
    (hu : IsU I x u) (hv : IsU I y v) : IsU I (x + y) (u + v) :=
    ⟨add_mem hu.1 hv.1, fun a ha => by
      rw [inner_add_left, hu.2 a ha, hv.2 a ha, Hf_add_left, Complex.add_im]⟩

lemma isU_neg {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim}
    (hu : IsU I x u) : IsU I (-x) (-u) :=
    ⟨neg_mem hu.1, fun a ha => by
      have hn : Hf (-x) a = -Hf x a := by simp [Hf, Finset.sum_neg_distrib]
      rw [inner_neg_left, hu.2 a ha, hn, Complex.neg_im]⟩

lemma isU_zero {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 :=
    ⟨zero_mem _, fun a _ => by rw [inner_zero_left, Hf_zero_left, Complex.zero_im]⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

section

variable {ι : Type} [Fintype ι]

open Classical

def paTh (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun v => ∑' γ : lat Y.b, Y.ka γ * paU q γ F v

end




end

end ReciprocityTheory.ChartRestriction.G.I2
end
