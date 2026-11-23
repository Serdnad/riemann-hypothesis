module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section

namespace ChA

lemma finite_sep {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Set V) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) (R : ℝ) :
    {x | x ∈ S ∧ ‖x‖ ≤ R}.Finite := by
  classical
  have hcpt : IsCompact (Metric.closedBall (0 : V) R) := isCompact_closedBall 0 R
  obtain ⟨t, htfin, hcov⟩ :=
    (Metric.totallyBounded_iff.mp hcpt.totallyBounded) (1 / 2) (by norm_num)
  have hT : ∀ x ∈ {x | x ∈ S ∧ ‖x‖ ≤ R}, ∃ y ∈ t, dist x y < 1 / 2 := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : V) R := by
      rw [mem_closedBall_zero_iff]; exact hx.2
    have := hcov hx'
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at this
    exact this
  choose! f hf hfx using hT
  refine Set.Finite.of_finite_image (f := f) (htfin.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hf x hx
  · intro x hx y hy hxy
    by_contra hne
    have hsep := hS x hx.1 y hy.1 hne
    have h1 := hfx x hx
    have h2 := hfx y hy
    rw [hxy] at h1
    have hlt : dist x y < 1 := by
      calc dist x y ≤ dist x (f y) + dist y (f y) := dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
        _ = 1 := by norm_num
    rw [dist_eq_norm] at hlt
    linarith

lemma sep_of_group {V : Type} [NormedAddCommGroup V] (G : AddSubgroup V)
    (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (S : Set V) (hS : S ⊆ G) :
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖ := by
  intro x hx y hy hne
  exact hG (x - y) (G.sub_mem (hS hx) (hS hy)) (sub_ne_zero.mpr hne)

lemma exists_closest {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (G : AddSubgroup V) (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (p : V) :
    ∃ w ∈ G, ∀ w' ∈ G, ‖p - w‖ ≤ ‖p - w'‖ := by
  classical
  have hsep := sep_of_group G hG (G : Set V) subset_rfl
  have hfin : {x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖}.Finite := finite_sep _ hsep _
  have hne : ({x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖} : Set V).Nonempty :=
    ⟨0, G.zero_mem, by simp⟩
  obtain ⟨w, hw, hmin⟩ := Set.exists_min_image _ (fun w => ‖p - w‖) hfin hne
  refine ⟨w, hw.1, fun w' hw' => ?_⟩
  by_cases h : ‖w'‖ ≤ 2 * ‖p‖
  · exact hmin w' ⟨hw', h⟩
  · push Not at h
    have h0 := hmin 0 ⟨G.zero_mem, by simp⟩
    simp only [sub_zero] at h0
    have h3 : ‖w'‖ - ‖p‖ ≤ ‖p - w'‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le w' p
    linarith

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ) (β δ : ι → ℝ)
    (hy : ∀ i, ‖y i‖ ≤ β i) (hxy : ∀ i, ‖x i - y i‖ ≤ δ i) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ∏ i ∈ s, (β i + δ i) - ∏ i ∈ s, β i := by
  classical
  have hβ : ∀ i, 0 ≤ β i := fun i => (norm_nonneg _).trans (hy i)
  have hδ : ∀ i, 0 ≤ δ i := fun i => (norm_nonneg _).trans (hxy i)
  have hx : ∀ i, ‖x i‖ ≤ β i + δ i := fun i => by
    calc ‖x i‖ = ‖y i + (x i - y i)‖ := by ring_nf
      _ ≤ ‖y i‖ + ‖x i - y i‖ := norm_add_le _ _
      _ ≤ β i + δ i := add_le_add (hy i) (hxy i)
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have hX : ‖∏ i ∈ s, x i‖ ≤ ∏ i ∈ s, (β i + δ i) := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hx i)
    have hP : ∏ i ∈ s, β i ≤ ∏ i ∈ s, (β i + δ i) :=
      Finset.prod_le_prod₀ (fun i _ => hβ i) (fun i _ => le_add_of_nonneg_right (hδ i))
    calc ‖x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i‖
        = ‖(x a - y a) * ∏ i ∈ s, x i + y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i)‖ := by ring_nf
      _ ≤ ‖(x a - y a) * ∏ i ∈ s, x i‖ + ‖y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i)‖ := norm_add_le _ _
      _ = ‖x a - y a‖ * ‖∏ i ∈ s, x i‖ + ‖y a‖ * ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ δ a * ∏ i ∈ s, (β i + δ i) + β a * (∏ i ∈ s, (β i + δ i) - ∏ i ∈ s, β i) := by
          exact add_le_add (mul_le_mul (hxy a) hX (norm_nonneg _) (hδ a))
            (mul_le_mul (hy a) ih (norm_nonneg _) (hβ a))
      _ = (β a + δ a) * ∏ i ∈ s, (β i + δ i) - β a * ∏ i ∈ s, β i := by ring

theorem norm_sum_prod_sub_le {τ ι : Type*} [Fintype τ] [Fintype ι] (sg : τ → ℂ)
    (hsg : ∀ T, ‖sg T‖ ≤ 1) (D A : τ → ι → ℂ) (α δ : ι → ℝ) (hA : ∀ T k, ‖A T k‖ ≤ α k)
    (hD : ∀ T k, ‖D T k - A T k‖ ≤ δ k) :
    ‖∑ T, sg T * ∏ k, D T k - ∑ T, sg T * ∏ k, A T k‖ ≤
      Fintype.card τ * (∏ k, (α k + δ k) - ∏ k, α k) := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ T, (sg T * ∏ k, D T k - sg T * ∏ k, A T k)‖
      ≤ ∑ T, ‖sg T * ∏ k, D T k - sg T * ∏ k, A T k‖ := norm_sum_le _ _
    _ ≤ ∑ _T : τ, (∏ k, (α k + δ k) - ∏ k, α k) := by
        refine Finset.sum_le_sum fun T _ => ?_
        rw [← mul_sub, norm_mul]
        have h := norm_prod_sub_prod_le Finset.univ (D T) (A T) α δ (hA T) (hD T)
        calc ‖sg T‖ * ‖∏ k, D T k - ∏ k, A T k‖ ≤ 1 * ‖∏ k, D T k - ∏ k, A T k‖ := by
              gcongr
              exact hsg T
          _ ≤ _ := by rw [one_mul]; exact h
    _ = Fintype.card τ * (∏ k, (α k + δ k) - ∏ k, α k) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem one_add_pow_sub_one_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (1 + x) ^ m - 1 ≤ m * x * (1 + x) ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℝ) ≤ (1 + x) ^ n := by
      have h : (1 : ℝ) ^ n ≤ (1 + x) ^ n := by gcongr; linarith
      simpa using h
    have h2 : (1 : ℝ) ≤ (1 + x) ^ n * (1 + x) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ 1 + x)
    push_cast
    rw [pow_succ]
    nlinarith [mul_nonneg hx (sub_nonneg.2 h2)]

theorem num_bound (r D : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-((D + 1) * (r * Real.log r + 3 * r + 3)))) :
    2 * D * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) * ε ≤ 1 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have h2D : 2 * (D : ℝ) ≤ Real.exp (2 * D) := by linarith [Real.add_one_le_exp (2 * (D : ℝ))]
  have hpow : ((4 : ℝ) * r) ^ D = Real.exp (D * Real.log (4 * r)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hlog : Real.log (4 * r) = Real.log 4 + Real.log r :=
    Real.log_mul (by norm_num) (by positivity)
  have hP : 2 * (D : ℝ) * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) ≤
      Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) := by
    rw [hpow]
    calc 2 * (D : ℝ) * Real.exp (D * Real.log (4 * r)) * Real.exp ((r / 2 + 1) * D)
        ≤ Real.exp (2 * D) * Real.exp (D * Real.log (4 * r)) * Real.exp ((r / 2 + 1) * D) := by
          gcongr
      _ = Real.exp (2 * D + D * Real.log (4 * r) + (r / 2 + 1) * D) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) := by
          apply Real.exp_le_exp.2
          rw [hlog]
          nlinarith [mul_nonneg hD0 (mul_nonneg (sub_nonneg.2 hr1) hlogr),
            mul_nonneg hD0 (sub_nonneg.2 hlog4), mul_nonneg hD0 (sub_nonneg.2 hr1),
            mul_nonneg hr0.le hlogr]
  calc 2 * (D : ℝ) * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) * ε
      ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) *
          Real.exp (-((D + 1) * (r * Real.log r + 3 * r + 3))) :=
        mul_le_mul hP hε hε0 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem eps_bound (g d : ℕ) (t K : ℝ) (h : g * Real.log 2 + 2 * d + 3 + K ≤ t) :
    7 * 2 ^ g * (4.3 : ℝ) ^ d * Real.exp (-t) ≤ Real.exp (-K) := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h7 : (7 : ℝ) ≤ Real.exp 3 := by
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (7 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := by gcongr
  have h43 : (4.3 : ℝ) ≤ Real.exp 2 := by
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (4.3 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := by gcongr
  have h2g : (2 : ℝ) ^ g = Real.exp (g * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h43d : (4.3 : ℝ) ^ d ≤ Real.exp (d * 2) := by
    rw [Real.exp_nat_mul]
    gcongr
  calc 7 * 2 ^ g * (4.3 : ℝ) ^ d * Real.exp (-t)
      ≤ Real.exp 3 * Real.exp (g * Real.log 2) * Real.exp (d * 2) * Real.exp (-t) := by
        rw [h2g]; gcongr
    _ = Real.exp (3 + g * Real.log 2 + d * 2 + -t) := by simp only [Real.exp_add]
    _ ≤ Real.exp (-K) := Real.exp_le_exp.2 (by linarith)

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2.DimA

open Module

section Perp

variable {H : Type*} [AddCommGroup H] (B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ)

theorem alt_swap (halt : ∀ h, B h h = 0) (x y : H) : B x y = -B y x := by
  have h := halt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, halt, zero_add, add_zero] at h
  linear_combination h

def perp (e f : H) : Submodule ℤ H := LinearMap.ker (B.flip e) ⊓ LinearMap.ker (B.flip f)

theorem mem_perp {e f h : H} : h ∈ perp B e f ↔ B h e = 0 ∧ B h f = 0 := by
  simp [perp]

variable (halt : ∀ h, B h h = 0) (e f : H) (he : B e f = 1)
include halt he

theorem proj_mem (y : H) : y - B y f • e + B y e • f ∈ perp B e f := by
  have h1 : B f e = -1 := by rw [alt_swap B halt, he]
  rw [mem_perp]
  constructor <;> simp [halt, he, h1] <;> ring

def proj : H →ₗ[ℤ] perp B e f where
  toFun y := ⟨y - B y f • e + B y e • f, proj_mem B halt e f he y⟩
  map_add' x y := by ext; simp only [map_add (f := _), LinearMap.add_apply, add_smul, Submodule.coe_add]; abel
  map_smul' c x := by
    ext; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Submodule.coe_smul, mul_smul,
      RingHom.id_apply, smul_add, smul_sub]

theorem proj_apply (y : H) : (proj B halt e f he y : H) = y - B y f • e + B y e • f := rfl

def splitEquiv : H ≃ₗ[ℤ] perp B e f × ℤ × ℤ where
  toFun y := (proj B halt e f he y, B y f, B y e)
  map_add' x y := by simp
  map_smul' c x := by simp
  invFun p := (p.1 : H) + p.2.1 • e - p.2.2 • f
  left_inv y := by simp only [proj_apply]; abel
  right_inv p := by
    obtain ⟨⟨p, hp⟩, a, c⟩ := p
    have h1 : B f e = -1 := by rw [alt_swap B halt, he]
    rw [mem_perp] at hp
    have hf : B (p + a • e - c • f) f = a := by
      simp [hp.2, he, halt]
    have hE : B (p + a • e - c • f) e = c := by
      simp [hp.1, h1, halt]
    simp only [Prod.mk.injEq]
    refine ⟨?_, hf, hE⟩
    ext
    rw [proj_apply, hf, hE]
    abel

theorem perp_surj (hB : ∀ φ : H →ₗ[ℤ] ℤ, ∃ x, B x = φ) (φ : perp B e f →ₗ[ℤ] ℤ) :
    ∃ x : perp B e f, B.domRestrict₁₂ (perp B e f) (perp B e f) x = φ := by
  obtain ⟨x, hx⟩ := hB (φ.comp (proj B halt e f he))
  refine ⟨proj B halt e f he x, LinearMap.ext fun ⟨p, hp⟩ => ?_⟩
  have hp' := (mem_perp B).1 hp
  have hpe : B e p = 0 := by rw [alt_swap B halt, hp'.1, neg_zero]
  have hpf : B f p = 0 := by rw [alt_swap B halt, hp'.2, neg_zero]
  have hproj : proj B halt e f he p = ⟨p, hp⟩ := by
    ext; rw [proj_apply, hp'.1, hp'.2]; simp
  have hxp : B x p = φ (proj B halt e f he p) := by
    rw [hx]; rfl
  rw [LinearMap.domRestrict₁₂_apply, proj_apply]
  simp only [map_add (f := _), map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hpe, hpf, smul_eq_mul, mul_zero, sub_zero, add_zero]
  rw [hxp, hproj]

end Perp

theorem sympl : ∀ (n : ℕ) (H : Type) [AddCommGroup H] [Module.Free ℤ H] [Module.Finite ℤ H],
    finrank ℤ H = n → ∀ B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ, (∀ h, B h h = 0) →
    (∀ φ : H →ₗ[ℤ] ℤ, ∃ x, B x = φ) →
    ∃ k, n = 2 * k ∧ ∃ e f : Fin k → H, (∀ i j, B (e i) (e j) = 0) ∧
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ hn B halt hB
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨0, rfl, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  let b := Module.finBasisOfFinrankEq ℤ H hn
  obtain ⟨x, hx⟩ := hB (b.coord ⟨0, hpos⟩)
  have hxf : B x (b ⟨0, hpos⟩) = 1 := by rw [hx]; simp
  set e := x
  set f := b ⟨0, hpos⟩
  let Q := perp B e f
  haveI : Module.Free ℤ Q := Module.Free.of_basis (Q.basisOfPid b).2
  haveI : Module.Finite ℤ Q := Module.Finite.of_basis (Q.basisOfPid b).2
  have hr : finrank ℤ Q + 2 = n := by
    have h : finrank ℤ H = finrank ℤ (Q × ℤ × ℤ) := (splitEquiv B halt e f hxf).finrank_eq
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, hn] at h
    omega
  have halt' : ∀ h : Q, B.domRestrict₁₂ Q Q h h = 0 := fun h => halt h
  obtain ⟨k', hk', e', f', hee, hef⟩ :=
    ih (n - 2) (by omega) Q (by omega) (B.domRestrict₁₂ Q Q) halt'
      (perp_surj B halt e f hxf hB)
  refine ⟨k' + 1, by omega, Fin.cons e (fun i => (e' i : H)), Fin.cons f (fun i => (f' i : H)),
    ?_, ?_⟩
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using halt e
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [alt_swap B halt, ((mem_perp B).1 (e' j).2).1, neg_zero]
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact ((mem_perp B).1 (e' i).2).1
      | succ j =>
        simp only [Fin.cons_succ]
        exact hee i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hxf
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [alt_swap B halt, ((mem_perp B).1 (f' j).2).1, neg_zero]
        simp [(Fin.succ_ne_zero j).symm]
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [((mem_perp B).1 (e' i).2).2]
        simp [Fin.succ_ne_zero i]
      | succ j =>
        simp only [Fin.cons_succ, Fin.succ_inj]
        exact hef i j

end ReciprocityTheory.ChartRestriction.G.I2.DimA
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

theorem one_sub_pow_mem {A : Type*} [CommRing A] (h : A) (K : Ideal A) (hK : h - 1 ∈ K) (m : ℕ) :
    1 - h ^ m ∈ K := by
  rw [← Ideal.Quotient.eq]
  have h1 : Ideal.Quotient.mk K h = 1 := by
    rw [← map_one (Ideal.Quotient.mk K)]; exact Ideal.Quotient.eq.mpr hK
  simp [map_pow, h1]

theorem quotientMap_bijective_of_loc {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (h : A) (K : Ideal A) (hK : h - 1 ∈ K)
    (hB : ∀ b : B, ∃ m : ℕ, ∃ a : A, algebraMap A B (h ^ m) * b = algebraMap A B a)
    (hinj : Function.Injective (algebraMap A B)) :
    Function.Bijective (Ideal.quotientMap (K.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map) := by

  have key : ∀ x ∈ K.map (algebraMap A B), ∃ M : ℕ, ∃ k ∈ K, algebraMap A B (h ^ M) * x = algebraMap A B k := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨0, k, hk, by simp⟩
    | zero => exact ⟨0, 0, K.zero_mem, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨M₁, k₁, hk₁, e₁⟩ := ihx
      obtain ⟨M₂, k₂, hk₂, e₂⟩ := ihy
      refine ⟨M₁ + M₂, h ^ M₂ * k₁ + h ^ M₁ * k₂,
        K.add_mem (K.mul_mem_left _ hk₁) (K.mul_mem_left _ hk₂), ?_⟩
      rw [map_add (f := _), map_mul, map_mul, ← e₁, ← e₂, pow_add, map_mul]
      ring
    | smul b x _ ih =>
      obtain ⟨M, k, hk, e⟩ := ih
      obtain ⟨m, a, hb⟩ := hB b
      refine ⟨M + m, a * k, K.mul_mem_left _ hk, ?_⟩
      rw [smul_eq_mul, map_mul, ← hb, ← e, pow_add, map_mul]
      ring
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨M, k, hk, e⟩ := key _ hz
    rw [← map_mul] at e
    have hM : h ^ M * a ∈ K := hinj e ▸ hk
    have h1 : (1 - h ^ M) * a ∈ K := K.mul_mem_right _ (one_sub_pow_mem h K hK M)
    have : a = h ^ M * a + (1 - h ^ M) * a := by ring
    rw [this]; exact K.add_mem hM h1
  · intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨m, a, hb⟩ := hB b
    refine ⟨Ideal.Quotient.mk K a, ?_⟩
    rw [Ideal.quotientMap_mk, ← hb, Ideal.Quotient.eq]
    have hmem : algebraMap A B (1 - h ^ m) ∈ K.map (algebraMap A B) :=
      Ideal.mem_map_of_mem _ (one_sub_pow_mem h K hK m)
    have : algebraMap A B (h ^ m) * b - b = -(algebraMap A B (1 - h ^ m) * b) := by
      rw [map_sub, map_one]; ring
    rw [this]
    exact Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hmem)

end ReciprocityTheory.ChartRestriction.G.I2
end
