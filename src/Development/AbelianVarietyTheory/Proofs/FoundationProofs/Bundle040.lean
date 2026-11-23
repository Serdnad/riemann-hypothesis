module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAddOfLt
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle003
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Ring.Ultra
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

@[expose] public section

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem cochain_coboundary_prod_hom_identities :
    ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
    (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
    η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
    (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  intro Γ _ N x y η h
  refine ⟨?_, ?_, ?_⟩
  · have h0 := h 1 1
    simp only [map_one, toAdd_one, zero_mul, mul_one] at h0
    linear_combination -h0
  · intro g n
    have h1 := h g n
    have h2 := h (g * n * g⁻¹) g
    have e : g * n * g⁻¹ * g = g * n := by group
    have e2 : (x (g * n * g⁻¹)).toAdd = (x n).toAdd := by
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
      ring
    rw [e, e2] at h2
    linear_combination h1 - h2
  · intro m n hm
    have h3 := h m n
    rw [hm, zero_mul] at h3
    linear_combination h3

end GlobalTheory
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem exists_extension_of_dense {X₀ X M : Type} [AddCommGroup X₀] [AddCommGroup X]
    [AddCommGroup M] [Module ℂ M] (ι : X₀ →+ X) (A : AddSubgroup X) (β : X → X → ℂ)
    (W₀ : X₀ → M →ₗ[ℂ] M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z)
    (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hA : ∀ a ∈ A, ∀ b ∈ A, β a b = 1)
    (hβ : ∀ x, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, β x (m • a) = 1 ∧ β (m • a) x = 1)
    (hW : ∀ x y v, W₀ x (W₀ y v) = β (ι x) (ι y) • W₀ (x + y) v)
    (hd : ∀ (x : X) (m : ℕ), 0 < m → ∃ z, ∃ a ∈ A, ι z = x + m • a)
    (hs : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ z, (∃ a ∈ A, ι z = m • a) → W₀ z v = v) :
    ∃ W : X → M →ₗ[ℂ] M, (∀ z, W (ι z) = W₀ z) ∧
      (∀ x y v, W x (W y v) = β x y • W (x + y) v) ∧
      ∀ x v, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, W (x + m • a) v = W x v := by
  choose b hb0 hb using hβ
  have hb' : ∀ x (n : ℕ), b x ∣ n → ∀ a ∈ A, β x (n • a) = 1 ∧ β (n • a) x = 1 := by
    rintro x n ⟨k, rfl⟩ a ha
    rw [mul_smul]
    exact hb x _ (A.nsmul_mem ha k)
  have hex : ∀ (x : X) (v : M), ∃ G : M, ∃ m : ℕ, 0 < m ∧
      ∀ n : ℕ, m ∣ n → ∀ z, ∀ a ∈ A, ι z = x + n • a → W₀ z v = G := by
    intro x v
    obtain ⟨m, hm0, hm⟩ := hs v
    obtain ⟨z₁, a₁, ha₁, hz₁⟩ := hd x (m * b x) (Nat.mul_pos hm0 (hb0 x))
    refine ⟨W₀ z₁ v, m * b x, Nat.mul_pos hm0 (hb0 x), ?_⟩
    rintro n ⟨k, rfl⟩ z a ha hz
    rw [mul_smul] at hz
    have ha' : k • a ∈ A := A.nsmul_mem ha k
    have hsub : a₁ - k • a ∈ A := A.sub_mem ha₁ ha'
    have hιd : ι (z₁ - z) = (m * b x) • (a₁ - k • a) := by
      rw [map_sub, hz₁, hz, smul_sub]; abel
    have h1 : W₀ (z₁ - z) v = v :=
      hm _ ⟨b x • (a₁ - k • a), A.nsmul_mem hsub _, by rw [hιd, mul_smul]⟩
    have h2 := hW z (z₁ - z) v
    rw [h1, hιd, hz, hl, (hb' x _ (Dvd.intro_left m rfl) _ hsub).1,
      hA _ (A.nsmul_mem ha' _) _ (A.nsmul_mem hsub _), add_sub_cancel] at h2
    simpa using h2
  choose val lev hlev0 hlev using hex
  refine ⟨fun x =>
    { toFun := val x
      map_add' := ?_
      map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro v w
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x w * lev x (v + w))
      (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x w * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x w _ ⟨lev x v * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x (v + w) _ ⟨lev x v * lev x w, by ring⟩ z a ha hz, map_add]
  · intro c v
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x (c • v))
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x (c • v), by ring⟩ z a ha hz,
      ← hlev x (c • v) _ ⟨lev x v, by ring⟩ z a ha hz, map_smul, RingHom.id_apply]
  · intro z
    ext v
    exact (hlev (ι z) v _ dvd_rfl z 0 A.zero_mem (by simp)).symm
  · intro x y v
    change val x (val y v) = β x y • val (x + y) v
    obtain ⟨n, hn0, h1, h2, h3, h4, h5⟩ : ∃ n : ℕ, 0 < n ∧ lev x (val y v) ∣ n ∧ lev y v ∣ n ∧
        lev (x + y) v ∣ n ∧ b x ∣ n ∧ b y ∣ n :=
      ⟨lev x (val y v) * lev y v * lev (x + y) v * b x * b y,
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
          (hb0 _)) (hb0 _),
        ⟨lev y v * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b x, by ring⟩⟩
    obtain ⟨z, a, ha, hz⟩ := hd x n hn0
    obtain ⟨w, c, hc, hw⟩ := hd y n hn0
    have hzw : ι (z + w) = x + y + n • (a + c) := by
      rw [map_add (f := _), hz, hw, smul_add]; abel
    have hβzw : β (ι z) (ι w) = β x y := by
      rw [hz, hw, hl, hr, hr, (hb' x n h4 c hc).1, (hb' y n h5 a ha).2,
        hA _ (A.nsmul_mem ha n) _ (A.nsmul_mem hc n)]
      ring
    rw [← hlev x (val y v) n h1 z a ha hz, ← hlev (x + y) v n h3 (z + w) _ (A.add_mem ha hc) hzw,
      ← hlev y v n h2 w c hc hw, hW, hβzw]
  · intro x v
    refine ⟨lev x v, hlev0 _ _, fun a ha => ?_⟩
    change val (x + lev x v • a) v = val x v
    obtain ⟨z, c, hc, hz⟩ := hd (x + lev x v • a) (lev x v * lev (x + lev x v • a) v)
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev _ v _ (Dvd.intro_left _ rfl) z c hc hz]
    refine hlev x v _ dvd_rfl z (a + lev (x + lev x v • a) v • c)
      (A.add_mem ha (A.nsmul_mem hc _)) ?_
    rw [hz, smul_add, mul_smul, add_assoc]

end GlobalTheory.FinWeil
end

section

open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory

theorem hahn_pow_neg_one_lead {R : Type} [CommRing R] (x : HahnSeries ℚ R)
    (h1 : x.coeff (-1) = 1) (hlt : ∀ r : ℚ, r < -1 → x.coeff r = 0) :
    ∀ m : ℕ, (x ^ m).coeff (-(m : ℚ)) = 1 ∧ ∀ r : ℚ, r < -(m : ℚ) → (x ^ m).coeff r = 0 := by
  intro m
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, fun r _ => Subsingleton.elim _ _⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hxo : x.order = -1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [h1]; exact one_ne_zero)) ?_
    by_contra hc
    push_neg at hc
    exact hx0 (HahnSeries.coeff_order_eq_zero.mp (hlt _ hc))
  have hxl : x.leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq, hxo, h1]
  have key : ∀ n : ℕ, (x ^ n).order = -(n : ℚ) ∧ (x ^ n).leadingCoeff = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : (x ^ n).leadingCoeff * x.leadingCoeff ≠ 0 := by
        rw [ih.2, hxl, one_mul]; exact one_ne_zero
      rw [pow_succ, HahnSeries.order_mul_of_ne_zero hne, HahnSeries.leadingCoeff_mul_of_ne_zero hne,
        ih.1, ih.2, hxo, hxl]
      constructor
      · push_cast; ring
      · simp
  obtain ⟨ho, hl⟩ := key m
  refine ⟨?_, fun r hr => ?_⟩
  · rw [← ho, ← HahnSeries.leadingCoeff_eq, hl]
  · exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [ho]; exact hr)

end GlobalTheory
end

section

namespace GlobalTheory.TorsionIntegral

open IsUltrametricDist WeierstrassCurve

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := norm_add_le_max a (-b)
  rwa [norm_neg, ← sub_eq_add_neg] at this

lemma norm_add_eq_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_y_sq {A B x y : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hx : 1 < ‖x‖)
    (h : y ^ 2 = x ^ 3 + A * x + B) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  have h1 : ‖x‖ < ‖x‖ ^ 3 := by
    have := pow_lt_pow_right₀ hx (show 1 < 3 by norm_num)
    simpa using this
  rw [← norm_pow, h, add_assoc, norm_add_eq_of_lt, norm_pow]
  rw [norm_pow]
  refine (norm_add_le_max _ _).trans_lt (max_lt ?_ (by linarith))
  rw [norm_mul]
  nlinarith [norm_nonneg A]

lemma norm_sum_three_le (a b c : K) : ‖a + b + c‖ ≤ max (max ‖a‖ ‖b‖) ‖c‖ :=
  (norm_add_le_max _ _).trans (max_le_max (norm_add_le_max _ _) le_rfl)

lemma norm_two_le : ‖(2 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 2

lemma norm_three_le : ‖(3 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 3

noncomputable def param {W : Affine K} : W.Point → K
  | .zero => 0
  | .some x y _ => x / y

def Near {W : Affine K} (M : ℝ) : W.Point → Prop
  | .zero => True
  | .some x _ _ => M ≤ ‖x‖

lemma add_step [DecidableEq K] {A B : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hM : 1 < M)
    (P Q : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Point) (hP : Near M P)
    (hQ : Near M Q) : Near M (P + Q) ∧ ‖param (P + Q) - param P - param Q‖ ≤ M⁻¹ := by
  first
  | exact @_root_.GlobalTheory.UltrametricLineBounds.large_add
  | exact _root_.GlobalTheory.UltrametricLineBounds.large_add
  | (apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricLineBounds.large_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricLineBounds.large_add ..)

theorem norm_x_le_one_of_nsmul_eq_zero (K : Type) [NormedField K] [IsUltrametricDist K]
    [DecidableEq K] (A B : K) (N : ℕ) (x y : K)
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hN : ‖(N : K)‖ = 1)
    (h0 : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖x‖ ≤ 1 := by
  by_contra hx
  push Not at hx
  have M0 : 0 ≤ ‖x‖⁻¹ := by positivity
  have hP : Near ‖x‖ (Affine.Point.some x y h) := le_refl _
  have key : ∀ k : ℕ, Near ‖x‖ (k • Affine.Point.some x y h) ∧
      ‖param (k • Affine.Point.some x y h) - (k : K) * (x / y)‖ ≤ ‖x‖⁻¹ := by
    intro k
    induction k with
    | zero =>
      rw [zero_nsmul]
      exact ⟨trivial, by simp [Affine.Point.zero_def, param]⟩
    | succ k ih =>
      obtain ⟨s1, s2⟩ := add_step hA hB hx _ _ ih.1 hP
      rw [succ_nsmul]
      refine ⟨s1, ?_⟩
      have := (norm_add_le_max _ _).trans (max_le s2 ih.2)
      refine le_of_eq_of_le (congrArg norm ?_) this
      simp only [param]
      push_cast
      ring
  have h1 := (key N).2
  rw [h0] at h1
  simp only [Affine.Point.zero_def, param, zero_sub, norm_neg, norm_mul, hN, one_mul,
    norm_div] at h1
  have he : y ^ 2 = x ^ 3 + A * x + B := by
    have := (Affine.equation_iff _ _).1 h.1
    simp only at this
    linear_combination this
  have hy := norm_y_sq hA hB hx he
  have x0 : 0 < ‖x‖ := by linarith
  have y0 : 0 < ‖y‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
    rw [← h] at hy
    have : 0 < ‖x‖ ^ 3 := by positivity
    simp at hy
    linarith
  rw [inv_eq_one_div, div_le_div_iff₀ y0 x0, one_mul] at h1
  have h2 : (‖x‖ * ‖x‖) ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
  rw [hy] at h2
  have : ‖x‖ ^ 3 * 1 < ‖x‖ ^ 3 * ‖x‖ := by gcongr
  nlinarith

end GlobalTheory.TorsionIntegral
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory

open scoped Interval

theorem green_periodic_rectangle : ∀ (G D : ℂ → ℂ) (T a b : ℝ), 0 < T → 0 < a → a ≤ b →
    (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = D s) →
    ContinuousOn D {s : ℂ | 0 < s.im} → (∀ s : ℂ, 0 < s.im → G (s + T) = G s) →
    (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (b : ℂ) * Complex.I)) -
      (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (a : ℂ) * Complex.I)) =
      ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
  intro G D T a b hT ha hab hG hD hper
  let φL : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Complex.I
  have hφ : ∀ p : ℝ × ℝ, φL p = (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
    intro p; simp [φL, Complex.real_smul]
  have him : ∀ p : ℝ × ℝ, (φL p).im = p.1 := by
    intro p; simp [hφ]
  have hder : ∀ s : ℂ, 0 < s.im → HasFDerivAt G (fderiv ℝ G s) s ∧
      fderiv ℝ G s Complex.I - Complex.I * fderiv ℝ G s 1 = D s := by
    intro s hs
    obtain ⟨L, hL, hLD⟩ := hG s hs
    rw [hL.fderiv]; exact ⟨hL, hLD⟩
  have hRpos : ∀ p ∈ [[a, b]] ×ˢ [[(0:ℝ), T]], 0 < (φL p).im := by
    intro p hp
    rw [him]
    have h1 := hp.1
    rw [Set.uIcc_of_le hab] at h1
    exact lt_of_lt_of_le ha h1.1
  have hGc : ContinuousOn G {s : ℂ | 0 < s.im} := fun s hs =>
    ((hder s hs).1.continuousAt).continuousWithinAt
  have hfc : ContinuousOn (fun p => G (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) :=
    hGc.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)
  have hsub : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T),
      x ∈ [[a, b]] ×ˢ [[(0:ℝ), T]] := fun x hx =>
    ⟨Set.Ioo_subset_Icc_self hx.1, Set.Ioo_subset_Icc_self hx.2⟩
  have hdf : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T),
      HasFDerivAt (fun p => G (φL p)) ((fderiv ℝ G (φL x)).comp φL) x := fun x hx =>
    (hder _ (hRpos x (hsub x hx))).1.comp x φL.hasFDerivAt
  have hpt : ∀ p : ℝ × ℝ, 0 < p.1 →
      (fderiv ℝ G (φL p)).comp φL (1, 0) + ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1)
        = D (φL p) := by
    intro p hp
    have h := (hder (φL p) (by rw [him]; exact hp)).2
    rw [← h]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, hφ, smul_eq_mul]
    simp
    ring
  have hi : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (fderiv ℝ G (φL p)).comp φL (1, 0) +
        ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) := by
    have hc : ContinuousOn (fun p => D (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) :=
      hD.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)
    refine (hc.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun ?_
      (measurableSet_uIcc.prod measurableSet_uIcc)
    intro p hp
    have := hRpos p hp
    rw [him] at this
    exact (hpt p this).symm
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (fun p => G (φL p)) (fun p => (-Complex.I) • G (φL p))
    (fun p => (fderiv ℝ G (φL p)).comp φL) (fun p => (-Complex.I) • (fderiv ℝ G (φL p)).comp φL)
    a 0 b T hfc (by exact hfc.const_smul (-Complex.I)) hdf (fun x hx => by exact (hdf x hx).const_smul (-Complex.I)) hi
  have hL : (∫ y in a..b, ∫ x in (0:ℝ)..T,
      (fderiv ℝ G (φL (y, x))).comp φL (1, 0) +
        ((-Complex.I) • (fderiv ℝ G (φL (y, x))).comp φL) (0, 1)) =
      ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have hy' : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1
    try simp only
    rw [hpt (y, x) hy', hφ]
  have hg : (∫ y in a..b, (-Complex.I) • G (φL (y, T))) =
      ∫ y in a..b, (-Complex.I) • G (φL (y, 0)) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hy' : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1
    try simp only
    have : φL (y, T) = φL (y, 0) + (T : ℂ) := by rw [hφ, hφ]; push_cast; ring
    rw [this, hper _ (by rw [him]; exact hy')]
  rw [hL, hg, sub_self, zero_add] at key
  rw [key]
  simp only [hφ]

end GlobalTheory
end

section

open MeasureTheory Filter Topology Set

theorem _root_.GlobalTheory.T.integral_segment_eq_parallelogram_sides : ∀ (g : ℂ → ℂ) (τ : ℂ) (S : ℝ), DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → 0 < τ.im → 0 ≤ S →
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I) := by
  first | exact @GlobalTheory.cauchy_parallelogram_upper_half_plane | exact GlobalTheory.cauchy_parallelogram_upper_half_plane | (intros; apply GlobalTheory.cauchy_parallelogram_upper_half_plane <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem tendsto_smul_inv_of_mul_tendsto_invertible (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ) (hL : L.det ≠ 0)
    (hAU : Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L))
    (hdU : Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0)) :
    Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  have hdet : Tendsto (fun τ => (A τ * U τ).det) atImInfty (𝓝 L.det) :=
    ((continuous_id.matrix_det).tendsto L).comp hAU
  have hev : ∀ᶠ τ in atImInfty, (A τ * U τ).det ≠ 0 := hdet.eventually_ne hL

  have hinvdet : Tendsto (fun τ => Ring.inverse (A τ * U τ).det) atImInfty (𝓝 (Ring.inverse L.det)) := by
    simp only [Ring.inverse_eq_inv']
    exact hdet.inv₀ hL
  have hadj : Tendsto (fun τ => (A τ * U τ).adjugate) atImInfty (𝓝 L.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto L).comp hAU
  have hinv : Tendsto (fun τ => (A τ * U τ)⁻¹) atImInfty (𝓝 L⁻¹) := by
    simp only [Matrix.inv_def]
    exact hinvdet.smul hadj
  have hlim : Tendsto (fun τ => (d τ • U τ) * (A τ * U τ)⁻¹) atImInfty (𝓝 0) := by
    have := hdU.mul hinv
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [hev] with τ hτ
  have hu : IsUnit (A τ * U τ).det := isUnit_iff_ne_zero.mpr hτ
  have h1 : A τ * (U τ * (A τ * U τ)⁻¹) = 1 := by
    rw [← mul_assoc]; exact Matrix.mul_nonsing_inv _ hu
  rw [Matrix.inv_eq_right_inv h1, Matrix.smul_mul]

end GlobalTheory.OddFrame
end
