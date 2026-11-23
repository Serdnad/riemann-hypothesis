module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem hasSum_comp {ι : Type} (p : MvPolynomial ι ℂ) (Λ : ι → ℂ) :
    HasSum (fun k => eval Λ (homogeneousComponent k p)) (eval Λ p) ∧
      Summable (fun k => ‖eval Λ (homogeneousComponent k p)‖) := by
  have h0 : ∀ k ∉ Finset.range (p.totalDegree + 1), eval Λ (homogeneousComponent k p) = 0 := by
    intro k hk
    rw [homogeneousComponent_eq_zero k p (by simpa using hk), map_zero]
  refine ⟨?_, summable_of_ne_finset_zero (s := Finset.range (p.totalDegree + 1))
    fun k hk => by rw [h0 k hk, norm_zero]⟩
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) h0
  rwa [← map_sum, sum_homogeneousComponent] at h

private theorem hasSum_single' {ι : Type} [Fintype ι] (v : ι → ℝ) (p : MvPolynomial ι ℂ) (Λ : ι → ℂ) :
    HasSum (fun k => ∑ b ∈ Finset.range (k + 1),
      ((b.factorial : ℂ)⁻¹ * eval Λ (lin v) ^ b) * eval Λ (homogeneousComponent (k - b) p))
      (Complex.exp (eval Λ (lin v)) * eval Λ p) := by
  obtain ⟨h1, h2⟩ := hasSum_comp p Λ
  set z := eval Λ (lin v)
  have e1 : HasSum (fun b : ℕ => (b.factorial : ℂ)⁻¹ * z ^ b) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp z
  have e2 : Summable (fun b : ℕ => ‖(b.factorial : ℂ)⁻¹ * z ^ b‖) := e1.summable.norm
  have s := (summable_norm_sum_mul_range_of_summable_norm e2 h2).of_norm
  have t := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm e2 h2
  rw [e1.tsum_eq, h1.tsum_eq] at t
  rw [t]
  exact s.hasSum

theorem UpperTheory.ConvolutionTheory.FX.piece_sum :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (Λ : ι → ℂ), HasSum (fun k => eval Λ (piece k f)) (ev Λ f) := by
  intro ι _ f Λ
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
    simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.1, map_zero]
    exact hasSum_zero
  | add f g hf hg =>
    simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).1 f g, map_add (f := _)]
    exact hf.add hg
  | single v p =>
    have hv : ev Λ (AddMonoidAlgebra.single v p : EP ι) = Complex.exp (eval Λ (lin v)) * eval Λ p := by
      simp [ev, PositivityTheory.Rg.Fx.lift, expChar, lin, mul_comm, aeval_eq_eval]
    rw [hv]
    convert hasSum_single' v p Λ using 2 with k

    rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.2 v p, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, map_pow, eval_C]
    ring
end

section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private lemma pow_le_exp_eventually (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0))
    (L : ℝ) (hL : 0 < L) : ∀ᶠ j : ℕ in atTop, L ^ (d j + 1) ≤ Real.exp j := by
  have h1 : Tendsto (fun j : ℕ => Real.log L * ((d j : ℝ) / j + 1 / j)) atTop
      (𝓝 (Real.log L * (0 + 0))) :=
    (hd.add tendsto_one_div_atTop_nhds_zero_nat).const_mul _
  have h2 := h1.eventually (gt_mem_nhds (show Real.log L * (0 + 0) < 1 by simp))
  filter_upwards [h2, eventually_gt_atTop 0] with j hj hj0
  have hjp : (0 : ℝ) < j := by exact_mod_cast hj0
  have h3 : Real.log L * ((d j : ℝ) + 1) ≤ j := by
    have : Real.log L * ((d j : ℝ) / j + 1 / j) = Real.log L * ((d j : ℝ) + 1) / j := by ring
    rw [this, div_lt_one hjp] at hj
    exact hj.le
  calc L ^ (d j + 1) = Real.exp (Real.log L * ((d j : ℝ) + 1)) := by
        rw [← Real.rpow_def_of_pos hL]
        rw [← Real.rpow_natCast]; push_cast; rfl
    _ ≤ _ := Real.exp_le_exp.2 h3

private lemma err_bound2 (p : ℕ) (hp : 0 < p) (c₁ cq a₀ : ℝ) (h0 : 0 < a₀) (h1 : a₀ ≤ 1)
    (A η : ℝ) (hA : A = |c₁ + cq + 1| + 1) (hηp : 0 < η) (hη : η ≤ a₀ * Real.exp (-(p * A))) (j : ℕ) (F : ℝ)
    (hF : Real.exp ((c₁ + cq + 2 + Real.log (4 / a₀)) * j) ≤ F) :
    Real.exp ((cq + 1) * j) * (η / a₀) ^ (j / p) *
      (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / F) +
        (4 / η) ^ (j / p) * Real.exp (-(cq + 2 + Real.log (4 / a₀)) * j)) ≤
      (Real.exp (p * A) + 2) * Real.exp (-j) := by
  have hFp : 0 < F := (Real.exp_pos _).trans_le hF
  set m := j / p with hm
  set g := Real.log (4 / a₀) with hg
  have hq : (η / a₀) ^ m * (4 / η) ^ m = (4 / a₀) ^ m := by
    rw [← mul_pow]; congr 1; field_simp
  have h4 : (4 / a₀) ^ m ≤ Real.exp (g * j) := by
    have : (1 : ℝ) ≤ 4 / a₀ := by rw [le_div_iff₀ h0]; linarith
    calc (4 / a₀) ^ m ≤ (4 / a₀) ^ j := pow_le_pow_right₀ this (Nat.div_le_self _ _)
      _ = Real.exp (g * j) := by
        rw [mul_comm, Real.exp_nat_mul, hg, Real.exp_log (by positivity)]
  have h5 : (η / a₀) ^ m ≤ Real.exp (-(m * p * A)) := by
    have : η / a₀ ≤ Real.exp (-(p * A)) := by rw [div_le_iff₀ h0, mul_comm]; exact hη
    calc _ ≤ Real.exp (-(p * A)) ^ m := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hmp : (j : ℝ) ≤ m * p + p := by
    have := Nat.lt_div_mul_add (a := j) hp
    rw [← hm] at this
    exact_mod_cast this.le
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hA1 : c₁ + cq + 2 ≤ A := by have := le_abs_self (c₁ + cq + 1); linarith
  have t1 : Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) ≤
      Real.exp (p * A) * Real.exp (-j) := by
    refine le_trans (b := Real.exp ((cq + 1) * j) * Real.exp (-(m * p * A)) * Real.exp (c₁ * j))
      (by gcongr) ?_
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right hmp hA0, mul_le_mul_of_nonneg_right hA1 hj]
  have t2 : Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * (4 / a₀) ^ m / F ≤ Real.exp (-j) := by
    rw [div_le_iff₀ hFp]
    calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * Real.exp (g * j) := by gcongr
      _ = Real.exp (-j) * Real.exp ((c₁ + cq + 2 + g) * j) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := by gcongr
  have t3 : Real.exp ((cq + 1) * j) * (4 / a₀) ^ m * Real.exp (-(cq + 2 + g) * j) ≤
      Real.exp (-j) := by
    calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (g * j) * Real.exp (-(cq + 2 + g) * j) := by gcongr
      _ = Real.exp (-j) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [← hq] at t2 t3
  calc _ = Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) +
        Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * ((η / a₀) ^ m * (4 / η) ^ m) / F +
        Real.exp ((cq + 1) * j) * ((η / a₀) ^ m * (4 / η) ^ m) * Real.exp (-(cq + 2 + g) * j) := by
        ring
    _ ≤ _ := by linarith

private lemma solve_bound2 (x a z η a₀ cq K₁ K E : ℝ) (d m j : ℕ) (hx : 0 ≤ x) (hη : 0 < η)
    (hηa : η < a₀) (h1 : a₀ ≤ 1) (ha : a₀ ≤ a) (hz : Real.exp (-cq) ≤ z) (hE : 0 ≤ E)
    (hL : ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) ≤ Real.exp j)
    (h : x * a ^ d * (2 * a / η - 1) ^ m * z ^ j ≤ K₁ * (K ^ (d + 1) * E)) :
    x ≤ Real.exp ((cq + 1) * j) * (η / a₀) ^ m * E := by
  have h0 : 0 < a₀ := hη.trans hηa
  have hb : a₀ / η ≤ 2 * a / η - 1 := by
    rw [div_sub_one hη.ne', div_le_div_iff_of_pos_right hη]; linarith
  have hb0 : 0 < a₀ / η := by positivity
  have hl : x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j ≤
      x * a ^ d * (2 * a / η - 1) ^ m * z ^ j := by
    have : a₀ ^ (d + 1) ≤ a ^ d :=
      (pow_le_pow_of_le_one h0.le h1 (Nat.le_succ d)).trans (pow_le_pow_left₀ h0.le ha d)
    have h2 : 0 ≤ a := by linarith
    have h3 : 0 ≤ 2 * a / η - 1 := by linarith
    gcongr
  have hr : K₁ * (K ^ (d + 1) * E) ≤ a₀ ^ (d + 1) * Real.exp j * E := by
    have e1 : |K₁| ≤ (|K₁| + 1) ^ (d + 1) :=
      (by linarith : |K₁| ≤ |K₁| + 1).trans
        (le_self_pow₀ (by linarith [abs_nonneg K₁]) (Nat.succ_ne_zero d))
    calc K₁ * (K ^ (d + 1) * E) ≤ |K₁ * (K ^ (d + 1) * E)| := le_abs_self _
      _ = |K₁| * |K| ^ (d + 1) * E := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hE, mul_assoc]
      _ ≤ (|K₁| + 1) ^ (d + 1) * |K| ^ (d + 1) * E := by gcongr
      _ = a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀) ^ (d + 1) * E := by
        rw [← mul_pow, ← mul_pow]; congr 2; field_simp
      _ ≤ a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) * E := by
        gcongr; linarith
      _ ≤ _ := by gcongr
  have h6 := (hl.trans h).trans hr
  have hpos : 0 < a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by positivity
  have e2 : (η / a₀) ^ m * (a₀ / η) ^ m = 1 := by
    rw [← mul_pow]
    have : η / a₀ * (a₀ / η) = 1 := by field_simp
    rw [this, one_pow]
  have e3 : Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j = Real.exp j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  refine le_of_mul_le_mul_right ?_ hpos
  calc _ = x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by ring
    _ ≤ a₀ ^ (d + 1) * Real.exp j * E := h6
    _ = a₀ ^ (d + 1) * (Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j) *
        ((η / a₀) ^ m * (a₀ / η) ^ m) * E := by rw [e2, e3, mul_one]
    _ = _ := by ring

theorem UpperTheory.ConvolutionTheory.FX.exponents2 :
    ∀ (d : ℕ → ℕ), Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) →
    (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
    ∀ (p : ℕ), 0 < p → ∀ (c₁ cq a₀ : ℝ), 0 < a₀ → a₀ ≤ 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < a₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ N : ℝ,
    ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
    Function.Injective (fun i => (a i, ζ i)) → ∀ (c : ℕ → I → ℂ) (c' : I → ℂ),
    (∀ i, Tendsto (fun j => c j i) atTop (𝓝 (c' i))) →
    (∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ s ≤ s₀, ∀ s' ≤ s₀,
    ‖∑ i, c j i * (a i : ℂ) ^ d j * (cheb η (j / p + s) (a i) : ℂ) * ζ i ^ (j + s')‖ ≤
    K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
    ∀ i, a₀ ≤ a i → Real.exp (-cq) ≤ ‖ζ i‖ → c' i = 0 := by
  intro d hd hfac p hp c₁ cq a₀ h0 h1
  obtain ⟨A, hA⟩ : ∃ A, A = |c₁ + cq + 1| + 1 := ⟨_, rfl⟩
  have hη₀a : a₀ * Real.exp (-(p * A)) < a₀ := by
    have hA0 : 0 < A := by rw [hA]; positivity
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have : Real.exp (-(p * A)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [mul_pos hp' hA0])
    nlinarith
  refine ⟨a₀ * Real.exp (-(p * A)), by positivity, hη₀a, ?_⟩
  intro η hηp hη
  have hηa : η < a₀ := hη.trans_lt hη₀a
  refine ⟨cq + 2 + Real.log (4 / a₀), ?_⟩
  intro I _ a ζ ha hζ0 hinj c c' hc hbd i hi hζ
  obtain ⟨s₀, K₁, hsep⟩ := UpperTheory.ConvolutionTheory.FX.separate0 η hηp I a ζ ha hζ0 hinj
  obtain ⟨K, hK⟩ := hbd s₀
  have hev : ∀ᶠ j : ℕ in atTop, ‖c j i‖ ≤ (Real.exp (p * A) + 2) * Real.exp (-j) := by
    filter_upwards [hK, hfac (c₁ + cq + 2 + Real.log (4 / a₀)),
      pow_le_exp_eventually d hd ((|K₁| + 1) * |K| / a₀ + 1) (by positivity)] with j hj hF hL
    have h := hsep (j / p) j (fun i => c j i * (a i : ℂ) ^ d j) _ hj i
    have hai : 0 ≤ a i := by linarith
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hai] at h
    exact (solve_bound2 _ _ _ η a₀ cq K₁ K _ _ _ _ (norm_nonneg _) hηp hηa h1 hi hζ
      (by positivity) hL h).trans (err_bound2 p hp c₁ cq a₀ h0 h1 A η hA hηp hη j _ hF)
  have hlim : Tendsto (fun j : ℕ => (Real.exp (p * A) + 2) * Real.exp (-j)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (Real.exp (p * A) + 2)
    simpa using this
  exact tendsto_nhds_unique (hc i) (squeeze_zero_norm' hev hlim)
end

section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ)
    (p : MvPolynomial ι ℂ) : lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem shift_sum (g : ℕ → ℕ → ℂ) (s : ℕ → ℂ) (d : ℕ) (h0 : ∀ a, d < a → ∀ b, g a b = 0) (h : ∀ a, HasSum (g a) (s a)) :
    HasSum (fun k => ∑ b ∈ Finset.range (k + 1), g (k - b) b) (∑ a ∈ Finset.range (d + 1), s a) := by
  have h1 : ∀ a, HasSum (fun k => if a ≤ k then g a (k - a) else 0) (s a) := fun a => by
    rw [← hasSum_nat_add_iff' a, Finset.sum_eq_zero fun i hi => if_neg (not_le.2 (Finset.mem_range.1 hi)), sub_zero]
    simpa using h a
  convert hasSum_sum (s := Finset.range (d + 1)) fun a _ => h1 a using 2 with k
  rw [← Finset.sum_range_reflect, ← Finset.sum_filter]
  have e : ∀ j ∈ Finset.range (k + 1), g (k - (k + 1 - 1 - j)) (k + 1 - 1 - j) = g j (k - j) := fun j hj => by
    have := Finset.mem_range.1 hj
    congr 1
    omega
  rw [Finset.sum_congr rfl e]
  symm
  refine Finset.sum_subset (fun a ha => ?_) fun a ha hn => h0 a ?_ _
  · simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  · simp only [Finset.mem_filter, Finset.mem_range] at ha hn
    omega

private theorem exp_sum {A M : Type} [CommRing A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    (φ : M →ₗ[ℂ] ℂ) (l : A) (c s : ℂ) (m : M) (h : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * φ (l ^ k • m)) s) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * φ ((algebraMap ℂ A c + l) ^ k • m)) (Complex.exp c * s) := by
  have e1 : HasSum (fun b : ℕ => (b.factorial : ℂ)⁻¹ * c ^ b) (Complex.exp c) := by
    rw [Complex.exp_eq_exp_ℂ]
    simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp c
  have s1 := (summable_norm_sum_mul_range_of_summable_norm e1.summable.norm h.summable.norm).of_norm
  have t := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm e1.summable.norm h.summable.norm
  rw [e1.tsum_eq, h.tsum_eq] at t
  rw [t]
  refine (congrArg (HasSum · _) (funext fun k => ?_)).mpr s1.hasSum

  rw [add_pow, Finset.sum_smul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbk : b ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
  have e : algebraMap ℂ A c ^ b * l ^ (k - b) * (k.choose b : A) = (c ^ b * k.choose b : ℂ) • l ^ (k - b) := by
    rw [Algebra.smul_def, map_mul, map_pow, map_natCast]
    ring
  have h4 : (k.factorial : ℂ) = k.choose b * b.factorial * (k - b).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hbk).symm
  have hb0 : (b.factorial : ℂ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have hc0 : (k.choose b : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hbk).ne'
  have he0 : ((k - b).factorial : ℂ) ≠ 0 := by exact_mod_cast (k - b).factorial_ne_zero
  rw [e, smul_assoc, map_smul, smul_eq_mul, h4]
  field_simp

theorem UpperTheory.ConvolutionTheory.FX.rearrange :
    PositivityTheory.Rg.Fx.Rearrange := by
  intro ι κ _ b A M _ _ _ _ _ _ D τ φ hT F m
  set ξ : ι → A := fun i => algebraMap ℂ A (b.Λ i) + ∑ j, (b.emb i j : ℂ) • D j with hξ
  have hA : ∀ (f : EP ι) (m : M), HasSum (fun k => φ (aeval ξ (piece k f) • m)) (φ (lift D τ (aff b.Λ b.emb f) • m)) := by
    intro f m
    induction f using AddMonoidAlgebra.induction_linear with
    | zero =>
      simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.1, map_zero, zero_smul]
      exact hasSum_zero
    | add f g hf hg =>
      simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).1 f g, map_add (f := _), add_smul]
      exact hf.add hg
    | single v p =>
      set c : ℂ := ∑ i, (v i : ℂ) * b.Λ i with hc
      set t := τ (Multiplicative.ofAdd (Matrix.vecMul v b.emb)) with ht
      have hl : aeval ξ (lin v) = algebraMap ℂ A c + ∑ j, ((Matrix.vecMul v b.emb j : ℝ) : ℂ) • D j := by

        simp only [lin, map_sum, map_mul, aeval_C, aeval_X, hξ, hc, mul_add, Finset.sum_add_distrib, Matrix.vecMul, dotProduct,
        Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul, Finset.mul_sum, Algebra.smul_def, mul_assoc]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul, mul_assoc]
      have hp : ∀ q : MvPolynomial ι ℂ, lift D τ (aeval (fun i => (AddMonoidAlgebra.single 0 (C (b.Λ i) + lin (b.emb i)) : EP (Fin b.r))) q) =
          aeval ξ q := fun q => by
        induction q using MvPolynomial.induction_on with
        | C a => simp [AddMonoidAlgebra.coe_algebraMap, lift_single]
        | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
        | mul_X p j hp =>
          rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, lift_single]
          simp [hξ, lin, Algebra.smul_def]
      have hv : lift D τ (aff b.Λ b.emb (AddMonoidAlgebra.single v p)) = aeval ξ p * (Complex.exp c • t) := by
        rw [aff, lift_single, map_mul, hp]
        simp [affChar, expChar, lift_single, Algebra.smul_def, hc, ht]
      have h1 := shift_sum (fun a k => (k.factorial : ℂ)⁻¹ * φ (aeval ξ (lin v) ^ k • aeval ξ (homogeneousComponent a p) • m))
        (fun a => Complex.exp c * φ (t • aeval ξ (homogeneousComponent a p) • m)) p.totalDegree
        (fun a ha k => by rw [homogeneousComponent_eq_zero a p ha]; simp)
        (fun a => by rw [hl]; exact exp_sum φ _ c _ _ (hT _ _))
      convert h1 using 1
      · funext k

        rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.2, map_sum, Finset.sum_smul, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul, aeval_C, map_pow, mul_comm, ← Algebra.smul_def, smul_mul_assoc, smul_assoc, map_smul, mul_smul,
          smul_eq_mul]

      · rw [hv, ← Finset.mul_sum, ← map_sum, ← Finset.smul_sum, ← Finset.sum_smul, ← map_sum, sum_homogeneousComponent,
        mul_comm, smul_mul_assoc, smul_assoc, map_smul, mul_smul, smul_eq_mul]
  have h2 := hasSum_sum (s := F.support) fun β _ => hA (F.coeff β) ((β.prod fun k e => lift D τ (b.h k) ^ e) • m)
  convert (preTransparency := .reducible) h2 using 1
  · funext k

    rw [pieceK, eval₂_sum, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [eval₂_monomial, mul_smul]
    rfl
  · conv_lhs => rw [F.as_sum]

    rw [map_sum, map_sum, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Fam.sub, eval₂Hom_monomial, map_mul, mul_smul, map_finsuppProd]
    simp only [map_pow]
end
