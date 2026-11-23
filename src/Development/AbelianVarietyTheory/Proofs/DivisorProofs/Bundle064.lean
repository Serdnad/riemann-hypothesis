module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Continuity
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_norm_pow_mul_le_sqrt_weighted_sq :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  intro E F _ _ _ _ _ μ _ _
  set s : ℕ := finrank ℝ E + 1 with hs
  have hfin : ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ < ∞ := by
    apply finite_integral_one_add_norm
    rw [hs]; push_cast
    have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    linarith
  set A := ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ with hA
  set B : ℝ≥0∞ := ENNReal.ofReal (2 ^ (2 * s - 1)) with hB
  refine ⟨A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin.ne)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  intro H hH k
  let f : E → ℝ≥0∞ := fun z => ENNReal.ofReal (((1 + ‖z‖) ^ s)⁻¹)
  let g : E → ℝ≥0∞ := fun z => ENNReal.ofReal ((1 + ‖z‖) ^ s * (‖z‖ ^ k * ‖H z‖))
  have hf : AEMeasurable f μ := by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    exact ((measurable_const.add measurable_norm).pow_const s).inv
  have hg : AEMeasurable g μ := by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    fun_prop
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have h1 : ∀ z, (f * g) z = ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) := by
    intro z
    have hp : 0 < (1 + ‖z‖) ^ s := by positivity
    simp only [Pi.mul_apply, f, g]
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  have h2 : ∀ z, f z ^ (2 : ℝ) = ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) := by
    intro z
    simp only [f]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two, inv_pow, ← pow_mul,
      mul_comm]
  have h3 : ∀ z, g z ^ (2 : ℝ) ≤ B * (ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) +
      ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2)) := by
    intro z
    simp only [g, hB]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h := add_pow_le (zero_le_one) (norm_nonneg z) (2 * s)
    rw [Real.rpow_two, add_assoc, ← hs]
    calc ((1 + ‖z‖) ^ s * (‖z‖ ^ k * ‖H z‖)) ^ 2
        = (1 + ‖z‖) ^ (2 * s) * (‖z‖ ^ k * ‖H z‖) ^ 2 := by ring
      _ ≤ (2 ^ (2 * s - 1) * (1 ^ (2 * s) + ‖z‖ ^ (2 * s))) * (‖z‖ ^ k * ‖H z‖) ^ 2 := by
        gcongr
      _ = _ := by rw [one_pow]; ring
  simp only [h1, h2] at key
  refine key.trans ?_
  rw [← hA, mul_assoc, ← ENNReal.mul_rpow_of_nonneg B _ (by norm_num)]
  refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num))
  have hm : Measurable fun z : E => ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    fun_prop
  rw [← lintegral_add_left hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono h3

end GlobalTheory
end

section

open Filter Real

namespace GlobalTheory

theorem eventually_const_mul_rpow_le_rpow (a b c : ℝ) (h : a < b) :
    ∀ᶠ x : ℝ in atTop, c * x ^ a ≤ x ^ b := by
  have ht := tendsto_rpow_atTop (sub_pos.2 h)
  filter_upwards [ht.eventually_ge_atTop c, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have e : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

theorem sqrt_mul_rpow_neg_eq (eps x : ℝ) (hx : 0 < x) :
    Real.sqrt (x * x ^ (-(eps / 8))) = x ^ (1 / 2 - eps / 16) := by
  have h1 : x * x ^ (-(eps / 8)) = x ^ (1 - eps / 8) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  ring_nf

theorem five_elementary_inequalities_eventually :
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧
      11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧
      2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧
      44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
  intro eps he he1
  have h1 := eventually_const_mul_rpow_le_rpow (eps / 4) eps 20 (by linarith)
  have h2 := eventually_const_mul_rpow_le_rpow (eps / 3) eps 20 (by linarith)
  have h3 := eventually_const_mul_rpow_le_rpow 0 eps 20 he
  have h4 := (isLittleO_log_rpow_atTop he).bound (show (0:ℝ) < 1 / 60 by norm_num)
  have h5 := eventually_const_mul_rpow_le_rpow 0 (eps / 5) 11 (by linarith)
  have h6 := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1 / 4 by norm_num)
  have h7 := eventually_const_mul_rpow_le_rpow (eps / 5 + eps / 100) (1 / 2 - eps / 16) 2
    (by linarith)
  have h8 := eventually_const_mul_rpow_le_rpow 0 (1 / 2 - eps / 16) 44 (by linarith)
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, eventually_gt_atTop (0 : ℝ)]
    with x h1 h2 h3 h4 h5 h6 h7 h8 hx
  rw [Real.rpow_zero] at h3 h5 h8
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)] at h4
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx] at h6
  rw [sqrt_mul_rpow_neg_eq eps x hx]
  have hl := le_abs_self (Real.log x)
  refine ⟨by linarith, by linarith, ?_, h7, by linarith⟩
  nlinarith [abs_nonneg (Real.log x), sq_abs (Real.log x)]

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

theorem hermitian_dotProduct_mulVec_star_swap {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ)
    (hH : H.IsHermitian) (x y : Fin g → ℂ) :
    y ⬝ᵥ H.mulVec (star x) = (starRingEnd ℂ) (x ⬝ᵥ H.mulVec (star y)) := by

  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := hH.apply j i
  simp only [Complex.star_def, Complex.conj_conj] at h ⊢
  rw [h]
  ring

theorem pi_mul_hermitian_alternation {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ)
    (hH : H.IsHermitian) (x y : Fin g → ℂ) :
    (Real.pi : ℂ) * (y ⬝ᵥ H.mulVec (star x)) - Real.pi * (x ⬝ᵥ H.mulVec (star y)) =
      (((-1 : ℤˣ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) *
        ((x ⬝ᵥ H.mulVec (star y)).im : ℂ) := by
  rw [hermitian_dotProduct_mulVec_star_swap H hH x y]
  set a := x ⬝ᵥ H.mulVec (star y)
  have h := Complex.sub_conj a
  push_cast at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  linear_combination (-(Real.pi : ℂ)) * h

end GlobalTheory
end

section

namespace GlobalTheory.CMModel

theorem cubic_three_roots (g h e₁ e₂ e₃ : ℂ) (h₁ : 4 * e₁ ^ 3 - g * e₁ - h = 0)
    (h₂ : 4 * e₂ ^ 3 - g * e₂ - h = 0) (h₃ : 4 * e₃ ^ 3 - g * e₃ - h = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    (∀ x, 4 * x ^ 3 - g * x - h = 4 * (x - e₁) * (x - e₂) * (x - e₃)) ∧
      16 * ((3 * e₁ ^ 2 - g / 4) * (3 * e₂ ^ 2 - g / 4) * (3 * e₃ ^ 2 - g / 4))
        = -(g ^ 3 - 27 * h ^ 2) := by
  have a : g = 4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₂)
    linear_combination h₂ - h₁
  have b : g = 4 * (e₁ ^ 2 + e₁ * e₃ + e₃ ^ 2) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₃)
    linear_combination h₃ - h₁
  have c : e₃ = -e₁ - e₂ := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₂₃)
    linear_combination (b - a) / 4
  have d : h = 4 * e₁ ^ 3 - g * e₁ := by linear_combination -h₁
  subst c
  rw [d, a]
  exact ⟨fun x => by ring, by ring⟩

end GlobalTheory.CMModel
end

section

namespace GlobalTheory

theorem exists_perm_of_univ_map_eq {ι β : Type} [Fintype ι] (g g' : ι → β)
    (h : Finset.univ.val.map g = Finset.univ.val.map g') :
    ∃ π : Equiv.Perm ι, ∀ i, g (π i) = g' i := by
  classical
  have hc : ∀ c, Fintype.card {i // g' i = c} = Fintype.card {i // g i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this.symm
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

theorem eq_of_perm_inv_invariant_of_multiset_eq :
    ∀ (m : ℕ) (f : (Fin m → ℂ) → ℂ), (∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) → (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧ ∀ i, f (Function.update α i (α i)⁻¹) = f α) → ∀ α α' : Fin m → ℂ, (∀ i, α i ≠ 0) → Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) = Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) → f α = f α' := by
  classical
  intro m f hf α α' hα h
  have hα' : ∀ i, α' i ≠ 0 := by
    intro i hi
    have hmem : (0 : ℂ) ∈ Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, hi⟩))
    rw [← h] at hmem
    rcases Multiset.mem_add.1 hmem with h1 | h1
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j hj
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j (inv_eq_zero.1 hj)
  have h2 := congrArg (Multiset.map (fun x : ℂ => x + x⁻¹)) h
  simp only [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => (γ i)⁻¹ + γ i) = fun i => γ i + (γ i)⁻¹ :=
    fun γ => funext fun i => add_comm _ _
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => α i + (α i)⁻¹)
      = Finset.univ.val.map (fun i => α' i + (α' i)⁻¹) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    have h4 := hπ i
    have ha := hα (π i)
    have hb := hα' i
    have h5 : (α' i - α (π i)) * (α' i * α (π i) - 1) = 0 := by
      field_simp at h4
      linear_combination -h4
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact Or.inl (sub_eq_zero.1 h6)
    · exact Or.inr (eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h6))
  have hβ : ∀ i, (α ∘ π) i ≠ 0 := fun i => hα _
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      have hne : ∀ i, (fun i => if i ∈ s then α' i else (α ∘ π) i) i ≠ 0 := by
        intro i
        by_cases hi : i ∈ s
        · simpa [hi] using hα' i
        · simpa [hi] using hα (π i)
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf _ hne).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α hα).1 π, ← this]

end GlobalTheory
end

section

open Module

namespace GlobalTheory

theorem semilinear_pi_eq_sum_single {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W]
    [Module ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ k, σ (x k) • j (Pi.single k 1) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]

  rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]

theorem span_range_inf_ker_eq_span_rational_ker {K : Type} [Field K] (σ : K →+* ℂ) {W E : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] {n d : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : (Fin d → K) →ₛₗ[σ] E) (f : W →ₗ[ℂ] E)
    (M : Matrix (Fin d) (Fin n) K)
    (hli : LinearIndependent ℂ (fun l => j' (Pi.single l 1)))
    (hf : ∀ x, f (j x) = j' (M.mulVec x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f
      = Submodule.span ℂ (j '' {x | M.mulVec x = 0}) := by
  classical
  apply le_antisymm
  · rintro w ⟨hw, hw0⟩
    have hle : Submodule.span ℂ (Set.range j)
        ≤ Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [semilinear_pi_eq_sum_single σ j x]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hw)
    have h0 : f (∑ k, c k • j (Pi.single k 1)) = 0 := hw0
    have h1 : ∑ l, (∑ k, σ (M l k) * c k) • j' (Pi.single l 1) = 0 := by

      rw [← h0, map_sum]
      simp only [map_smul, hf, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [semilinear_pi_eq_sum_single σ j' (M.mulVec _), Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, mul_comm]
      simp
    have h2 : ∀ l, ∑ k, σ (M l k) * c k = 0 := Fintype.linearIndependent_iff.1 hli _ h1
    letI : Algebra K ℂ := σ.toAlgebra
    let b := Basis.ofVectorSpace K ℂ
    let s := Finset.univ.biUnion fun k => (b.repr (c k)).support
    have hc : ∀ k, c k = ∑ i ∈ s, σ (b.repr (c k) i) * b i := by
      intro k
      have h3 := b.linearCombination_repr (c k)
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (s := s)
          (Finset.subset_biUnion_of_mem (fun k => (b.repr (c k)).support) (Finset.mem_univ k))
          _ (by simp)] at h3
      exact h3.symm
    have hw' : ∑ k, c k • j (Pi.single k 1) = ∑ i ∈ s, b i • j (fun k => b.repr (c k) i) := by
      have h5 : ∀ i, b i • j (fun k => b.repr (c k) i)
          = ∑ k, b i • σ (b.repr (c k) i) • j (Pi.single k 1) := fun i => by
        rw [semilinear_pi_eq_sum_single σ j (fun k => b.repr (c k) i), Finset.smul_sum]
      rw [Finset.sum_congr rfl fun i _ => h5 i, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hc k, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm]
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    ext l
    have h4 : b.repr (∑ k, M l k • c k) i = 0 := by
      have : ∑ k, M l k • c k = 0 := h2 l
      rw [this]; simp

    rw [map_sum, Finsupp.finsetSum_apply] at h4
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h4
    exact h4
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩
    have hx' : M.mulVec x = 0 := hx
    change f (j x) = 0
    rw [hf, hx', map_zero]

end GlobalTheory
end

section

set_option autoImplicit false

namespace GlobalTheory.FGFieldEmb

open Cardinal

theorem nonempty_ringHom_complex_of_mk_le (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

theorem nonempty_ringHom_complex_of_fg :
    ∀ (K : Type) [Field K] [CharZero K] (k : IntermediateField ℚ K), k.FG → Nonempty (k →+* ℂ) := by
  intro K _ _ k hk
  obtain ⟨t, rfl⟩ := hk
  refine nonempty_ringHom_complex_of_mk_le _ ?_
  refine le_trans ?_ Cardinal.aleph0_le_continuum
  refine (IntermediateField.cardinalMk_adjoin_le ℚ (t : Set K)).trans ?_
  refine max_le (max_le ?_ ?_) le_rfl
  · simp [Cardinal.mkRat]
  · exact (Cardinal.lt_aleph0_of_finite _).le

end GlobalTheory.FGFieldEmb
end
