module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.ClopenEqualizer

theorem exists_isClopen_equalizer {P C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (a b : P ⟶ C)
    (h : a ≫ c = b ≫ c) :
    ∃ (U : Set P), IsClopen U ∧ ∀ (T : Scheme.{0}) (y : T ⟶ P), y ≫ a = y ≫ b ↔ Set.range y ⊆ U := by
  let d := pullback.diagonal c
  let l : P ⟶ pullback c c := pullback.lift a b h
  haveI : IsOpenImmersion d := inferInstance
  haveI : IsClosedImmersion d := inferInstance
  let j : pullback l d ⟶ P := pullback.fst l d
  have hj : j ≫ a = j ≫ b := by
    have h0 : j ≫ l = pullback.snd l d ≫ d := pullback.condition
    have h1 := congrArg (· ≫ pullback.fst c c) h0
    have h2 := congrArg (· ≫ pullback.snd c c) h0
    simp [l, d, pullback.lift_fst, pullback.lift_snd] at h1 h2
    rw [h1, h2]
  refine ⟨Set.range j, ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩, ?_⟩
  intro T y
  constructor
  · intro hy
    have e : y ≫ l = (y ≫ a) ≫ d := by
      apply pullback.hom_ext
      · simp [l, d, pullback.lift_fst]
      · simp [l, d, hy, pullback.lift_snd]
    have e2 : pullback.lift y (y ≫ a) e ≫ j = y := pullback.lift_fst _ _ _
    rintro _ ⟨t, rfl⟩
    refine ⟨pullback.lift y (y ≫ a) e t, ?_⟩
    rw [← Scheme.Hom.comp_apply, e2]
  · intro hy
    rw [← IsOpenImmersion.lift_fac j y hy, Category.assoc, Category.assoc, hj]

end GlobalTheory.ClopenEqualizer
end

section

namespace GlobalTheory.AnalyticMatrixEntries

universe u_1 u_2

theorem analyticAt_entry {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {ι : Type*} (b : Module.Basis ι ℂ E) {A : X → E →L[ℂ] E} {a : X}
    (hA : AnalyticAt ℂ A a) (i j : ι) :
    AnalyticAt ℂ (fun z : X ↦ b.repr (A z (b j)) i) a := by
  let L : (E →L[ℂ] E) →L[ℂ] ℂ :=
    (LinearMap.toContinuousLinearMap (b.coord i)).comp (ContinuousLinearMap.apply ℂ E (b j))
  have h := (L.analyticAt (A a)).comp hA
  convert h using 1
  funext z
  simp [L, Module.Basis.coord_apply]

theorem analyticAt_det {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : X → E →L[ℂ] E} {a : X} (hA : AnalyticAt ℂ A a) :
    AnalyticAt ℂ (fun z : X ↦ LinearMap.det (A z : E →ₗ[ℂ] E)) a := by
  let b := Module.finBasis ℂ E
  have hfun : (fun z : X => LinearMap.det (A z : E →ₗ[ℂ] E)) =
      fun z => ∑ σ : Equiv.Perm (Fin (Module.finrank ℂ E)),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, b.repr (A z (b i)) (σ i) := by
    funext z
    rw [← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [LinearMap.toMatrix_apply]
  rw [hfun]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ?_)
  exact analyticAt_entry b hA (σ i) i

end GlobalTheory.AnalyticMatrixEntries
end

section

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

theorem eq_zero_of_norm_real_mul_le {c : ℂ} {C : ℝ} (h : ∀ r : ℝ, ‖(r : ℂ) * c‖ ≤ C) : c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h0 : 0 ≤ C := (norm_nonneg _).trans (h 0)
  have key := h ((C + 1) / ‖c‖)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hpos.le), div_mul_cancel₀ _ hpos.ne'] at key
  linarith

theorem entire_sub_conj_bounded_const {φ : ℂ → ℂ} {b : ℂ} {C : ℝ} (hφ : Differentiable ℂ φ)
    (h : ∀ s, ‖φ s - (starRingEnd ℂ) s * b‖ ≤ C) : b = 0 ∧ ∀ s, φ s = φ 0 := by

  have hshift : ∀ a s, φ (s + a) - φ s = φ a - φ 0 := by
    intro a
    have hd : Differentiable ℂ (fun s => φ (s + a) - φ s) :=
      (hφ.comp (differentiable_id.add_const a)).sub hφ
    have hbd : Bornology.IsBounded (Set.range (fun s => φ (s + a) - φ s)) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨2 * C + ‖(starRingEnd ℂ) a * b‖, ?_⟩
      rintro _ ⟨s, rfl⟩
      show ‖φ (s + a) - φ s‖ ≤ _
      have e : φ (s + a) - φ s = ((φ (s + a) - (starRingEnd ℂ) (s + a) * b)
          - (φ s - (starRingEnd ℂ) s * b)) + (starRingEnd ℂ) a * b := by
        rw [map_add (f := _)]; ring
      rw [e]
      calc _ ≤ ‖(φ (s + a) - (starRingEnd ℂ) (s + a) * b) - (φ s - (starRingEnd ℂ) s * b)‖
            + ‖(starRingEnd ℂ) a * b‖ := norm_add_le _ _
        _ ≤ (‖φ (s + a) - (starRingEnd ℂ) (s + a) * b‖ + ‖φ s - (starRingEnd ℂ) s * b‖)
            + ‖(starRingEnd ℂ) a * b‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith [h (s + a), h s]
    intro s
    simpa [zero_add] using hd.apply_eq_apply_of_bounded hbd s 0

  have hderiv : ∀ s, deriv φ s = deriv φ 0 := by
    intro s
    have e1 : (fun x => φ (x + s)) = fun x => φ x + (φ s - φ 0) := by
      funext x
      linear_combination hshift s x
    have e2 := congrArg (fun f => deriv f 0) e1
    simp only [deriv_comp_add_const, deriv_add_const, zero_add] at e2
    exact e2

  obtain ⟨β, hlin⟩ : ∃ β : ℂ, ∀ s, φ s = φ 0 + β * s := by
    refine ⟨deriv φ 0, fun s => ?_⟩
    have hd : Differentiable ℂ (fun s => φ s - deriv φ 0 * s) :=
      hφ.sub (differentiable_id.const_mul _)
    have hz : ∀ x, deriv (fun s => φ s - deriv φ 0 * s) x = 0 := by
      intro x
      have hx : HasDerivAt (fun s => φ s - deriv φ 0 * s) (deriv φ x - deriv φ 0 * 1) x :=
        (hφ x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul _)
      rw [hx.deriv, hderiv x]
      ring
    have := is_const_of_deriv_eq_zero hd hz s 0
    linear_combination this

  have hB : ∀ s, ‖β * s - (starRingEnd ℂ) s * b‖ ≤ C + ‖φ 0‖ := by
    intro s
    have e : β * s - (starRingEnd ℂ) s * b = (φ s - (starRingEnd ℂ) s * b) - φ 0 := by
      rw [hlin s]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [h s])
  have h1 : β - b = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB r
    rw [Complex.conj_ofReal] at hr
    calc ‖(r : ℂ) * (β - b)‖ = ‖β * (r : ℂ) - (r : ℂ) * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h2 : Complex.I * (β + b) = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB (r * Complex.I)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I] at hr
    calc ‖(r : ℂ) * (Complex.I * (β + b))‖
        = ‖β * ((r : ℂ) * Complex.I) - (r : ℂ) * -Complex.I * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h3 : β + b = 0 := (mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
  have hβ : β = 0 := by linear_combination (h1 + h3) / 2
  refine ⟨by linear_combination (h3 - h1) / 2, fun s => ?_⟩
  rw [hlin s, hβ, zero_mul, add_zero]

theorem entire_antilinear_periods_const :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v →
        (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) →
        t = 0 ∧ ∀ z, v z = v 0 := by
  intro g Λ hdisc hspan v t hv hper
  have : IsZLattice ℝ Λ := ⟨hspan⟩

  have hcont : Continuous (fun z => v z - t ⬝ᵥ star z) :=
    hv.continuous.sub (continuous_const.dotProduct continuous_star)
  have hperw : ∀ z w, w ∈ Λ → (fun z => v z - t ⬝ᵥ star z) (z + w) = (fun z => v z - t ⬝ᵥ star z) z := by
    intro z w hw
    simp only
    rw [hper ⟨w, hw⟩ z, star_add, dotProduct_add]
    ring
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (IsZLattice.isCompact_range_of_periodic Λ _ hcont hperw).isBounded

  have hline : ∀ d : Fin g → ℂ, t ⬝ᵥ star d = 0 ∧ ∀ s : ℂ, v (s • d) = v 0 := by
    intro d
    have hd : Differentiable ℂ (fun s : ℂ => v (s • d)) :=
      hv.comp (differentiable_id.smul_const d)
    have hb : ∀ s : ℂ, ‖v (s • d) - (starRingEnd ℂ) s * (t ⬝ᵥ star d)‖ ≤ M := by
      intro s
      have e : (starRingEnd ℂ) s * (t ⬝ᵥ star d) = t ⬝ᵥ star (s • d) := by
        rw [star_smul, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
      rw [e]
      exact hM _ ⟨s • d, rfl⟩
    obtain ⟨h1, h2⟩ := entire_sub_conj_bounded_const hd hb
    exact ⟨h1, fun s => by simpa using h2 s⟩
  refine ⟨?_, fun z => by simpa using (hline z).2 1⟩
  funext i
  have hi := (hline (Pi.single i 1)).1
  rw [← Pi.single_star, star_one, dotProduct_single, mul_one] at hi
  simpa using hi

end GlobalTheory
end

section

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

open Complex Matrix in
open scoped ContDiff BigOperators Real in
private lemma integral_Ioc_cexp_two_pi_I_int_mul (j : ℤ) :
    ∫ t, cexp (2 * π * I * (j : ℂ) * (t : ℂ)) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      if j = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hj
  · subst hj; simp
  · have hc : (2 * π * I * (j : ℂ)) ≠ 0 := by
      have : (j : ℂ) ≠ 0 := by exact_mod_cast hj
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hπ, this, I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : cexp (2 * π * I * (j : ℂ)) = 1 := by
      rw [show 2 * π * I * (j : ℂ) = j * (2 * π * I) by ring]
      exact exp_int_mul_two_pi_mul_I j
    simp [h1]


open Complex Matrix in
open scoped ContDiff BigOperators Real in
theorem _root_.GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), Summable (fun ν => ‖c ν‖) →
      (∀ x : Fin n → ℝ, ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = 0) →
      ∀ ν, c ν = 0 := by
  intro n c hc h μ
  set m : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1) with hm
  haveI : MeasureTheory.IsProbabilityMeasure m := ⟨by simp [m]⟩
  set P : MeasureTheory.Measure (Fin n → ℝ) := MeasureTheory.Measure.pi fun _ => m
  set G : (Fin n → ℤ) → (Fin n → ℝ) → ℂ := fun ν x =>
    c ν * ∏ k, cexp (2 * π * I * (((ν k - μ k : ℤ)) : ℂ) * (x k : ℂ)) with hG
  have hnorm : ∀ ν x, ‖G ν x‖ = ‖c ν‖ := by
    intro ν x
    simp only [G, norm_mul, norm_prod, Complex.norm_exp]
    simp [Complex.mul_re]
  have hint : ∀ ν, MeasureTheory.Integrable (G ν) P := by
    intro ν
    refine MeasureTheory.Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
      ‖c ν‖ (MeasureTheory.ae_of_all _ fun x => (hnorm ν x).le)
  have hval : ∀ ν, ∫ x, G ν x ∂P = if ν = μ then c ν else 0 := by
    intro ν
    simp only [G]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_fintype_prod_eq_prod (E := fun _ => ℝ)
      (μ := fun _ => m) (fun k (t : ℝ) => cexp (2 * π * I * (((ν k - μ k : ℤ)) : ℂ) * (t : ℂ)))]
    simp only [hm, integral_Ioc_cexp_two_pi_I_int_mul]
    by_cases hνμ : ν = μ
    · subst hνμ; simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hνμ
      rw [if_neg hνμ, Finset.prod_eq_zero (Finset.mem_univ k) (by simp [sub_eq_zero, hk]), mul_zero]
  have hsum : ∀ x, ∑' ν, G ν x = 0 := by
    intro x
    have hx := h x
    have : ∀ ν, G ν x = c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) *
        cexp (-(2 * π * I * ∑ k, (μ k : ℂ) * (x k : ℂ))) := by
      intro ν
      simp only [G, mul_assoc]
      congr 1
      rw [← Complex.exp_add, ← Complex.exp_sum]
      congr 1
      push_cast
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this]
    rw [tsum_mul_right, hx, zero_mul]
  have key := MeasureTheory.integral_tsum_of_summable_integral_norm hint
    (by simpa [hnorm] using hc)
  simp only [hval, hsum, MeasureTheory.integral_zero] at key
  rwa [tsum_ite_eq] at key

end GlobalTheory
end

section

namespace GlobalTheory.RationalIntegralCoordinates

theorem exists_coords {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) {z : ℂ}
    (hzK : z ∈ IntermediateField.adjoin ℚ ({r} : Set ℂ)) :
    ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * r := by
  have hint : IsIntegral ℚ r := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    simp [hr]
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hzK
  induction hzK using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap q => exact ⟨q, 0, by simp [eq_ratCast]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : ℂ) * e * hr

theorem conj_eq_neg {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) r = -r := by
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : r.re = 0 := by
    by_contra hne
    have him : r.im = 0 := by
      have hprod : r.re * r.im = 0 := by linarith
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h hne
      · exact h
    rw [him] at h1
    nlinarith [mul_self_nonneg r.re]
  apply Complex.ext <;> simp [hre]

theorem rat_int {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) : ∃ m : ℤ, (m : ℚ) = q := by
  have hq : IsIntegral ℤ q := by
    have hinj : Function.Injective (algebraMap ℚ ℂ).toIntAlgHom := (algebraMap ℚ ℂ).injective
    rw [← isIntegral_algHom_iff _ hinj]
    simpa [eq_ratCast] using h
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  exact ⟨m, by simpa using hm⟩

theorem int_of_prime_mul_sq {d : ℕ} (hd : d.Prime) {q : ℚ} {n : ℤ}
    (h : (d : ℚ) * q ^ 2 = n) : ∃ k : ℤ, (k : ℚ) = q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hz : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * n := by
    have hq : q = q.num / q.den := (Rat.num_div_den q).symm
    rw [hq, div_pow] at h
    field_simp at h
    exact_mod_cast h
  have hcop : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  have hdvd : (q.den : ℤ) ^ 2 ∣ d := hcop.dvd_of_dvd_mul_right ⟨n, hz⟩
  have hdvd' : q.den ∣ d := by
    have : q.den ^ 2 ∣ d := by exact_mod_cast hdvd
    exact (dvd_pow_self _ two_ne_zero).trans this
  rcases hd.eq_one_or_self_of_dvd _ hdvd' with h1 | h1
  · exact ⟨q.num, by rw [← Rat.den_eq_one_iff]; exact h1⟩
  · exfalso
    have h2 : q.den ^ 2 ∣ d := by exact_mod_cast hdvd
    rw [h1] at h2
    have h3 := Nat.le_of_dvd hd.pos h2
    have h4 := hd.two_le
    nlinarith

theorem main {d : ℕ} (hd : Nat.Prime d) (hd4 : d % 4 = 3) {r : ℂ} (hr : r ^ 2 = -(d : ℂ))
    (T : Subring ℂ) (hT : (1 + r) / 2 ∈ T) {z : ℂ}
    (hzK : z ∈ IntermediateField.adjoin ℚ ({r} : Set ℂ)) (hz : IsIntegral ℤ z) : z ∈ T := by
  have hd0 : 0 < d := hd.pos
  obtain ⟨a, b, rfl⟩ := exists_coords hd0 hr hzK
  have hc : starRingEnd ℂ ((a : ℂ) + b * r) = a - b * r := by
    rw [map_add (f := _), map_mul, conj_eq_neg hd0 hr, map_ratCast, map_ratCast]
    ring
  have hcz : IsIntegral ℤ (starRingEnd ℂ ((a : ℂ) + b * r)) := hz.map (starRingEnd ℂ).toIntAlgHom
  have htr : IsIntegral ℤ (((2 * a : ℚ)) : ℂ) := by
    have e : (((2 * a : ℚ)) : ℂ) = ((a : ℂ) + b * r) + starRingEnd ℂ ((a : ℂ) + b * r) := by
      rw [hc]
      push_cast
      ring
    rw [e]
    exact hz.add hcz
  have hnm : IsIntegral ℤ (((a ^ 2 + d * b ^ 2 : ℚ)) : ℂ) := by
    have e : (((a ^ 2 + d * b ^ 2 : ℚ)) : ℂ) =
        ((a : ℂ) + b * r) * starRingEnd ℂ ((a : ℂ) + b * r) := by
      rw [hc]
      push_cast
      linear_combination (b : ℂ) ^ 2 * hr
    rw [e]
    exact hz.mul hcz
  obtain ⟨m, hm⟩ := rat_int htr
  obtain ⟨N, hN⟩ := rat_int hnm
  obtain ⟨k, hk⟩ := int_of_prime_mul_sq hd (q := 2 * b) (n := 4 * N - m ^ 2) (by
    push_cast
    rw [hm, hN]
    ring)
  have heq : m ^ 2 + (d : ℤ) * k ^ 2 = 4 * N := by
    have : ((m ^ 2 + (d : ℤ) * k ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [hm, hk, hN]
      ring
    exact_mod_cast this
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (d : ℤ) = 4 * t + 3 := ⟨(d / 4 : ℕ), by omega⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, m - k = 2 * j := by
    obtain ⟨u, hu | hu⟩ := Int.even_or_odd' m <;> obtain ⟨v, hv | hv⟩ := Int.even_or_odd' k
    · exact ⟨u - v, by omega⟩
    · exfalso
      obtain ⟨X, hX⟩ : ∃ X : ℤ, (d : ℤ) = 4 * X :=
        ⟨N - u ^ 2 - d * (v ^ 2 + v), by rw [hu, hv] at heq; linear_combination heq⟩
      omega
    · exfalso
      obtain ⟨X, hX⟩ : ∃ X : ℤ, (1 : ℤ) = 4 * X :=
        ⟨N - u ^ 2 - u - d * v ^ 2, by rw [hu, hv] at heq; linear_combination heq⟩
      omega
    · exact ⟨u - v, by omega⟩
  have hm' : (m : ℂ) = 2 * a := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) hm
  have hk' : (k : ℂ) = 2 * b := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) hk
  have hj' : (m : ℂ) - k = 2 * j := by exact_mod_cast hj
  have hsplit : (a : ℂ) + b * r = (j : ℂ) + (k : ℂ) * ((1 + r) / 2) := by
    linear_combination (-1 / 2 : ℂ) * hm' + (-r / 2) * hk' + (1 / 2 : ℂ) * hj'
  rw [hsplit]
  exact T.add_mem (intCast_mem T j) (T.mul_mem (intCast_mem T k) hT)

end GlobalTheory.RationalIntegralCoordinates
end
