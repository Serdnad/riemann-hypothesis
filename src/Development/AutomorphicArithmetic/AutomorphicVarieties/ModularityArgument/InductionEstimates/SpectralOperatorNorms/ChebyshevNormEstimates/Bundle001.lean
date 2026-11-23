module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenPiecesK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem specSum_op {d : ℕ} (a Y : Eu d →L[ℂ] Eu d) (y : ℝ → ℂ) (sp : Finset ℝ) (ha : 0 ≤ a) (hc : Commute a Y)
    (hsp : ∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ) ≠ ⊥)
    (hY : ∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ), Y v = y x • v) (w : Eu d) :
    a (Y w) = ∑ x ∈ sp, ((x : ℂ) * y x) • eigP a x w := by
  have hpos : a.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive).1 ha
  have hsym : (a : Eu d →ₗ[ℂ] Eu d).IsSymmetric := hpos.isSymmetric
  have htop : (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hsym.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hw : w ∈ (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ) := htop ▸ Submodule.mem_top
  induction hw using Submodule.iSup_induction' with
  | zero => simp
  | add u v _ _ hu hv => simp only [map_add (f := _), hu, hv, smul_add, Finset.sum_add_distrib]
  | mem μ v hv =>
    by_cases h0 : v = 0
    · subst h0; simp
    have hav : a v = μ • v := Module.End.mem_eigenspace_iff.1 hv
    have hev : Module.End.HasEigenvalue (a : Eu d →ₗ[ℂ] Eu d) μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, h0⟩
    have hre : (starRingEnd ℂ) μ = μ := hsym.conj_eigenvalue_eq_self hev
    obtain ⟨r, rfl⟩ : ∃ r : ℝ, μ = r := ⟨μ.re, (Complex.conj_eq_iff_re.1 hre).symm⟩
    have hr : 0 ≤ r := by
      have h1 := hpos.re_inner_nonneg_right v
      rw [hav, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
      have h2 : 0 < ‖v‖ ^ 2 := by positivity
      have h3 : RCLike.re ((r : ℂ) * ((‖v‖ : ℂ)) ^ 2) = r * ‖v‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; simp only [RCLike.re_to_complex, Complex.ofReal_re]
      have h4 : 0 ≤ r * ‖v‖ ^ 2 := by rw [← h3]; exact h1
      exact nonneg_of_mul_nonneg_left h4 h2
    have hne : ∀ x : ℝ, x ≠ r → eigP a x v = 0 := by
      intro x hx
      unfold eigP
      rw [Submodule.starProjection_apply_eq_zero_iff]
      intro u hu
      have hx' : (x : ℂ) ≠ r := by exact_mod_cast hx
      exact hsym.orthogonalFamily_eigenspaces hx' ⟨u, hu⟩ ⟨v, hv⟩
    have heq : eigP a r v = v := Submodule.starProjection_eq_self_iff.2 hv
    rcases hr.eq_or_lt with h | h
    · have h1 : a (Y v) = Y (a v) := congrArg (fun T : Eu d →L[ℂ] Eu d => T v) hc.eq
      rw [h1, hav, ← h]
      simp only [Complex.ofReal_zero, zero_smul, map_zero]
      refine (Finset.sum_eq_zero fun x hx => ?_).symm
      rw [hne x (h ▸ ((hsp x).1 hx).1.ne'), smul_zero]
    · have hm : r ∈ sp := (hsp r).2 ⟨h, hev⟩
      rw [Finset.sum_eq_single_of_mem r hm fun x _ hx => by rw [hne x hx, smul_zero], heq, hY r h v hv, map_smul, hav,
        smul_smul, mul_comm]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.specSum :
    ∀ {d d' : ℕ} (a Y Z : Eu d' →L[ℂ] Eu d') (N : Eu d' →ₗ[ℂ] Eu d) (s : Eu d →ₗ[ℂ] Eu d') (y : ℝ → ℂ) (sp : Finset ℝ), 0 ≤ a → Commute a Y →
      (∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (a : Eu d' →ₗ[ℂ] Eu d') (x : ℂ) ≠ ⊥) →
      (∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : Eu d' →ₗ[ℂ] Eu d') (x : ℂ), Y v = y x • v) →
      LinearMap.trace ℂ (Eu d) (N ∘ₗ ((a ∘L Y ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) =
        ∑ x ∈ sp, x * y x * LinearMap.trace ℂ (Eu d) (N ∘ₗ ((eigP a x ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) := by
  intro d d' a Y Z N s y sp ha hc hsp hY
  have key : (N ∘ₗ ((a ∘L Y ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) =
      ∑ x ∈ sp, ((x : ℂ) * y x) • (N ∘ₗ ((eigP a x ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) := by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.sum_apply]
    change N (a (Y (Z (s w)))) = ∑ x ∈ sp, ((x : ℂ) * y x) • N (eigP a x (Z (s w)))

    rw [specSum_op a Y y sp ha hc hsp hY, map_sum]
    simp only [map_smul]

  rw [key, map_sum]
  simp only [map_smul, smul_eq_mul]
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem chebyshev_image_norm_le {A B : Type} [CommRing A] [Algebra ℂ A] [NormedRing B] (φ : A →+* B)
    (h1 : ‖(1 : B)‖ ≤ 1) (y : A) (r : ℝ) (hr : ‖φ y‖ ≤ r) (m : ℕ) :
    ‖φ (Polynomial.aeval y (Polynomial.Chebyshev.T ℂ (m : ℤ)))‖ ≤ (2 * r + 1) ^ m := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  induction m using Nat.twoStepInduction with
  | zero => simpa using h1
  | one =>
    have : ‖φ y‖ ≤ 2 * r + 1 := by linarith
    simpa using this
  | more m ih0 ih1 =>
    have e : Polynomial.Chebyshev.T ℂ ((m + 2 : ℕ) : ℤ) =
        Polynomial.X * Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ) +
          Polynomial.X * Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ) - Polynomial.Chebyshev.T ℂ (m : ℤ) := by
      push_cast
      rw [Polynomial.Chebyshev.T_add_two]
      ring
    rw [e, map_sub, map_add (f := _), map_mul, Polynomial.aeval_X, map_sub, map_add (f := _), map_mul]
    set u := φ (Polynomial.aeval y (Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ)))
    set v := φ (Polynomial.aeval y (Polynomial.Chebyshev.T ℂ (m : ℤ)))
    have hp : ‖φ y * u‖ ≤ r * (2 * r + 1) ^ (m + 1) :=
      (norm_mul_le _ _).trans (mul_le_mul hr ih1 (norm_nonneg _) hr0)
    have hq : (2 * r + 1) ^ m ≤ (2 * r + 1) ^ (m + 1) :=
      pow_le_pow_right₀ (by linarith) (Nat.le_succ m)
    have h2 := norm_sub_le (φ y * u + φ y * u) v
    have h3 := norm_add_le (φ y * u) (φ y * u)
    have h4 : (2 * r + 1) ^ (m + 2) = (2 * r + 1) * (2 * r + 1) ^ (m + 1) := by ring
    rw [h4]
    linarith

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.chebSB :
    ∀ {K : Type} [Field K] [NumberField K] {n d : ℕ} (evz : ℂ → PR K n →+* (Eu d →L[ℂ] Eu d)), (∀ z (c : ℂ), evz z (C (C c)) = c • 1) → ∀ M₀, SB (fun z => evz z (C (X none))) M₀ →
      ∃ M₁ : ℝ, 4 ≤ M₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ m : ℕ, SB (fun z => evz z (chebP η m)) ((M₁ / η) ^ m) := by
  intro K _ _ n d evz hc M₀ hM
  have hM0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM 0 (by simp))
  refine ⟨4 * M₀ + 4, by linarith, fun η hη hη1 m z hz => ?_⟩
  have h1 : ‖(1 : Eu d →L[ℂ] Eu d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hX : ‖evz z (C (X none))‖ ≤ M₀ := hM z hz
  have h2η : 0 ≤ 2 / η := by positivity
  have hy : ‖((evz z).comp C) (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ)‖
      ≤ 2 / η * M₀ + 1 := by
    rw [map_sub, map_mul, map_one, RingHom.comp_apply, RingHom.comp_apply, hc, smul_mul_assoc, one_mul]
    refine (norm_sub_le _ _).trans (add_le_add ?_ h1)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h2η]
    exact mul_le_mul_of_nonneg_left hX h2η
  have := chebyshev_image_norm_le ((evz z).comp C) h1 _ _ hy m
  refine this.trans (pow_le_pow_left₀ (by positivity) ?_ m)
  have h4 : 4 ≤ 4 / η := by rw [le_div_iff₀ hη]; linarith
  have e : (4 * M₀ + 4) / η = 2 * (2 / η * M₀) + 4 / η := by ring
  rw [e]
  linarith
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private theorem exTest (z : ℂ) (v : V) (R : ℝ) :
    ∃ x : L V, ∀ᵐ y : ℝ, y ∈ Set.Icc (-R) R → x y = Complex.exp (z * y) • v := by
  have hc : Continuous fun y : ℝ => Complex.exp (z * y) • v := by fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hc.continuousOn
  have hm : MemLp ((Set.Icc (-R) R).indicator fun y : ℝ => Complex.exp (z * y) • v) 2 volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
    exact MemLp.of_bound hc.aestronglyMeasurable C (ae_restrict_of_forall_mem measurableSet_Icc hC)
  refine ⟨hm.toLp _, ?_⟩
  filter_upwards [hm.coeFn_toLp] with y hy hm'
  rw [hy, Set.indicator_of_mem hm']

private theorem sumAe (S : Finset ℝ) (c : ℝ → V →L[ℂ] V) (x : L V) :
    ∀ᵐ y : ℝ, (∑ t ∈ S, (c t).compLpL 2 volume (sh V t x) : L V) y = ∑ t ∈ S, c t (x (y + t)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero V 2 (volume : Measure ℝ)] with y hy
    simpa using hy
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [ih, Lp.coeFn_add ((c a).compLpL 2 volume (sh V a x)) (∑ t ∈ S, (c t).compLpL 2 volume (sh V t x) : L V),
      (c a).coeFn_compLpL (sh V a x), sh_ae V a x] with y h1 h2 h3 h4
    rw [h2, Pi.add_apply, h1, h3, h4, Finset.sum_insert ha]

private theorem actTest (u : ℝ →₀ (V →L[ℂ] V)) (κ : ℝ → V →L[ℂ] V) (hk : Ker κ) (z : ℂ) (v : V) :
    ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → ∀ x : L V, (∀ᵐ y : ℝ, y ∈ Set.Icc (-R) R → x y = Complex.exp (z * y) • v) →
      ∀ᵐ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
        ((u.sum fun t c => c.compLpL 2 volume (sh V t x)) + conv κ x : L V) y =
          Complex.exp (z * y) • ((u.sum fun t c => Complex.exp (z * t) • c) + symb κ z) v := by
  obtain ⟨r, hr⟩ := (u.support.finite_toSet.isCompact.union hk.2.isCompact).isBounded.subset_closedBall (0 : ℝ)
  refine ⟨r + 1, fun R hR x hx => ?_⟩
  have hmem : ∀ t ∈ (u.support : Set ℝ) ∪ tsupport κ, ∀ y ∈ Set.Icc (0 : ℝ) 1, y + t ∈ Set.Icc (-R) R := by
    intro t ht y hy
    have := hr ht
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le] at this
    constructor <;> linarith [this.1, this.2, hy.1, hy.2]
  have hs : ∀ᵐ y : ℝ, ∀ t ∈ u.support, y + t ∈ Set.Icc (-R) R → x (y + t) = Complex.exp (z * (y + t : ℝ)) • v := by
    rw [Filter.eventually_all_finset]
    intro t _
    exact (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hx
  have hint : Integrable fun t : ℝ => Complex.exp (z * t) • κ t := by
    have h1 : Continuous fun t : ℝ => Complex.exp (z * t) := by fun_prop
    exact (h1.smul hk.1).integrable_of_hasCompactSupport (hk.2.smul_left (f := fun t : ℝ => Complex.exp (z * t)))
  filter_upwards [hs, sumAe u.support u x, (convSpec κ hk x).1,
    Lp.coeFn_add (u.sum fun t c => c.compLpL 2 volume (sh V t x) : L V) (conv κ x)] with y h1 h2 h3 h4 hy
  rw [h4, Pi.add_apply, h3, ContinuousLinearMap.add_apply, smul_add]
  congr 1
  · rw [Finsupp.sum, h2, Finsupp.sum, ContinuousLinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h1 t ht (hmem t (Or.inl ht) y hy), map_smul, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.exp_add]
    push_cast
    rw [mul_add]
  · rw [symb, ContinuousLinearMap.integral_apply hint, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_add_left volume y).quasiMeasurePreserving.ae hx] with t ht
    by_cases h : t ∈ tsupport κ
    · rw [ht (hmem t (Or.inr h) y hy), map_smul, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.exp_add]
      push_cast
      rw [mul_add]
    · simp [image_eq_zero_of_notMem_tsupport h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.actUniq :
    ∀ {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) (s s' : ℂ → V →L[ℂ] V), Act J Y s → Act J Y s' → s = s' := by
  rintro H V _ _ _ _ _ _ _ J Y s s' ⟨u, κ, hk, hY, hs⟩ ⟨u', κ', hk', hY', hs'⟩
  funext z
  ext1 v
  obtain ⟨R, hR⟩ := actTest u κ hk z v
  obtain ⟨R', hR'⟩ := actTest u' κ' hk' z v
  obtain ⟨x, hx⟩ := exTest z v (max R R')
  have e := J.injective ((hY x).symm.trans (hY' x))
  have h1 := hR _ (le_max_left R R') x hx
  have h2 := hR' _ (le_max_right R R') x hx
  rw [← hs] at h1
  rw [← hs', ← e] at h2
  by_contra hne
  have h3 : ∀ᵐ y : ℝ, y ∉ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [h1, h2] with y a b hy
    exact hne (smul_right_injective V (Complex.exp_ne_zero (z * y)) ((a hy).symm.trans (b hy)))
  have h4 : volume (Set.Icc (0 : ℝ) 1) = 0 := measure_eq_zero_iff_ae_notMem.2 h3
  simp at h4
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem homog_eq {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) :
    homog d p = ∑ α ∈ p.support,
      monomial (Finsupp.single none (d - α.degree) + α.mapDomain some) (p.coeff α) := by
  unfold homog
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [rename_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

private theorem deg_le {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) {α : ι →₀ ℕ}
    (hα : α ∈ p.support) : α.degree ≤ d := by
  have := (le_totalDegree hα).trans h
  simpa [Finsupp.degree_apply, Finsupp.sum] using this

private theorem deg_exp {ι : Type} {d : ℕ} {α : ι →₀ ℕ} (h : α.degree ≤ d) :
    (Finsupp.single none (d - α.degree) + α.mapDomain some : Option ι →₀ ℕ).degree = d := by
  rw [map_add (f := _), Finsupp.degree_single, Finsupp.degree_mapDomain]
  omega

private theorem trunc_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (d : ℕ)
    (G : ℕ → MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)) (s : Finset ((Pl K × Fin n) →₀ ℕ))
    (h : ∀ k, (G k).support ⊆ s) :
    trunc d G = ∑ β ∈ s, monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)) := by
  unfold trunc

  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_subset (h k) fun β _ hβ => ?_
  rw [notMem_support_iff.mp hβ]
  simp [homog]

private theorem mon_norm {σ : Type} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial σ ℂ →+* (H →L[ℂ] H)) {D : ℝ} (hD : 1 ≤ D) (hX : ∀ i, ‖ψ (X i)‖ ≤ D) (m : σ →₀ ℕ) :
    ‖ψ (monomial m 1)‖ ≤ D ^ m.degree := by
  have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  induction m using Finsupp.induction_linear with
  | zero => simpa using h1
  | add a b ha hb =>
    have : (monomial (a + b) 1 : MvPolynomial σ ℂ) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, map_add (f := _), pow_add]
    exact (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))
  | single i e =>
    rw [← X_pow_eq_monomial, map_pow, Finsupp.degree_single]
    induction e with
    | zero => simpa using h1
    | succ e ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih (hX i) (norm_nonneg _) (by positivity))

private theorem homog_norm {ι : Type} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial (Option ι) ℂ →+* (H →L[ℂ] H)) (hψ : ∀ c : ℂ, ψ (C c) = c • 1) {D : ℝ} (hD : 1 ≤ D)
    (hX : ∀ i, ‖ψ (X i)‖ ≤ D) (d : ℕ) (p : MvPolynomial ι ℂ) (hp : p.totalDegree ≤ d) :
    ‖ψ (homog d p)‖ ≤ l1 p * D ^ d := by

  rw [homog_eq, map_sum, l1, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
  rw [← mul_one (p.coeff α), ← C_mul_monomial, map_mul, hψ, smul_mul_assoc, one_mul, norm_smul, mul_one]
  refine mul_le_mul_of_nonneg_left ((mon_norm ψ hD hX _).trans (le_of_eq ?_)) (norm_nonneg _)
  rw [deg_exp (deg_le hp hα)]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.truncSB :
    ∀ {K : Type} [Field K] [NumberField K] {n d : ℕ} (evz : ℂ → PR K n →+* (Eu d →L[ℂ] Eu d)), (∀ z (c : ℂ), evz z (C (C c)) = c • 1) → ∀ (S : Set (Pl K)), (∀ R : PR K n, (∀ y ∈ R.vars, y.1 ∉ S) → ∃ M, SB (fun z => evz z R) M) →
      ∀ (Φ : KF (Ix K n) (Pl K × Fin n)) G, _root_.UpperTheory.ConvolutionTheory.admitted S Φ → IsGen Φ G → ∃ M : ℝ, ∀ k, SB (fun z => evz z (trunc k G)) (M ^ (k + 1)) := by
  intro K _ _ n d₀ evz hev S hS Φ G hΦ hG
  classical
  obtain ⟨K₀, G₀, hG₀⟩ := UpperTheory.ConvolutionTheory.FX.gen_piecesK (K →+* ℂ) (Pl K × Fin n) n Φ (by
    intro w
    convert hΦ.1 w)
  have hGG : G = G₀ := by
    funext k
    refine map_injective _ (UpperTheory.ConvolutionTheory.FX.blockE_inj (K →+* ℂ) n) ?_
    exact (hG k).trans (hG₀ k).1.symm
  subst hGG
  have hs : ∀ k, (G k).support ⊆ Φ.support := fun k => (hG₀ k).2.1
  have hdeg : ∀ d β, ∀ k ∈ Finset.range (d + 1), ((G k).coeff β).totalDegree ≤ d := fun d β k hk =>
    ((hG₀ k).2.2 β).1.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hT := fun d => trunc_eq d G Φ.support hs
  choose MX hMX using fun o : Option (Ix K n) => hS (C (X o)) (by simp)
  have hmon : ∀ β : (Pl K × Fin n) →₀ ℕ, ∃ M, β ∈ Φ.support → SB (fun z => evz z (monomial β 1)) M := by
    intro β
    by_cases hβ : β ∈ Φ.support
    · obtain ⟨M, hM⟩ := hS (monomial β 1) (by
        intro y hy
        rw [vars_monomial one_ne_zero] at hy
        exact hΦ.2 y ((mem_vars_iff_mem_support y).mpr ⟨β, hβ, hy⟩))
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose Mβ hMβ using hmon
  set D : ℝ := 1 + ∑ o, |MX o| with hDdef
  have h0 : 0 ≤ ∑ o, |MX o| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD : 1 ≤ D := by linarith
  set A : ℝ := ∑ β ∈ Φ.support, |Mβ β| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set E : ℝ := |K₀| + 1 with hE
  have hE1 : 1 ≤ E := by have := abs_nonneg K₀; linarith
  refine ⟨(A + 1) * 2 * E * D, fun d z hz => ?_⟩
  have hb := homog_norm ((evz z).comp C) (hev z) hD (fun o => by
    have h1 := hMX o z hz
    have h2 := Finset.single_le_sum (f := fun o => |MX o|) (fun _ _ => abs_nonneg _) (Finset.mem_univ o)
    have h3 := le_abs_self (MX o)
    exact h1.trans (by linarith))
  have hm : ∀ β ∈ Φ.support, ‖evz z (monomial β 1)‖ ≤ |Mβ β| := fun β hβ =>
    (hMβ β hβ z hz).trans (le_abs_self _)
  show ‖evz z (trunc d G)‖ ≤ _
  generalize evz z = ev at hb hm ⊢
  have h1 : ∀ β, ‖ev (C (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
      ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) := by
    intro β

    rw [map_sum, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ k ∈ Finset.range (d + 1), ‖ev (C (homog d ((G k).coeff β)))‖ ≤ E ^ (d + 1) * D ^ (d + 1) := by
      intro k hk
      refine (hb d _ (hdeg d β k hk)).trans (mul_le_mul ?_ (pow_le_pow_right₀ hD (Nat.le_succ d))
        (by positivity) (by positivity))
      refine ((hG₀ k).2.2 β).2.trans ?_
      have h3 : K₀ ^ (k + 1) ≤ E ^ (k + 1) :=
        (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
      have h4 : E ^ (k + 1) ≤ E ^ (d + 1) :=
        pow_le_pow_right₀ hE1 (by have := Finset.mem_range.mp hk; omega)
      have h5 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
      calc K₀ ^ (k + 1) / k.factorial ≤ E ^ (d + 1) / k.factorial := by gcongr; linarith
        _ ≤ E ^ (d + 1) := div_le_self (by positivity) h5
    refine (Finset.sum_le_card_nsmul _ _ _ h2).trans ?_
    rw [Finset.card_range, nsmul_eq_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast (Nat.lt_two_pow_self (n := d + 1)).le

  rw [hT, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have h6 : ∀ β ∈ Φ.support, ‖ev (monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
      ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * |Mβ β| := by
    intro β hβ
    rw [← mul_one (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)), ← C_mul_monomial, map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (h1 β) (hm β hβ) (norm_nonneg _) (by positivity))
  refine (Finset.sum_le_sum h6).trans ?_
  rw [← Finset.mul_sum, ← hA, mul_pow, mul_pow, mul_pow]
  have h7 : A ≤ (A + 1) ^ (d + 1) :=
    (by linarith : A ≤ A + 1).trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero d))
  calc 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * A ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * (A + 1) ^ (d + 1) := by
        gcongr
    _ = _ := by ring
end
