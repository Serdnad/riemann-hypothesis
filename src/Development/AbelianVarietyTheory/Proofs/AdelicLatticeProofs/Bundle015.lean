module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandauSummableOfExpDirichletSeriesEntire
public import Mathlib.Analysis.Complex.Circle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle004
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
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
public import Mathlib.RepresentationTheory.Intertwining
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Compactness.Compact
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_ringEquiv_ne_of_transcendental :
    ∀ z : ℂ, Transcendental ℚ z → ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  intro z hz
  have hind : AlgebraicIndepOn ℚ id ({z} : Set ℂ) := by
    show AlgebraicIndependent ℚ _
    exact algebraicIndependent_unique_type_iff.2 hz
  obtain ⟨t, hzt, ht⟩ := exists_isTranscendenceBasis_superset hind
  let v : t → ℂ := (↑)
  let i0 : t := ⟨z, hzt rfl⟩
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v ht
  let f : t → MvPolynomial t ℚ := fun i => if i = i0 then -MvPolynomial.X i else MvPolynomial.X i
  have hcomp : (MvPolynomial.aeval f).comp (MvPolynomial.aeval f) =
      AlgHom.id ℚ (MvPolynomial t ℚ) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases h : i = i0 <;> simp [f, h]
  let neg := AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f) hcomp hcomp
  let e : Algebra.adjoin ℚ (Set.range v) ≃+* Algebra.adjoin ℚ (Set.range v) :=
    ht.1.aevalEquiv.symm.toRingEquiv.trans (neg.toRingEquiv.trans ht.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, ?_⟩
  have h1 : algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ (ht.1.aevalEquiv (MvPolynomial.X i0)) = z := by
    rw [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  have key : IsAlgClosure.equivOfEquiv ℂ ℂ e z = -z := by
    conv_lhs => rw [← h1]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.symm_apply_apply]
    rw [AlgebraicIndependent.algebraMap_aevalEquiv]
    simp [neg, f, v, i0]
  rw [key]
  intro h
  have h0 : z = 0 := by linear_combination (-1 / 2 : ℂ) * h
  rw [h0] at hz
  exact hz isAlgebraic_zero

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_ringEquiv_apply_ne_of_isAlgebraic :
    ∀ z : ℂ, IsAlgebraic ℚ z → (∀ q : ℚ, z ≠ q) → ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  intro z _ hz
  by_contra h
  have hfix : ∀ σ : ℂ ≃ₐ[ℚ] ℂ, σ z = z := fun σ => by_contra fun hne => h ⟨σ.toRingEquiv, hne⟩
  obtain ⟨q, hq⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := ℚ) z hfix
  exact hz q (hq.symm.trans (by simp))

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem compact_subset_finite_leftCosets (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (K : Set G) (hU : IsOpen (U : Set G))
    (hK : IsCompact K) : ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, ∃ u ∈ U, k = t * u := by
  obtain ⟨T, -, hT⟩ := hK.elim_nhds_subcover (fun t : G => (fun k => t⁻¹ * k) ⁻¹' (U : Set G))
    (fun t _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨T, fun k hk => ?_⟩
  have := hT hk
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨t, ht, h⟩ := this
  exact ⟨t, ht, t⁻¹ * k, h, by simp⟩

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private lemma neg_one_le_re_pow_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) (k : ℕ) : -1 ≤ (c ^ k).re := by
  have h1 : ‖c ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
  have h2 := Complex.abs_re_le_norm (c ^ k)
  linarith [(abs_le.mp (h2.trans h1)).1]


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.not_summable_two_add_two_re_pow_div (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ¬ Summable fun k : ℕ => (2 + 2 * (c ^ (k + 1)).re) / ((k : ℝ) + 1) := by
  intro h
  set f := fun k : ℕ => (2 + 2 * (c ^ (k + 1)).re) / ((k : ℝ) + 1) with hf
  have hnn : ∀ k, 0 ≤ f k := fun k =>
    div_nonneg (by linarith [neg_one_le_re_pow_of_norm_le_one hc (k + 1)]) (by positivity)
  have hkey : ∀ k : ℕ, 3 / 2 * (1 / ((k : ℝ) + 1)) ≤ f k + f (2 * k + 1) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hn : ‖c ^ (k + 1)‖ ^ 2 ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hc)
    rw [Complex.sq_norm, Complex.normSq_apply] at hn
    have hz : c ^ (2 * k + 1 + 1) = c ^ (k + 1) * c ^ (k + 1) := by ring
    have hsum : f k + f (2 * k + 1) = (3 + 2 * (c ^ (k + 1)).re +
        ((c ^ (k + 1)).re * (c ^ (k + 1)).re - (c ^ (k + 1)).im * (c ^ (k + 1)).im)) /
        ((k : ℝ) + 1) := by
      simp only [hf, hz, Complex.mul_re]
      push_cast
      field_simp
      ring
    rw [hsum, mul_one_div]
    exact (div_le_div_iff_of_pos_right hk).mpr (by nlinarith [sq_nonneg ((c ^ (k + 1)).re + 1 / 2)])
  have hs2 : Summable fun k : ℕ => f k + f (2 * k + 1) :=
    h.add (h.comp_injective (fun a b hab => by simpa using hab))
  have hharm : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    have h3 : Summable fun k : ℕ => 3 / 2 * (1 / ((k : ℝ) + 1)) :=
      hs2.of_nonneg_of_le (fun k => by positivity) hkey
    exact (summable_mul_left_iff (by norm_num : (3 / 2 : ℝ) ≠ 0)).mp h3
  refine Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp ?_)
  simpa using hharm

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private lemma norm_mul_natCast_cpow_neg_le {n : ℕ} (hn : 2 ≤ n) {c : ℂ} (hc : ‖c‖ ≤ 1) (s : ℂ) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), neg_re]
  exact mul_le_of_le_one_left (by positivity) hc

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private lemma natCast_rpow_neg_le_half {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    (n : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hn


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.conj_neg_log_euler_factor (n : ℕ) (hn : 2 ≤ n) (c : ℂ) (hc : ‖c‖ ≤ 1) (s : ℂ)
    (hs : 1 < s.re) :
    starRingEnd ℂ (-Complex.log (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s)))) =
      -Complex.log (1 - starRingEnd ℂ c * (n : ℂ) ^ (-s)) := by
  have hlt : ‖c * (n : ℂ) ^ (-(starRingEnd ℂ s))‖ < 1 :=
    ((norm_mul_natCast_cpow_neg_le hn hc (starRingEnd ℂ s)).trans
      (natCast_rpow_neg_le_half hn (by simpa using hs))).trans_lt (by norm_num)
  have hre : 0 < (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s))).re := by
    rw [sub_re, one_re]
    linarith [Complex.re_le_norm (c * (n : ℂ) ^ (-(starRingEnd ℂ s)))]
  have harg : (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s))).arg ≠ Real.pi := fun h => by
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have hconj : starRingEnd ℂ ((n : ℂ) ^ (-(starRingEnd ℂ s))) = (n : ℂ) ^ (-s) := by
    have := Complex.cpow_conj (n : ℂ) (-s) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
    rw [map_neg] at this
    rw [this, Complex.conj_conj, Complex.conj_natCast]
  rw [map_neg, ← Complex.log_conj _ harg, map_sub, map_one, map_mul, hconj]


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.eulerProduct_ne_zero_one_of_entire : ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z L : ℂ → ℂ, Differentiable ℂ Z → Differentiable ℂ L → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → (∀ s : ℂ, 1 < s.re → L s = Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))) → L 1 ≠ 0 := by
  intro ι N c hN hc hsum hne Z L hZ hL hZs hLs h1
  set L' : ℂ → ℂ := fun s => starRingEnd ℂ (L (starRingEnd ℂ s)) with hL'
  have hdL' : Differentiable ℂ L' := fun s => by
    have := (hL (starRingEnd ℂ s)).conj_conj
    simpa [hL', Function.comp_def] using this
  have hL'1 : L' 1 = 0 := by simp [hL', h1]
  have hds : ∀ f : ℂ → ℂ, Differentiable ℂ f → Differentiable ℂ (dslope f 1) := fun f hf =>
    differentiableOn_univ.mp ((differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn)
  have ha : ∀ p : ι × ℕ, 0 ≤ (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1) := fun p =>
    div_nonneg (by linarith [neg_one_le_re_pow_of_norm_le_one (hc p.1) (p.2 + 1)]) (by positivity)
  have key := _root_.GlobalTheory.landau_exp_summable (ι × ℕ)
    (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1))
    (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1))
    (fun s => Z s ^ 2 * dslope L 1 s * dslope L' 1 s) ha
    (fun p => mul_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (by have := hN p.1; omega : 1 ≤ N p.1))))
    (((hZ.pow 2).mul (hds L hL)).mul (hds L' hdL')) (by
      intro s hs
      refine ⟨_, _root_.GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
      have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hL's : L' s = Complex.exp (∑' i, -Complex.log
          (1 - starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s))) := by
        simp only [hL']
        rw [hLs _ (by simpa using hs), ← Complex.exp_conj, Complex.conj_tsum]
        congr 1
        exact tsum_congr fun i => _root_.GlobalTheory.conj_neg_log_euler_factor (N i) (hN i) (c i) (hc i) s hs
      simp only [dslope_of_ne _ hs1, slope_def_field, h1, hL'1, sub_zero]
      rw [hZs s hs, hLs s hs, hL's, two_mul, Complex.exp_add, Complex.exp_add, Complex.exp_add]
      field_simp)
  obtain ⟨i⟩ := hne
  exact _root_.GlobalTheory.not_summable_two_add_two_re_pow_div (c i) (hc i)
    (((summable_prod_of_nonneg (fun p => ha p)).mp key).1 i)

end GlobalTheory
end

section

open scoped Topology BigOperators

namespace GlobalTheory

open scoped Topology BigOperators in
private lemma continuous_circle_toUnits' : Continuous Circle.toUnits := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  have : Continuous (fun w : Circle => ((w⁻¹ : Circle) : ℂ)) :=
    continuous_subtype_val.comp continuous_inv
  convert this using 2 with w
  simp

open scoped Topology BigOperators in
private lemma div_norm_sq_eq_div_conj_of_ne_zero (x : ℂ) (hx : x ≠ 0) :
    (x / ‖x‖) ^ 2 = x / starRingEnd ℂ x := by
  have h : x * starRingEnd ℂ x = ((‖x‖ : ℂ)) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hc : starRingEnd ℂ x ≠ 0 := by simpa using hx
  rw [div_pow, ← h]
  field_simp


open scoped Topology BigOperators in
theorem _root_.GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow :
    ∀ (ι : Type) [Fintype ι] (f : (ι → ℂˣ) →* Circle), Continuous f → (∀ z : ι → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) → f z = 1) → ∃ k : ι → ℤ, ∀ z, ((f z : Circle) : ℂ) = ∏ i, ((z i : ℂ) / starRingEnd ℂ (z i : ℂ)) ^ k i := by
  intro ι _ f hf hreal
  classical
  let g : ι → Circle →* Circle := fun i =>
    f.comp ((MonoidHom.mulSingle (fun _ => ℂˣ) i).comp Circle.toUnits)
  have hg : ∀ i, Continuous (g i) := fun i =>
    hf.comp ((continuous_mulSingle i).comp continuous_circle_toUnits')
  choose n hn using fun i => _root_.GlobalTheory.circle_hom_eq_zpow (g i) (hg i)
  have heven : ∀ i, Even (n i) := by
    intro i
    have h1 : g i (Circle.exp Real.pi) = 1 := by
      apply hreal
      intro j
      by_cases hj : j = i
      · subst hj
        simp [Circle.coe_exp, Complex.exp_pi_mul_I]
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [hn] at h1
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp [Circle.coe_exp, Complex.exp_pi_mul_I] at h2
    rcases Int.even_or_odd (n i) with h | h
    · exact h
    · rw [h.neg_one_zpow] at h2
      norm_num at h2
  choose k hk using heven
  refine ⟨k, fun z => ?_⟩
  have hne : ∀ i, ((‖(z i : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun i => by simp
  set u : ι → Circle := fun i => Circle.exp (Complex.arg (z i)) with hu_def
  have hu : ∀ i, ((u i : Circle) : ℂ) = (z i : ℂ) / ‖(z i : ℂ)‖ := by
    intro i
    rw [eq_div_iff (hne i), mul_comm]
    simpa [u, Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I (z i : ℂ)
  have hz : z = (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) *
      fun i => Circle.toUnits (u i) := by
    funext i
    ext
    simp only [Pi.mul_apply, Units.val_mul, Units.val_mk0]
    simp [hu, mul_div_cancel₀ _ (hne i)]
  have hr : f (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) = 1 :=
    hreal _ fun i => by simp
  have hv : f (fun i => Circle.toUnits (u i)) = ∏ i, g i (u i) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle (fun i => Circle.toUnits (u i))]
    rw [map_prod]
    rfl
  have hfz : f z = ∏ i, g i (u i) := by
    conv_lhs => rw [hz]
    rw [map_mul, hr, one_mul, hv]
  rw [hfz]
  refine (map_prod Circle.coeHom (fun i => g i (u i)) Finset.univ).trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  show ((g i (u i) : Circle) : ℂ) = _
  rw [hn, Circle.coe_zpow, hu, hk i, ← two_mul, zpow_mul, zpow_ofNat,
    div_norm_sq_eq_div_conj_of_ne_zero _ (z i).ne_zero]

end GlobalTheory
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem log_sq_le_tangent_add_sq :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, a ≤ x → a ≤ y →
      (Real.log y) ^ 2 ≤ (Real.log x) ^ 2 + 2 * Real.log x / x * (y - x) + C * (y - x) ^ 2 := by
  intro a ha
  refine ⟨(2 + 2 * |Real.log a|) / a ^ 2, by positivity, ?_⟩
  intro x y hx hy
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have hy0 : 0 < y := lt_of_lt_of_le ha hy
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = Real.log y - Real.log x := ⟨_, rfl⟩
  have hlogy : Real.log y = Real.log x + d := by rw [hd]; ring
  have hup : d ≤ (y - x) / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h
    have e : y / x - 1 = (y - x) / x := by field_simp
    rw [hd]; linarith
  have hlow : (y - x) / y ≤ d := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at h
    have e : (y - x) / y = 1 - x / y := by field_simp
    rw [hd, e]; linarith
  have hxy : a ^ 2 ≤ x * y := by nlinarith
  have hxx : a ^ 2 ≤ x ^ 2 := by nlinarith
  have hyy : a ^ 2 ≤ y ^ 2 := by nlinarith
  have ha2 : 0 < a ^ 2 := by positivity
  have hK0 : 0 ≤ (y - x) ^ 2 / a ^ 2 := by positivity
  have hgap : (y - x) / x - d ≤ (y - x) ^ 2 / a ^ 2 := by
    have e : (y - x) / x - (y - x) / y = (y - x) ^ 2 / (x * y) := by
      field_simp
    have h : (y - x) ^ 2 / (x * y) ≤ (y - x) ^ 2 / a ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) ha2 hxy
    linarith
  have hq2 : ((y - x) / x) ^ 2 ≤ (y - x) ^ 2 / a ^ 2 := by
    rw [div_pow]; exact div_le_div_of_nonneg_left (sq_nonneg _) ha2 hxx
  have hp2 : ((y - x) / y) ^ 2 ≤ (y - x) ^ 2 / a ^ 2 := by
    rw [div_pow]; exact div_le_div_of_nonneg_left (sq_nonneg _) ha2 hyy
  have hd2 : d ^ 2 ≤ 2 * ((y - x) ^ 2 / a ^ 2) := by
    rcases le_total 0 d with h | h
    · nlinarith [sq_nonneg ((y - x) / y)]
    · nlinarith [sq_nonneg ((y - x) / x)]
  have hu : -Real.log x ≤ |Real.log a| := by
    have := Real.log_le_log ha hx
    have := neg_le_abs (Real.log a)
    linarith
  have hL0 : 0 ≤ |Real.log a| := abs_nonneg _
  have he0 : 0 ≤ (y - x) / x - d := by linarith
  have h3 : -Real.log x * ((y - x) / x - d) ≤ |Real.log a| * ((y - x) ^ 2 / a ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_right hu he0) (mul_le_mul_of_nonneg_left hgap hL0)
  have e1 : 2 * Real.log x / x * (y - x) = 2 * Real.log x * ((y - x) / x) := by ring
  have e2 : (2 + 2 * |Real.log a|) / a ^ 2 * (y - x) ^ 2
      = (2 + 2 * |Real.log a|) * ((y - x) ^ 2 / a ^ 2) := by ring
  rw [hlogy, e1, e2]
  nlinarith [h3, hd2]

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range :
    ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  intro G _ W _ _ ρ J V _ _ r p hr hp htop
  let f : ∀ j, (r j).IntertwiningMap ρ := fun j => ⟨p j, fun g => LinearMap.ext fun v => hp j g v⟩
  let F : ∀ j, (r j).asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule :=
    fun j => Representation.IntertwiningMap.equivLinearMapAsModule (r j) ρ (f j)
  have hF : ∀ j (v : V j), F j v = p j v := fun j v => rfl
  have hs : ∀ j, IsSemisimpleModule (MonoidAlgebra ℂ G) (LinearMap.range (F j)) := by
    intro j
    haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule (r j)).mp
      (hr j)
    exact IsSemisimpleModule.range (F j)
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' hs ?_
  rw [eq_top_iff]
  intro x _
  have hx : (show W from x) ∈ ⨆ j, LinearMap.range (p j) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (fun j => LinearMap.range (p j))
    (motive := fun y : W => (show ρ.asModule from y) ∈ ⨆ j, LinearMap.range (F j)) hx ?_ ?_ ?_
  · rintro j y ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem j ⟨v, hF j v⟩
  · exact Submodule.zero_mem _
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem adjugate_entry_mem_subring {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]
    (R₀ : Subring R) (A : Matrix ι ι R) (hA : ∀ i j, A i j ∈ R₀) (i j : ι) : A.adjugate i j ∈ R₀ := by
  let B : Matrix ι ι R₀ := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hB : A = R₀.subtype.mapMatrix B := by
    ext i j; rfl
  rw [hB, ← RingHom.map_adjugate]
  exact (B.adjugate i j).2

end GlobalTheory.ClassFin
end
