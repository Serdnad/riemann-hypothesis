module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.JensenFormula
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.CauchyIntegral
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Polynomial Real

def circPt (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (t : ℂ))

lemma circPt_eq (t : ℝ) : circPt t = circleMap 0 1 (2 * π * t) := by
  rw [circleMap_zero, circPt]; push_cast; ring_nf

lemma norm_circPt (t : ℝ) : ‖circPt t‖ = 1 := by
  rw [circPt_eq, norm_circleMap_zero]; simp

instance isProbabilityMeasure_restrict_Ioc :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by simp⟩

lemma integrableOn_log_circ (p : ℂ[X]) :
    IntegrableOn (fun t => Real.log ‖p.eval (circPt t)‖) (Set.Ioc (0 : ℝ) 1) := by
  have h := (p.intervalIntegrable_mahlerMeasure).comp_mul_left (c := 2 * π) enorm_ne_top
    enorm_ne_top
  have h2 : IntervalIntegrable (fun t => Real.log ‖p.eval (circPt t)‖) volume 0 1 := by
    simp only [circPt_eq]
    convert h using 2 <;> simp
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h2

lemma integral_log_circ (p : ℂ[X]) :
    ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (circPt t)‖ = p.logMahlerMeasure := by
  rw [← intervalIntegral.integral_of_le zero_le_one, logMahlerMeasure_def, circleAverage_def]
  simp only [circPt_eq]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.log ‖p.eval (circleMap 0 1 x)‖)
    (by positivity : (2 * π) ≠ 0)]
  simp

lemma log_norm_leadingCoeff_le (p : ℂ[X]) : Real.log ‖p.leadingCoeff‖ ≤ p.logMahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  rw [logMahlerMeasure_eq_log_MahlerMeasure]
  exact Real.log_le_log (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp))
    (leadingCoeff_le_mahlerMeasure p)

lemma log_norm_coeff_top_le (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (htop : ∀ k', k < k' → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by
  have hd : p.natDegree = k := by
    apply le_antisymm
    · exact natDegree_le_iff_coeff_eq_zero.mpr fun k' hk' => htop k' (by exact_mod_cast hk')
    · exact le_natDegree_of_ne_zero hk
  have := log_norm_leadingCoeff_le p
  rwa [leadingCoeff, hd] at this

lemma log_norm_coeff_bot_le (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (hbot : ∀ k', k' < k → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.mpr hbot
  have hp : p ≠ 0 := fun h => hk (by simp [h])
  have hq0 : q ≠ 0 := fun h => hp (by simp [hq, h])
  have hc : p.coeff k = q.coeff 0 := by
    rw [hq, coeff_X_pow_mul']; simp
  have hM : p.logMahlerMeasure = q.logMahlerMeasure := by
    rw [hq, logMahlerMeasure_mul_eq_add_logMahlerMeasure (by rw [← hq]; exact hp),
      X_pow_eq_monomial, logMahlerMeasure_monomial]
    simp
  rw [hc, hM, logMahlerMeasure_eq_log_MahlerMeasure]
  rw [hc] at hk
  apply Real.log_le_log (norm_pos_iff.mpr hk)
  simpa using norm_coeff_le_choose_mul_mahlerMeasure 0 q

lemma circPt_injOn : Set.InjOn circPt (Set.Ioc (0 : ℝ) 1) := by
  intro a ha b hb h
  simp only [circPt_eq] at h
  have hinj := injOn_circleMap_of_abs_sub_le (c := (0 : ℂ)) (R := 1) one_ne_zero
    (a := 0) (b := 2 * π) (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
  rw [Set.uIoc_of_le (by positivity)] at hinj
  have : 2 * π * a = 2 * π * b := by
    apply hinj
    · constructor <;> nlinarith [ha.1, ha.2, pi_pos]
    · constructor <;> nlinarith [hb.1, hb.2, pi_pos]
    · exact h
  have hpi : (2 * π) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi this

lemma zero_set_circ_null (p : ℂ[X]) (hp : p ≠ 0) :
    volume.restrict (Set.Ioc (0 : ℝ) 1) {t | p.eval (circPt t) = 0} = 0 := by
  rw [Measure.restrict_apply' measurableSet_Ioc]
  apply Set.Finite.measure_zero _ volume
  apply Set.Finite.of_finite_image (f := circPt) _
    (Set.InjOn.mono
      (s₁ := {t | p.eval (circPt t) = 0} ∩ Set.Ioc (0 : ℝ) 1)
      (s₂ := Set.Ioc (0 : ℝ) 1) (fun _ h => h.2) circPt_injOn)
  apply p.roots.finite_toSet.subset
  rintro _ ⟨t, ⟨ht, _⟩, rfl⟩
  simpa [mem_roots hp] using ht

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwp_poly_eq_of_eval_eq_off (P Q : ℂ[X]) (E : Set ℂ) (hE : E.Finite)
    (h : ∀ t ∉ E, P.eval t = Q.eval t) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (fun t ht => h t ht) hE.infinite_compl

theorem bwp_finite_eval_eq_zero {P : ℂ[X]} (hP : P ≠ 0) : {t : ℂ | P.eval t = 0}.Finite :=
  Polynomial.finite_setOfPred_isRoot hP

theorem bwp_exists_nodes (E : Set ℂ) (hE : E.Finite) (k : ℕ) :
    ∃ S : Finset ℂ, S.card = k + 1 ∧ ∀ c ∈ S, c ∉ E := by
  obtain ⟨S, hS, hcard⟩ := hE.infinite_compl.exists_subset_card_eq (k + 1)
  exact ⟨S, hcard, fun c hc => hS hc⟩

theorem bwp_eval_eq_lagrange (S : Finset ℂ) (Q : ℂ[X]) (k : ℕ) (hS : S.card = k + 1)
    (hQ : Q.natDegree ≤ k) (x : ℂ) :
    Q.eval x = ∑ c ∈ S, (Lagrange.basis S id c).eval x * Q.eval c := by
  have hinj : Set.InjOn id (S : Set ℂ) := Function.injective_id.injOn
  have hdeg : Q.degree < S.card := by
    rw [hS]
    calc Q.degree ≤ (k : WithBot ℕ) := Polynomial.degree_le_of_natDegree_le hQ
      _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp [mul_comm]

theorem bwp_eval_aeval_X {σ : Type*} (L : ℂ[X]) (i : σ) (y : σ → ℂ) :
    MvPolynomial.eval y (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ ℂ) L) = L.eval (y i) := by
  induction L using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

theorem bwp_sepPoly_fin (k : ℕ) : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    (∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t) →
    ∃ F : MvPolynomial (Fin n) ℂ, ∀ y, G y = MvPolynomial.eval y F := by
  intro n
  induction n with
  | zero =>
    intro G _
    exact ⟨MvPolynomial.C (G 0), fun y => by
      rw [MvPolynomial.eval_C, Subsingleton.elim y 0]⟩
  | succ n ih =>
    intro G hG
    obtain ⟨S, hS, -⟩ := bwp_exists_nodes ∅ Set.finite_empty k
    have hsub : ∀ c : ℂ, ∃ F : MvPolynomial (Fin n) ℂ,
        ∀ y', G (Fin.cons c y') = MvPolynomial.eval y' F := by
      intro c
      refine ih (fun y' => G (Fin.cons c y')) ?_
      intro y' m
      obtain ⟨Q, hQ, hQt⟩ := hG (Fin.cons c y') m.succ
      exact ⟨Q, hQ, fun t => by simp only [Fin.cons_update]; exact hQt t⟩
    choose Fc hFc using hsub
    refine ⟨∑ c ∈ S, Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis S id c) *
      MvPolynomial.rename Fin.succ (Fc c), fun y => ?_⟩
    obtain ⟨Q, hQ, hQt⟩ := hG y 0
    have hy : ∀ t, Function.update y 0 t = Fin.cons t (Fin.tail y) := by
      intro t
      conv_lhs => rw [← Fin.cons_self_tail y]
      exact Fin.update_cons_zero _ _ _
    have h1 : G y = Q.eval (y 0) := by
      rw [← hQt]; simp
    rw [h1, bwp_eval_eq_lagrange S Q k hS hQ, MvPolynomial.eval_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MvPolynomial.eval_mul, bwp_eval_aeval_X, MvPolynomial.eval_rename, ← hQt c, hy c, hFc c]
    rfl

theorem bwp_sepPoly {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ) (G : (σ → ℂ) → ℂ)
    (hG : ∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t) :
    ∃ F : MvPolynomial σ ℂ, ∀ y, G y = MvPolynomial.eval y F := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  obtain ⟨F, hF⟩ := bwp_sepPoly_fin k (Fintype.card σ) (fun z => G (z ∘ e)) (fun z m => by
    obtain ⟨Q, hQd, hQ⟩ := hG (z ∘ e) (e.symm m)
    refine ⟨Q, hQd, fun t => ?_⟩
    show G ((Function.update z m t) ∘ e) = _
    rw [Function.update_comp_equiv, hQ])
  refine ⟨MvPolynomial.rename e.symm F, fun y => ?_⟩
  rw [MvPolynomial.eval_rename, ← hF]
  congr 1
  ext s
  simp

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem log_norm_eval_zero_le_circleAverage (q : ℂ[X]) (hq : q.eval 0 ≠ 0) :
    Real.log ‖q.eval 0‖ ≤ Real.circleAverage (fun ζ => Real.log ‖q.eval ζ‖) 0 1 := by
  have hA : AnalyticOnNhd ℂ (fun z => q.eval z) Set.univ := fun z _ =>
    (Polynomial.differentiable q).analyticAt z
  have hM : MeromorphicOn (fun z => q.eval z) (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) :=
    (hA.mono (Set.subset_univ _)).meromorphicOn
  have hD : 0 ≤ MeromorphicOn.divisor (fun z => q.eval z) (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hA.mono (Set.subset_univ _))
  rw [MeromorphicOn.circleAverage_log_norm one_ne_zero hM,
    AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (hA 0 trivial) hq, Real.log_one, mul_zero,
    add_zero]
  have hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor (fun z => q.eval z)
      (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℝ) * Real.log (1 * ‖0 - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |(1 : ℝ)|
    · have hle : ‖u‖ ≤ 1 := by simpa using hu
      apply mul_nonneg
      · exact_mod_cast (show (0 : ℤ) ≤ _ by simpa using hD u)
      · rw [one_mul, Real.log_inv, zero_sub, norm_neg]
        exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hle)
    · have h0 : MeromorphicOn.divisor (fun z => q.eval z) (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) u = 0 := by
        by_contra h
        exact hu (Function.locallyFinsuppWithin.supportWithinDomain _ (Function.mem_support.mpr h))
      simp [h0]
  linarith

theorem eval_smul_of_isHomogeneous {σ : Type*} {f : MvPolynomial σ ℂ} {a : ℕ}
    (hf : f.IsHomogeneous a) (c : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun i => c * x i) f = c ^ a * MvPolynomial.eval x f := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = a := by
    have h := hf (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField

theorem relIndex_span_comb {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (M : Matrix (Fin k) (Fin k) (𝓞 K))
    (hM : M.det ≠ 0) :
    (((Submodule.span (𝓞 K) (Set.range (fun j => ∑ i, M i j • b i))).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup : ℕ) : ℤ) = |Algebra.norm ℤ M.det| := by
  set P := Submodule.span (𝓞 K) (Set.range b) with hPdef
  set Q := Submodule.span (𝓞 K) (Set.range (fun j => ∑ i, M i j • b i)) with hQdef
  have hbO : LinearIndependent (𝓞 K) b := hb.restrict_scalars' (𝓞 K)
  let bP : Module.Basis (Fin k) (𝓞 K) P := Module.Basis.span hbO
  let f : P →ₗ[𝓞 K] P := Matrix.toLin bP bP M
  have hfb : ∀ j, ((f (bP j) : P) : Fin r → K) = ∑ i, M i j • b i := by
    intro j
    simp only [f, Matrix.toLin_self, bP, Submodule.coe_sum, Submodule.coe_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [Module.Basis.span_apply]
  have hQ : Submodule.map P.subtype (LinearMap.range f) = Q := by
    rw [LinearMap.range_eq_map, ← bP.span_eq, Submodule.map_span, Submodule.map_span,
      ← Set.range_comp, ← Set.range_comp, hQdef]
    congr 2
    funext j
    exact hfb j
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := LinearMap.toMatrix_mulVec_repr bP bP f x
    rw [hx, map_zero, LinearMap.toMatrix_toLin] at h1
    have h2 : ⇑(bP.repr x) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using h1)
    have h3 : bP.repr x = 0 := DFunLike.coe_injective h2
    simpa using h3
  have hR : Q.toAddSubgroup.addSubgroupOf P.toAddSubgroup = (LinearMap.range f).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, ← hQ,
      Submodule.mem_toAddSubgroup, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have : Module.Free (𝓞 K) P := Module.Free.of_basis bP
  have : Module.Finite (𝓞 K) P := Module.Finite.of_basis bP
  have : Module.Free ℤ P := Module.Free.of_basis ((RingOfIntegers.basis K).smulTower bP)
  have : Module.Finite ℤ P := Module.Finite.of_basis ((RingOfIntegers.basis K).smulTower bP)
  set N : Submodule ℤ P := (LinearMap.range f).toAddSubgroup.toIntSubmodule with hN
  let e : P ≃+ N := (LinearEquiv.ofInjective f hf).toAddEquiv
  have hdet : N.subtype ∘ₗ e.toAddMonoidHom.toIntLinearMap = f.restrictScalars ℤ := by
    ext x
    rfl
  have key : (LinearMap.det (N.subtype ∘ₗ e.toAddMonoidHom.toIntLinearMap)).natAbs =
      Nat.card (P ⧸ N) := Submodule.natAbs_det_equiv N e
  rw [hdet, LinearMap.det_restrictScalars, LinearMap.det_toLin] at key
  rw [AddSubgroup.relIndex, hR]
  change ((Nat.card (P ⧸ N) : ℕ) : ℤ) = _
  rw [← key, Int.natCast_natAbs]

theorem comb_diagonal {K : Type} [Field K] [NumberField K] {r k : ℕ} (v : Fin k → Fin r → K)
    (D : 𝓞 K) : (fun j => ∑ i, Matrix.diagonal (fun _ : Fin k => D) i j • v i) = fun j => D • v j := by
  funext j
  simp [Matrix.diagonal_apply, ite_smul]

theorem exists_smul_mem_span {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (x : Fin r → K) (hx : x ∈ Submodule.span K (Set.range b)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
  obtain ⟨⟨d, hd⟩, hdc⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Finset.univ c
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨e, he⟩ := hdc i (Finset.mem_univ i)
  have h1 : d • (c i • b i) = e • b i := by
    rw [← smul_assoc, ← algebraMap_smul K e (b i), he]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_smul_le_span {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (B : Submodule (𝓞 K) (Fin r → K)) (hB : B.FG)
    (hBb : ∀ x ∈ B, x ∈ Submodule.span K (Set.range b)) :
    ∃ D : 𝓞 K, D ≠ 0 ∧ ∀ x ∈ B, D • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
  obtain ⟨s, hs⟩ := hB
  have hgen : ∀ g ∈ s, ∃ d : 𝓞 K, d ≠ 0 ∧ d • g ∈ Submodule.span (𝓞 K) (Set.range b) :=
    fun g hg => exists_smul_mem_span b g (hBb g (by rw [← hs]; exact Submodule.subset_span hg))
  choose! d hd0 hdm using hgen
  refine ⟨∏ g ∈ s, d g, Finset.prod_ne_zero_iff.2 hd0, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem d hg
    rw [ht, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hdm g hg)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hx

theorem relIndex_span_ne_zero {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (B : Submodule (𝓞 K) (Fin r → K))
    (hbB : ∀ i, b i ∈ B) (D : 𝓞 K) (hD : D ≠ 0)
    (hDB : ∀ x ∈ B, D • x ∈ Submodule.span (𝓞 K) (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
  set P := Submodule.span (𝓞 K) (Set.range b) with hP
  let φ : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) := D • LinearMap.id
  have hD' : algebraMap (𝓞 K) K D ≠ 0 := by
    rw [← map_zero (algebraMap (𝓞 K) K)]
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hD
  have hφ : Function.Injective φ := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simp only [φ, Algebra.smul_def] at this
    exact mul_left_cancel₀ hD' this
  have hPB : P ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hbB)
  have hmapP : Submodule.map φ P = Submodule.span (𝓞 K)
      (Set.range (fun j => ∑ i, Matrix.diagonal (fun _ : Fin k => D) i j • b i)) := by
    rw [comb_diagonal, hP, Submodule.map_span, ← Set.range_comp]
    rfl
  have h1 : (Submodule.map φ P).toAddSubgroup ≤ (Submodule.map φ B).toAddSubgroup :=
    Submodule.map_mono hPB
  have h2 : (Submodule.map φ B).toAddSubgroup ≤ P.toAddSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    exact hDB x hx
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  have hdet : (Matrix.diagonal fun _ : Fin k => D).det ≠ 0 := by
    simp [Matrix.det_diagonal, hD]
  have hidx := relIndex_span_comb b hb (Matrix.diagonal fun _ => D) hdet
  rw [← hmapP] at hidx
  have hne : (Submodule.map φ P).toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    intro h0
    rw [h0] at hidx
    have hn : Algebra.norm ℤ (Matrix.diagonal fun _ : Fin k => D).det ≠ 0 :=
      Algebra.norm_ne_zero_iff.mpr hdet
    simp only [Nat.cast_zero] at hidx
    exact hn (abs_eq_zero.mp hidx.symm)
  have heq : (Submodule.map φ P).toAddSubgroup.relIndex (Submodule.map φ B).toAddSubgroup =
      P.toAddSubgroup.relIndex B.toAddSubgroup := by
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hφ
  rw [← heq]
  intro h0
  rw [h0, zero_mul] at hmul
  exact hne hmul.symm

end ReciprocityTheory.MultiplicativeHeights
end
end
