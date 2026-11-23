module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle006
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_stalk_Sp (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (y : Sp A) :
    IsDomain ((Sp A).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp A).presheaf.stalk y) := by
  have hy : (y.asIdeal : Ideal A).IsPrime := y.isPrime
  let _ : Algebra A ((Sp A).presheaf.stalk y) := StructureSheaf.stalkAlgebra A y
  have : IsLocalization.AtPrime ((Sp A).presheaf.stalk y) (y.asIdeal : Ideal A) :=
    StructureSheaf.IsLocalization.to_stalk A y
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (B := A) (y.asIdeal : Ideal A)
    ((Sp A).presheaf.stalk y)

theorem isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s →
      IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X := by
  intro k _ X s hs
  have : Smooth s := hs
  have hN : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (fun y => isDomain_and_isIntegrallyClosed_stalk_Sp k y)
  refine ⟨?_, hN, ?_⟩
  · have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hN x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  · have : IsLocallyNoetherian (Sp k) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian s

end GlobalTheory
end

section

open Filter Metric Set
open scoped Topology

namespace GlobalTheory

theorem exists_circle_ne_zero_of_frequently_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {S : Set E} {g : E → ℂ} {z₀ : E} (hS : S ∈ 𝓝 z₀)
    (hg : DifferentiableOn ℂ g S) (hfr : ∃ᶠ z in 𝓝 z₀, g z ≠ 0) :
    ∃ (v : E) (r : ℝ), 0 < r ∧ (∀ t ∈ closedBall (0 : ℂ) r, z₀ + t • v ∈ S) ∧
      ∀ t ∈ sphere (0 : ℂ) r, g (z₀ + t • v) ≠ 0 := by
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.1 hS
  obtain ⟨z₁, hz₁, hz₁b⟩ := (hfr.and_eventually (ball_mem_nhds z₀ (half_pos hε))).exists
  have hv : ‖z₁ - z₀‖ < ε / 2 := by simpa [dist_eq_norm] using hz₁b
  have hmem : ∀ t ∈ ball (0 : ℂ) 2, z₀ + t • (z₁ - z₀) ∈ S := by
    intro t ht
    apply hεS
    rw [mem_ball_zero_iff] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg t, norm_nonneg (z₁ - z₀)]
  have hd : DifferentiableOn ℂ (fun t : ℂ => g (z₀ + t • (z₁ - z₀))) (ball 0 2) :=
    hg.comp (f := fun t : ℂ => z₀ + t • (z₁ - z₀)) (by fun_prop) hmem
  have han := hd.analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 2 := by simp
  rcases (han 0 h0).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 2).isPreconnected
      h0 h (show (1 : ℂ) ∈ ball (0 : ℂ) 2 by simp)
    exact absurd (by simpa using this) hz₁
  · rw [eventually_nhdsWithin_iff] at h
    obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.1
      (h.and (ball_mem_nhds (0 : ℂ) two_pos))
    refine ⟨z₁ - z₀, r, hr, fun t ht => hmem t (hrs ht).2, fun t ht => ?_⟩
    refine (hrs (sphere_subset_closedBall ht)).1 ?_
    rintro rfl
    simp at ht
    exact hr.ne ht

theorem differentiableOn_quotient_of_differentiableOn_slice :
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
      [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V'))
      (f θ F : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W →
      (∀ w ∈ W, F w * θ w = f w) →
      (∀ b, DifferentiableOn ℂ (fun z => F (b, z)) {z | (b, z) ∈ W}) →
      (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1, z) ≠ 0) → DifferentiableOn ℂ F W := by
  intro V V' _ _ _ _ _ _ W f θ F hW hf hθ hF hsl hfr w hw
  obtain ⟨v, r, hr, hin, hne⟩ := exists_circle_ne_zero_of_frequently_ne_zero
    (S := {z | (w.1, z) ∈ W}) (g := fun z => θ (w.1, z)) (z₀ := w.2)
    ((hW.preimage (f := fun z => (w.1, z)) (by fun_prop)).mem_nhds hw)
    (hθ.comp (f := fun z => (w.1, z)) (by fun_prop) fun z hz => hz) (hfr w hw)
  let p : V × V' → ℂ → V × V' := fun y t => (y.1, y.2 + t • v)
  have hp : Continuous fun q : (V × V') × ℂ => p q.1 q.2 := by fun_prop
  have h1 : ∀ᶠ y in 𝓝 w, ∀ t ∈ closedBall (0 : ℂ) r, p y t ∈ W :=
    (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht =>
      hp.continuousAt.eventually (hW.mem_nhds (hin t ht))
  have h2 : ∀ᶠ y in 𝓝 w, ∀ t ∈ sphere (0 : ℂ) r, θ (p y t) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => by
      have hc : ContinuousAt θ (p w t) :=
        (hθ.differentiableAt (hW.mem_nhds (hin t (sphere_subset_closedBall ht)))).continuousAt
      exact (ContinuousAt.comp (g := θ) (f := fun q : (V × V') × ℂ => p q.1 q.2) (x := (w, t))
        hc hp.continuousAt).eventually_ne (hne t ht)
  obtain ⟨U, hU, hUo, hwU⟩ := _root_.eventually_nhds_iff.1 (h1.and h2)
  have hcm : ∀ s : ℝ, circleMap 0 r s ∈ sphere (0 : ℂ) r := fun s =>
    circleMap_mem_sphere 0 hr.le s
  have hG := (differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (s : ℝ) (y : V × V') => f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)))
    (a := 0) (b := 2 * Real.pi) hUo ?_ ?_).1
  · have hEq : ∀ y ∈ U, F y = (2 * Real.pi)⁻¹ • ∫ s in (0 : ℝ)..2 * Real.pi,
        f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)) := by
      intro y hy
      have hd : DifferentiableOn ℂ (fun t : ℂ => F (p y t)) (closedBall 0 r) :=
        (hsl y.1).comp (f := fun t : ℂ => y.2 + t • v) (by fun_prop) fun t ht => (hU y hy).1 t ht
      have hdc : DiffContOnCl ℂ (fun t : ℂ => F (p y t)) (ball 0 |r|) := by
        apply DifferentiableOn.diffContOnCl
        rwa [abs_of_pos hr, closure_ball _ hr.ne']
      have hav := hdc.circleAverage
      rw [Real.circleAverage_def] at hav
      have : F y = F (p y 0) := by simp [p]
      rw [this, ← hav]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      have hs := hcm s
      rw [eq_div_iff ((hU y hy).2 _ hs), hF _ ((hU y hy).1 _ (sphere_subset_closedBall hs))]
    have hFU : DifferentiableOn ℂ F U := (hG.const_smul ((2 * Real.pi)⁻¹ : ℝ)).congr hEq
    exact (hFU.differentiableAt (hUo.mem_nhds hwU)).differentiableWithinAt
  · have hq : Continuous fun q : ℝ × (V × V') => p q.2 (circleMap 0 r q.1) :=
      hp.comp (f := fun q : ℝ × (V × V') => (q.2, circleMap 0 r q.1)) (by fun_prop)
    have hm : ∀ q : ℝ × (V × V'), q ∈ uIcc 0 (2 * Real.pi) ×ˢ U →
        p q.2 (circleMap 0 r q.1) ∈ W := fun q hq =>
      (hU _ hq.2).1 _ (sphere_subset_closedBall (hcm _))
    exact (hf.continuousOn.comp hq.continuousOn hm).div
      (hθ.continuousOn.comp hq.continuousOn hm) fun q hq => (hU _ hq.2).2 _ (hcm _)
  · intro s _
    have hq : Differentiable ℂ fun y : V × V' => p y (circleMap 0 r s) := by fun_prop
    have hm : ∀ y ∈ U, p y (circleMap 0 r s) ∈ W := fun y hy =>
      (hU _ hy).1 _ (sphere_subset_closedBall (hcm _))
    simp only [div_eq_mul_inv]
    exact (hf.comp hq.differentiableOn hm).mul
      ((hθ.comp hq.differentiableOn hm).inv fun y hy => (hU _ hy).2 _ (hcm _))

end GlobalTheory
end

section

open scoped TensorProduct
theorem _root_.GlobalTheory.T.dvd_trace_of_tensor_lmul_eq : ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Free O H] [Module.Finite O H] (Θ : H ⊗[O] H) (c : O), ((∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0) → ∀ h : H, c ∣ Algebra.trace O H h := by
  first | exact @GlobalTheory.dvd_trace_of_balanced_tensor | exact GlobalTheory.dvd_trace_of_balanced_tensor | (intros; apply GlobalTheory.dvd_trace_of_balanced_tensor <;> assumption)
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem finite_card_trace_algHom_of_isReduced_baseChange :
    ∀ (O H K : Type) [CommRing O] [Nontrivial O] [CommRing H] [Algebra O H] [Module.Free O H]
      [Module.Finite O H] [Field K] [IsAlgClosed K] [Algebra O K], IsReduced (K ⊗[O] H) →
      Finite (H →ₐ[O] K) ∧ Nat.card (H →ₐ[O] K) = Module.finrank O H ∧
        ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ᶠ ga : H →ₐ[O] K, ga h := by
  classical
  intro O H K _ _ _ _ _ _ _ _ _ hred
  have : IsReduced (K ⊗[O] H) := hred
  have hcard : Nat.card (H →ₐ[O] K) = Module.finrank O H :=
    natCard_algHom_eq_finrank_of_isReduced_baseChange O H K
  have hfin : Finite (H →ₐ[O] K) := by
    by_cases h0 : Module.finrank O H = 0
    · have : IsEmpty (H →ₐ[O] K) := by
        refine ⟨fun f => ?_⟩
        have hι : IsEmpty (Module.Free.ChooseBasisIndex O H) := by
          rw [← Fintype.card_eq_zero_iff, ← Module.finrank_eq_card_chooseBasisIndex]
          exact h0
        have h10 : (1 : H) = 0 :=
          (Module.Free.chooseBasis O H).repr.injective (Subsingleton.elim _ _)
        have h1 := congrArg f h10
        rw [map_one, map_zero] at h1
        exact one_ne_zero h1
      infer_instance
    · exact Nat.finite_of_card_ne_zero (hcard ▸ h0)
  refine ⟨hfin, hcard, fun h => ?_⟩
  let _ := Fintype.ofFinite (H →ₐ[O] K)
  rw [finsum_eq_sum_of_fintype]
  exact algebraMap_trace_eq_sum_algHom_of_card (R := O) (S := H) (L := K)
    (by rw [← Nat.card_eq_fintype_card, hcard]) (P := fun g => g) (fun _ _ e => e) h

end GlobalTheory
end

section

namespace GlobalTheory

private lemma finite_setOf_finsupp_degree_eq (σ : Type) [Finite σ] [Nonempty σ] (e : ℕ) :
    Finite ↑{d : σ →₀ ℕ | d.degree = e} := by
  have := Fintype.ofFinite σ
  have h : Nat.card {d : σ →₀ ℕ // d.degree = e} ≠ 0 := by
    rw [_root_.GlobalTheory.natCard_degree_eq]
    have := Fintype.card_pos (α := σ)
    exact (Nat.choose_pos (by omega)).ne'
  exact Nat.finite_of_card_ne_zero h

private lemma finrank_homogeneousSubmodule_eq_choose (σ : Type) [Fintype σ] [Nonempty σ] (K : Type)
    [Field K] (e : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K e) =
      (e + Fintype.card σ - 1).choose e := by
  have := finite_setOf_finsupp_degree_eq σ e
  have := Fintype.ofFinite ↑{d : σ →₀ ℕ | d.degree = e}
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
      {d : σ →₀ ℕ | d.degree = e}).finrank_eq,
    ← _root_.GlobalTheory.natCard_degree_eq σ e, Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
  rfl

private lemma cast_choose_eq_eval_descPochhammer (m e : ℕ) (hm : 1 ≤ m) :
    (((e + m - 1).choose e : ℕ) : ℚ) = (Polynomial.C (1 / ((m - 1).factorial : ℚ)) *
      (descPochhammer ℚ (m - 1)).comp (Polynomial.X + Polynomial.C ((m - 1 : ℕ) : ℚ))).eval
        (e : ℚ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  have h1 : (e : ℚ) + ((m - 1 : ℕ) : ℚ) = ((e + (m - 1) : ℕ) : ℚ) := by push_cast; ring
  rw [h1, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    show e + m - 1 = e + (m - 1) by omega, Nat.choose_symm_add]
  have : ((m - 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem _root_.GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule :
    ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ),
      ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) =
        Q.eval (e : ℚ) := by
  intro σ _ _
  have := Fintype.ofFinite σ
  refine ⟨Polynomial.C (1 / ((Fintype.card σ - 1).factorial : ℚ)) *
    (descPochhammer ℚ (Fintype.card σ - 1)).comp
      (Polynomial.X + Polynomial.C ((Fintype.card σ - 1 : ℕ) : ℚ)), fun K _ e => ?_⟩
  rw [finrank_homogeneousSubmodule_eq_choose σ K e]
  exact cast_choose_eq_eval_descPochhammer _ e Fintype.card_pos

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem det_notMem_span_mulVec_of_socle {T : Type} [CommRing T] {g N : ℕ} (x : Fin g → T)
    (hsyz : ∀ r : Fin g → T, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) T,
      s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x)
    (hsoc : ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)))
    (a : Matrix (Fin g) (Fin g) T)
    (h : ∀ i, x i ^ (N + 1) ∈ Ideal.span (Set.range (a.mulVec x))) :
    a.det ∉ Ideal.span (Set.range (a.mulVec x)) := by
  intro hdet
  have h' : ∀ i, ∃ c : Fin g → T, ∑ j, c j * a.mulVec x j = x i ^ (N + 1) := fun i =>
    Ideal.mem_span_range_iff_exists_fun.mp (h i)
  choose b hb using h'
  let B : Matrix (Fin g) (Fin g) T := Matrix.of b
  have hB : B.mulVec (a.mulVec x) = fun i => x i ^ (N + 1) := by
    funext i
    exact hb i
  set J : Ideal T := Ideal.span (Set.range fun i => x i ^ (N + 1)) with hJ
  have hf : ∀ i, B.det * a.mulVec x i ∈ J := by
    intro i
    have e : B.adjugate.mulVec (B.mulVec (a.mulVec x)) = B.det • a.mulVec x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have e' := congrFun e i
    rw [hB, Pi.smul_apply, smul_eq_mul] at e'
    rw [← e']
    exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun j => B.adjugate i j, rfl⟩
  have hBa : (B * a).det ∈ J := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hdet
    rw [Matrix.det_mul, ← hc, Finset.mul_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Ideal.mul_mem_left _ _ (hf j)
  have hBx : (B * a).mulVec x = fun i => x i ^ (N + 1) := by
    rw [← Matrix.mulVec_mulVec, hB]
  have hD : (Matrix.diagonal fun i => x i ^ N).mulVec x = fun i => x i ^ (N + 1) := by
    funext i
    rw [Matrix.mulVec_diagonal, pow_succ]
  have key := GlobalTheory.det_sub_det_mem_span_of_mulVec_eq T g x hsyz (B * a)
    (Matrix.diagonal fun i => x i ^ N) (hBx.trans hD.symm)
  rw [hBx, Matrix.det_diagonal] at key
  have := J.sub_mem hBa key
  rw [sub_sub_cancel] at this
  exact hsoc this

theorem det_notMem_span_mulVec_X : ∀ (k : Type) [Field k] (g N : ℕ) (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k)), (∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range (a.mulVec MvPowerSeries.X))) → a.det ∉ Ideal.span (Set.range (a.mulVec MvPowerSeries.X)) := by
  intro k _ g N a h
  obtain ⟨hsyz, hsoc⟩ := GlobalTheory.mvPowerSeries_variables_syzygy_socle k g MvPowerSeries.X (fun _ => rfl)
  refine det_notMem_span_mulVec_of_socle MvPowerSeries.X hsyz (hsoc N) a fun i => ?_
  rw [pow_succ]
  exact Ideal.mul_mem_right _ _ (h i)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenericFlat


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint {O K : Type} [CommRing O] [IsDomain O] [Field K]
    (δ : O →+* K) (pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)) :
    Function.Injective δ := by
  change (Spec.map (CommRingCat.ofHom δ)) pt = genericPoint (Spec (CommRingCat.of O)) at h
  rw [genericPoint_eq_bot_of_affine] at h
  have hpt : pt.asIdeal = ⊥ := Ideal.eq_bot_of_prime (h := pt.isPrime) _
  have h2 := congrArg PrimeSpectrum.asIdeal h
  change Ideal.comap δ pt.asIdeal = ⊥ at h2
  rw [hpt, ← RingHom.ker_eq_comap_bot] at h2
  exact (RingHom.injective_iff_ker_eq_bot δ).mpr h2


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.GenericFlat.apply_eq_genericPoint {O : Type} [CommRing O] [IsDomain O]
    {T : Scheme.{0}} (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) [Flat s]
    {t : T} (ht : t ∈ genericPoints T) : s t = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
  obtain ⟨t', hspec, heq⟩ := Flat.generalizingMap s
    ((genericPoint_spec (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)).specializes (Set.mem_univ (s t)))
  have hsub : closure {t} ⊆ closure {t'} := specializes_iff_closure_subset.mp hspec
  have hcl : closure {t} = closure {t'} :=
    (show closure {t} ∈ irreducibleComponents T from ht).eq_of_le
      isIrreducible_singleton.closure hsub
  have hback : t ⤳ t' := specializes_iff_closure_subset.mpr hcl.ge
  rw [← heq, (hspec.antisymm hback).eq]


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.GenericFlat.generic_charZero_and_flat : (∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Flat s → ∀ x : T, ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ)) ∧ ∀ (R O : Type) [CommRing R] [IsDedekindDomain R] [CommRing O] [IsDomain O] (b : R →+* O) (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ T) (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Function.Injective b → Flat s → Set.range x ⊆ genericPoints T → x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap V K) ≫ v → Flat (v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b) := by
  refine ⟨fun O _ _ _ T s hs x => ?_,
    fun R O _ _ _ _ b T s V K _ _ _ _ _ x v hb hs hx hxs => ?_⟩
  · obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x))
      (isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x))
    refine ⟨ξ, hξ.specializes mem_irreducibleComponent, ?_⟩
    have hgen : ξ ∈ genericPoints T := by
      change closure {ξ} ∈ irreducibleComponents T
      rw [hξ.def]
      exact irreducibleComponent_mem_irreducibleComponents x
    let δ : O →+* T.residueField ξ := (Spec.preimage (T.fromSpecResidueField ξ ≫ s)).hom
    have hδ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ = T.fromSpecResidueField ξ ≫ s := Spec.map_preimage _
    have hinj : Function.Injective δ := by
      refine _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint δ
        (IsLocalRing.closedPoint (T.residueField ξ)) ?_
      rw [hδ]
      exact (congrArg s (Scheme.fromSpecResidueField_apply ξ _)).trans
        (_root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s hgen)
    exact charZero_of_injective_ringHom hinj
  · let φ : O →+* V := (Spec.preimage v).hom
    have hv : v = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ := (Spec.map_preimage v).symm
    have hcomp : x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) := by
      rw [hxs, hv]; exact (Spec.map_comp _ _).symm
    let pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K := IsLocalRing.closedPoint K
    have hpt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
      rw [← hcomp, Scheme.Hom.comp_apply]
      exact _root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s (hx ⟨pt, rfl⟩)
    have hφ : Function.Injective φ := by
      have h := _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ pt hpt
      rw [RingHom.coe_comp] at h
      exact h.of_comp
    have hψ : Function.Injective (φ.comp b) := hφ.comp hb
    have hmap : v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b = Spec.map (CommRingCat.ofHom (φ.comp b)) := by
      rw [hv]; exact (Spec.map_comp _ _).symm
    rw [hmap, HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (φ.comp b).toAlgebra
    change Module.Flat R V
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule.eq_bot_iff]
    intro m hm
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff m).mp hm
    rw [Submonoid.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at ha
    have h0 : (φ.comp b) a ≠ 0 := fun h =>
      nonZeroDivisors.coe_ne_zero a (hψ (h.trans (map_zero _).symm))
    exact (mul_eq_zero.mp ha).resolve_left h0

end GlobalTheory.GenericFlat
end
