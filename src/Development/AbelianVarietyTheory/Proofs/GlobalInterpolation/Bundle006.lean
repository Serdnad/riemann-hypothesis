module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

section

namespace GlobalTheory.IterationConvergence

theorem step (w : ℂ) (h : ‖w - 1‖ < 1 / 2) : (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have e2 : w + 1 = 2 - (1 - w) := by ring
  have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
    have := norm_sub_norm_le (2 : ℂ) (1 - w)
    rw [← e2] at this
    have h1 : ‖(1 : ℂ) - w‖ = ‖w - 1‖ := norm_sub_rev _ _
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  rw [e, norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

theorem iter {z : ℂ} (hz : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := step (z ^ (2 ^ k)) (hz _)
    have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [e, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
      _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := by gcongr
      _ ≤ _ := hs

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := iter hz k
  have h2 := hz (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.IterationConvergence
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem normSq_geomSum_le_fejer (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    Complex.normSq (∑ j ∈ Finset.range (J + 1), w ^ j) ≤
      (J + 1 : ℝ) + 2 * ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re := by
  have hre : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), w ^ j).re
      = 1 + ∑ j ∈ Finset.Icc 1 n, (w ^ j).re := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Complex.add_re, ih, Finset.sum_Icc_succ_top (by omega)]
      ring
  induction J with
  | zero => simp
  | succ J ih =>
    have h1 : ∑ j ∈ Finset.range (J + 1 + 1), w ^ j
        = w * (∑ j ∈ Finset.range (J + 1), w ^ j) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ']
    have h2 : ∑ j ∈ Finset.Icc 1 (J + 1), (((J + 1 : ℕ) : ℝ) + 1 - j) * (w ^ j).re
        = ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re
          + ∑ j ∈ Finset.Icc 1 (J + 1), (w ^ j).re := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
      · push_cast; ring
    have h3 := hre (J + 1)
    have hw2 : Complex.normSq w ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have := norm_nonneg w
      nlinarith
    rw [h2]
    set S := ∑ j ∈ Finset.range (J + 1), w ^ j
    rw [h1] at h3 ⊢
    have h4 : Complex.normSq (w * S + 1) = Complex.normSq w * Complex.normSq S
        + 2 * (w * S + 1).re - 1 := by
      rw [Complex.normSq_add, map_mul]
      simp
      ring
    have h5 := Complex.normSq_nonneg S
    rw [h4, h3]
    push_cast
    nlinarith

theorem fejer_re_ge (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    -(1 / 2) ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re := by
  have h := normSq_geomSum_le_fejer w hw J
  have h0 := Complex.normSq_nonneg (∑ j ∈ Finset.range (J + 1), w ^ j)
  have hJ : (0 : ℝ) < J + 1 := by positivity
  have h1 : ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re
      = (∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re) / (J + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [h1, le_div_iff₀ hJ]
  linarith

theorem sum_fejer_weights (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) = (J : ℝ) / 2 := by
  have h : ∀ n : ℕ, ∑ j ∈ Finset.Icc 1 n, (j : ℝ) = n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast; ring
  have hJ : (0 : ℝ) < J + 1 := by positivity
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, h]
  simp
  field_simp
  ring

theorem weighted_fejer_split (J : ℕ) (θ : ℝ) (w : ℂ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re
      = ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (θ * I)) ^ j).re) / 2
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (-(θ * I))) ^ j).re) / 2 := by
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : Complex.exp (θ * I) ^ j = Complex.exp (((j * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Complex.exp (-(θ * I)) ^ j = Complex.exp (((-(j * θ) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, mul_pow, e1, e2, Complex.mul_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  ring

theorem weighted_fejer_positivity : ∀ (J : ℕ) (θ : ℝ), (∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re) ∧ (J : ℝ) / 4 - 3 / 4 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (Complex.exp (θ * I) ^ j).re := by
  intro J θ
  have n1 : ‖Complex.exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have n2 : ‖Complex.exp (-(θ * I))‖ = 1 := by
    rw [Complex.exp_neg, norm_inv, n1, inv_one]
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [weighted_fejer_split]
    have a := fejer_re_ge w hw J
    have b := fejer_re_ge (w * Complex.exp (θ * I)) (by rw [norm_mul, n1, mul_one]; exact hw) J
    have c := fejer_re_ge (w * Complex.exp (-(θ * I)))
      (by rw [norm_mul, n2, mul_one]; exact hw) J
    linarith
  · rw [weighted_fejer_split]
    have a := fejer_re_ge (Complex.exp (θ * I)) n1.le J
    have b := fejer_re_ge (Complex.exp (θ * I) * Complex.exp (θ * I))
      (by rw [norm_mul, n1, mul_one]) J
    have c : Complex.exp (θ * I) * Complex.exp (-(θ * I)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [c]
    simp only [one_pow, Complex.one_re, mul_one]
    rw [sum_fejer_weights]
    linarith

end GlobalTheory
end

section

namespace GlobalTheory

theorem linearEquiv_descends_of_preserves_image {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ))
    (h : ∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) :
    ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧
      LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
        f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  classical
  let F : (ι → K) → (ι → ℂ) := fun v i => f (v i)
  have hFinj : Function.Injective F := by
    intro v w hvw
    funext i
    exact f.injective (congrFun hvw i)
  choose G hG using h
  have hG' : ∀ v, u (F v) = F (G v) := hG
  have hFadd : ∀ v w, F (v + w) = F v + F w := by
    intro v w; funext i; simp [F]
  have hFsmul : ∀ (c : K) v, F (c • v) = f c • F v := by
    intro c v; funext i; simp [F]
  let Gl : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := G
      map_add' := fun v w => hFinj (by rw [← hG', hFadd, map_add (f := _), hG', hG', hFadd])
      map_smul' := fun c v => hFinj (by
        simp only [RingHom.id_apply]
        rw [← hG', hFsmul, map_smul, hG', hFsmul]) }
  have hGl : ∀ v, Gl v = G v := fun _ => rfl
  have hinj : Function.Injective Gl := by
    intro v w hvw
    apply hFinj
    apply u.injective
    rw [hG', hG']
    exact congrArg F hvw
  let g : (ι → K) ≃ₗ[K] (ι → K) := LinearEquiv.ofInjectiveEndo Gl hinj
  have hg : ∀ v, g v = G v := fun v => by
    simp [g, hGl]
  have hsingle : ∀ j : ι, F (Pi.single j 1) = Pi.single j 1 := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij; simp [F]
    · simp [F, Pi.single_eq_of_ne hij]
  have hmat : LinearMap.toMatrix' (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
      (LinearMap.toMatrix' (g : (ι → K) →ₗ[K] (ι → K))).map f := by
    ext i j
    have := congrFun (hG' (Pi.single j 1)) i
    rw [hsingle j] at this
    simp only [LinearMap.toMatrix'_apply, Matrix.map_apply]
    simp only [LinearEquiv.coe_coe, hg]
    exact this
  refine ⟨g, fun v => ?_, ?_⟩
  · rw [hg]; exact hG v
  · rw [← LinearMap.det_toMatrix', hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      LinearMap.det_toMatrix']

end GlobalTheory
end

section

namespace GlobalTheory.FinitePointsDetect

theorem finite_points_detect : ∀ {X : Type} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥W],
    ∃ (s : Finset X), ∀ (v : ↥W), (∀ x ∈ s, (↑v : X → ℂ) x = (0 : ℂ)) → v = (0 : ↥W) := by
  intro X W _
  classical
  let ev : X → (W →ₗ[ℂ] ℂ) := fun x => (LinearMap.proj x).comp W.subtype
  let K : Finset X → Submodule ℂ W := fun s => ⨅ x ∈ s, LinearMap.ker (ev x)
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ :=
    (wellFounded_lt (α := Submodule ℂ W)).has_min (Set.range K) ⟨K ∅, ∅, rfl⟩
  have key : ∀ v ∈ K s, ∀ y : X, (↑v : X → ℂ) y = 0 := by
    intro v hv y
    have hle : K (insert y s) ≤ K s := by
      intro w hw
      simp only [K, Submodule.mem_iInf] at hw ⊢
      intro x hx
      exact hw x (Finset.mem_insert_of_mem hx)
    have heq : K (insert y s) = K s := eq_of_le_of_not_lt hle (hs _ ⟨_, rfl⟩)
    rw [← heq] at hv
    simp only [K, Submodule.mem_iInf] at hv
    have := hv y (Finset.mem_insert_self y s)
    simpa [ev] using this
  refine ⟨s, fun v hv => ?_⟩
  have hvK : v ∈ K s := by
    simp only [K, Submodule.mem_iInf]
    intro x hx
    simpa [ev] using hv x hx
  apply Subtype.ext
  funext y
  simpa using key v hvK y

end GlobalTheory.FinitePointsDetect
end

section

namespace GlobalTheory

theorem complex_rootOfUnity_mem_range_of_isPrimitiveRoot :
    ∀ (K : Type) [Field K] (s : K →+* ℂ) (n : ℕ) (ζ : K), 0 < n → IsPrimitiveRoot ζ n →
      ∀ z : ℂ, z ^ n = 1 → ∃ r : K, s r = z := by
  intro K _ s n ζ hn hζ z hz
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : IsPrimitiveRoot (s ζ) n := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Topology

namespace GlobalTheory.CuspNF.KprOpen

theorem mem_map_ker {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n] (S : Subring A) (m : S) (g : GL n A)
    (h1 : ∀ i j, (g : Matrix n n A) i j ∈ S) (h2 : ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ S)
    (h3 : ∀ i j, ∃ y ∈ S, y * (m : A) = (g : Matrix n n A) i j - (1 : Matrix n n A) i j) :
    g ∈ (Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {m}))).ker.map
      (Matrix.GeneralLinearGroup.map S.subtype) := by
  let P : Matrix n n S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let Q : Matrix n n S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hinj : Function.Injective (S.subtype.mapMatrix : Matrix n n S →+* Matrix n n A) := fun x y h => by
    ext i j
    exact congrFun (congrFun h i) j
  have hP : S.subtype.mapMatrix P = (g : Matrix n n A) := rfl
  have hQ : S.subtype.mapMatrix Q = ((g⁻¹ : GL n A) : Matrix n n A) := rfl
  let u : GL n S := ⟨P, Q, hinj (by rw [map_mul, hP, hQ, map_one, Units.mul_inv]),
    hinj (by rw [map_mul, hP, hQ, map_one, Units.inv_mul])⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  refine Units.ext ?_
  ext i j
  obtain ⟨y, hy, e⟩ := h3 i j
  have key : Ideal.Quotient.mk (Ideal.span {m}) (P i j) = Ideal.Quotient.mk (Ideal.span {m}) ((1 : Matrix n n S) i j) := by
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)
    change y * (m : A) = (g : Matrix n n A) i j - _
    rw [e]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  change Ideal.Quotient.mk (Ideal.span {m}) (P i j) = (1 : Matrix n n _) i j
  rw [key]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end GlobalTheory.CuspNF.KprOpen
end

section

open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_tsum_orbit_unfold (G G' V X : Type) [Group G] [Group G'] [MeasurableSpace G]
    [MeasurableSpace G'] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul G'] [MulAction G V]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (μ' : Measure G') [SFinite μ']
    [μ'.IsMulLeftInvariant] (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ']
    (𝓕 : Set G) (𝓕' : Set G') (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (h𝓕' : IsFundamentalDomain Γ' 𝓕' μ') (φ : G' →* G) (hφm : Measurable φ)
    (hφi : Function.Injective φ) (hΓ : ∀ g, φ g ∈ Γ ↔ g ∈ Γ') (x : V)
    (hst : φ.range = MulAction.stabilizer G x) (c : X → V) (hc : Function.Injective c)
    (hcr : ∀ y, y ∈ Set.range c ↔ ∃ γ ∈ Γ, γ • x = y) (u : G → ℝ≥0∞) (hu : Measurable u)
    (Φ : V → ℝ≥0∞) (hΦ : ∀ h : G, Φ (h⁻¹ • x) = ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ') :
    ∫⁻ h in 𝓕, ∑' i, Φ (h⁻¹ • c i) ∂μ = μ' 𝓕' * ∫⁻ h, u h ∂μ := by
  haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : MeasurableConstSMul Γ' G' := ⟨fun γ => measurable_const_mul (γ : G')⟩
  haveI : SMulInvariantMeasure Γ G μ :=
    ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  haveI : SMulInvariantMeasure Γ' G' μ' :=
    ⟨fun γ s _ => measure_preimage_mul μ' (γ : G') s⟩
  have hex : ∀ i, ∃ γ ∈ Γ, γ • x = c i := fun i => (hcr _).1 ⟨i, rfl⟩
  choose γ hγ hγx using hex
  have hfix : ∀ g, φ g • x = x := fun g => by
    have : φ g ∈ MulAction.stabilizer G x := hst ▸ ⟨g, rfl⟩
    exact this
  let f : X × Γ' → Γ := fun p => ⟨γ p.1 * φ p.2, Γ.mul_mem (hγ _) ((hΓ _).2 p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hab
      have h1 : γ i * φ a = γ j * φ b := congrArg Subtype.val hab
      have h2 : i = j := by
        apply hc
        have := congrArg (· • x) h1
        simpa [mul_smul, hfix, hγx] using this
      subst h2
      have h3 : a = b := Subtype.ext (hφi (mul_left_cancel h1))
      rw [h3]
    · rintro ⟨δ, hδ⟩
      obtain ⟨i, hi⟩ := (hcr (δ • x)).2 ⟨δ, hδ, rfl⟩
      have h1 : (γ i)⁻¹ * δ ∈ φ.range := by
        rw [hst, MulAction.mem_stabilizer_iff, mul_smul, ← hi, ← hγx, inv_smul_smul]
      obtain ⟨a, ha⟩ := h1
      have ha' : a ∈ Γ' := (hΓ a).1 (ha ▸ Γ.mul_mem (Γ.inv_mem (hγ i)) hδ)
      refine ⟨(i, ⟨a, ha'⟩), Subtype.ext ?_⟩
      show γ i * φ a = δ
      rw [ha, mul_inv_cancel_left]
  let F : G → ℝ≥0∞ := fun h => ∫⁻ g in 𝓕', u ((φ g)⁻¹ * h) ∂μ'
  have hK : Measurable (fun p : G × G' => u ((φ p.2)⁻¹ * p.1)) :=
    hu.comp (((hφm.comp measurable_snd).inv).mul measurable_fst)
  have hF : Measurable F := hK.lintegral_prod_right'
  have step : ∀ h : G, ∑' i, Φ (h⁻¹ • c i) = ∑' δ : Γ, F (δ⁻¹ • h) := by
    intro h
    rw [← (Equiv.ofBijective f hf).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun i => ?_
    have h1 : h⁻¹ • c i = ((γ i)⁻¹ * h)⁻¹ • x := by
      rw [mul_inv_rev, inv_inv, mul_smul, hγx]
    rw [h1, hΦ, h𝓕'.lintegral_eq_tsum'']
    refine tsum_congr fun a => ?_
    refine lintegral_congr fun g => ?_
    congr 1
    show (φ ((a : G') * g))⁻¹ * ((γ i)⁻¹ * h) = (φ g)⁻¹ * ((γ i * φ a)⁻¹ * h)
    simp [mul_assoc]
  simp_rw [step]
  rw [lintegral_tsum (f := fun (δ : Γ) h => F (δ⁻¹ • h)) (fun δ => (hF.comp (measurable_const_smul δ⁻¹)).aemeasurable),
    ← h𝓕.lintegral_eq_tsum' F]
  show ∫⁻ h, ∫⁻ g in 𝓕', u ((φ g)⁻¹ * h) ∂μ' ∂μ = _
  rw [lintegral_lintegral_swap hK.aemeasurable]
  simp_rw [lintegral_mul_left_eq_self u]
  rw [setLIntegral_const, mul_comm]

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem valuation_of_generator_of_pow (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (π : 𝓞 K) (h : 𝔭.asIdeal ^ n = Ideal.span {π}) :
    𝔭.valuation K (π : K) = WithZero.exp (-(n : ℤ)) := by
  have hπ : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at h
    exact 𝔭.ne_bot (pow_eq_zero_iff'.mp h).1
  rw [show (π : K) = algebraMap (𝓞 K) K π from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    𝔭.intValuation_if_neg hπ, ← h, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr 𝔭.ne_bot) 𝔭.associates_irreducible,
    Associates.count_self 𝔭.associates_irreducible, mul_one]

end GlobalTheory
end

section

namespace GlobalTheory.MaximalIdealMembership

theorem mem_maximalIdeal_iff {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (f : MvPowerSeries (Fin a) O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ↔
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

end GlobalTheory.MaximalIdealMembership
end
