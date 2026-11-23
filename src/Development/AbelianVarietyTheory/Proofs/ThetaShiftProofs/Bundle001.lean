module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.OfNorm
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Submodule.Basic

@[expose] public section

section

namespace GlobalTheory

theorem exists_basis_over_embedding (K : Type) [Field K] (σ₀ : K →+* ℂ) (m : ℕ)
    (a : Fin m → ℂ) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (c : Fin m → Fin n → K),
      (∀ t : Fin n → K, ∑ b, σ₀ (t b) * e b = 0 → t = 0) ∧
        ∀ i, a i = ∑ b, σ₀ (c i b) * e b := by
  letI : Algebra K ℂ := σ₀.toAlgebra
  have hs : ∀ (k : K) (z : ℂ), k • z = σ₀ k * z := fun k z => rfl
  let V : Submodule K ℂ := Submodule.span K (Set.range a)
  haveI : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range a)
  let B := Module.finBasis K V
  have ha : ∀ i, a i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.finrank K V, fun b => (B b : ℂ), fun i b => B.repr ⟨a i, ha i⟩ b, ?_, ?_⟩
  · intro t ht
    have hli := Fintype.linearIndependent_iff.1 B.linearIndependent t
    funext b
    refine hli ?_ b
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs, Submodule.coe_zero]
    exact ht
  · intro i
    have h := congrArg (Subtype.val : V → ℂ) (B.sum_repr ⟨a i, ha i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs] at h
    exact h.symm

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory.RowDet

theorem det_mem_subalgebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {m : Type*} [Fintype m] [DecidableEq m] (S : Subalgebra R A) (M : Matrix m m A)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem notMem_vars_det {R σ : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]
    (a : σ) (M : Matrix m m (MvPolynomial σ R)) (h : ∀ i j, a ∉ (M i j).vars) :
    a ∉ M.det.vars := by
  have : M.det ∈ supported R ({a}ᶜ : Set σ) := by
    refine det_mem_subalgebra _ _ fun i j => ?_
    rw [mem_supported]
    intro b hb hba
    rw [Set.mem_singleton_iff] at hba
    exact h i j (hba ▸ hb)
  rw [mem_supported] at this
  intro ha
  exact this ha rfl

theorem det_updateRow_single {A : Type*} [CommRing A] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    (M.updateRow (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · have : (-1 : A) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
      rw [← two_mul, pow_mul]; simp
    rw [this, Matrix.updateRow_self, Pi.single_eq_same, one_mul, one_mul, Fin.succAbove_last]
    congr 1
    ext i j
    simp [Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem minor_not_dvd {R σ : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (e : Fin (n + 2) × Fin (n + 2) → σ) (he : Function.Injective e) :
    ¬ ((Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ∣
      (Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  classical
  intro h
  let w : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
    (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) R).submatrix (Equiv.swap 0 (Fin.last (n + 1))) id
  let v : σ → R := Function.extend e (fun p => w p.1 p.2) 0
  have hv : ∀ i k, v (e (i, k)) = w i k := fun i k => he.extend_apply _ _ _
  have h2 := map_dvd (eval v) h
  rw [RingHom.map_det, RingHom.map_det] at h2
  have e1 : (eval v).mapMatrix
      (Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)) = w := by
    ext i k; simp [hv]
  have e2 : ((eval v).mapMatrix ((Matrix.of fun i k : Fin (n + 2) =>
      (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc)).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    simp [hv, w, Matrix.one_apply, (Fin.castSucc_lt_last j).ne']
  rw [e1, e2, zero_dvd_iff] at h2
  have hu : IsUnit w.det := by
    rw [Matrix.det_permute, Matrix.det_one, mul_one]
    exact (Units.isUnit _).map (Int.castRingHom R)
  exact hu.ne_zero h2

theorem irreducible_det_of_isRelPrime {R σ : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : Function.Injective e)
    (h0 : ((Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0)
    (h : IsRelPrime ((Matrix.of fun i k : Fin (n + 1) =>
        (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc).det
      (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det) :
    Irreducible (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  classical
  set A := (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)) with hA
  let r : Fin (n + 1) → MvPolynomial σ R := fun k => if k = Fin.last n then 0 else A (Fin.last n) k
  have hD : A.det = (A.submatrix Fin.castSucc Fin.castSucc).det * X (e (Fin.last n, Fin.last n))
      + (A.updateRow (Fin.last n) r).det := by
    rw [← det_updateRow_single, mul_comm, ← Matrix.det_updateRow_smul,
      ← Matrix.det_updateRow_add]
    congr 1
    rw [eq_comm]
    convert Matrix.updateRow_eq_self A (Fin.last n)
    ext1 k
    by_cases hk : k = Fin.last n
    · subst hk; simp [r, A]
    · simp [r, hk]
  rw [hD] at h ⊢
  refine irreducible_mul_X_add _ _ _ h0 ?_ ?_ ?_
  · refine notMem_vars_det _ _ fun i j => ?_
    simp [A, vars_X, he.eq_iff, (Fin.castSucc_lt_last j).ne']
  · refine notMem_vars_det _ _ fun i j => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      by_cases hj : j = Fin.last n
      · simp [r, hj]
      · simp [r, hj, A, vars_X, he.eq_iff, Ne.symm hj]
    · simp [Matrix.updateRow_ne hi, A, vars_X, he.eq_iff, Ne.symm hi]
  · intro c hc1 hc2
    exact h hc1 (dvd_add (hc1.mul_right _) hc2)

theorem irreducible_det {R σ : Type*} [CommRing R] [IsDomain R] (n : ℕ) :
    ∀ (e : Fin (n + 1) × Fin (n + 1) → σ), Function.Injective e →
    Irreducible (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  induction n with
  | zero =>
    intro e he
    refine irreducible_det_of_isRelPrime e he ?_ ?_
    · simp
    · rw [Matrix.det_isEmpty]; exact isRelPrime_one_left
  | succ n ih =>
    intro e he
    have h := ih (fun p => e (p.1.castSucc, p.2.castSucc)) (fun p q hpq => by
      have := he hpq
      simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
      exact Prod.ext this.1 this.2)
    exact irreducible_det_of_isRelPrime e he h.ne_zero
      (h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he))

theorem minor_isRelPrime {R σ : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : Function.Injective e) :
    ((Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0 ∧
    IsRelPrime ((Matrix.of fun i k : Fin (n + 1) =>
        (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc).det
      (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  cases n with
  | zero => rw [Matrix.det_isEmpty]; exact ⟨one_ne_zero, isRelPrime_one_left⟩
  | succ n =>
    have h := irreducible_det (R := R) n (fun p => e (p.1.castSucc, p.2.castSucc))
      (fun p q hpq => by
        have := he hpq
        simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
        exact Prod.ext this.1 this.2)
    exact ⟨h.ne_zero, h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he)⟩

end GlobalTheory.RowDet
end

section

open Complex

namespace GlobalTheory

theorem exists_const_ratio_of_norm_eq :
    ∀ (I : Type) (T K : ℝ) (f g : I → ℂ → ℂ) (c : ℂ → ℂ), 0 < K →
      (∀ i, DifferentiableOn ℂ (f i) {w | T < w.im} ∧ DifferentiableOn ℂ (g i) {w | T < w.im}) →
      (∀ i w, T < w.im → f i w = c w * g i w ∧ ‖f i w‖ = K * ‖g i w‖) →
      ∃ κ : ℂ, ‖κ‖ = K ∧ ∀ i w, T < w.im → f i w = κ * g i w := by
  intro I T K f g c hK hd h
  by_cases h0 : ∀ i w, T < w.im → g i w = 0
  · refine ⟨K, by simp [abs_of_pos hK], fun i w hw => ?_⟩
    rw [(h i w hw).1, h0 i w hw]; simp
  push_neg at h0
  obtain ⟨i₀, w₀, hw₀, hg₀⟩ := h0
  have hU : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {w : ℂ | T < w.im} := (convex_halfSpace_im_gt T).isPreconnected
  have hca : ContinuousAt (g i₀) w₀ :=
    (hd i₀).2.continuousOn.continuousAt (hU.mem_nhds hw₀)
  have hev : ∀ᶠ w in nhds w₀, T < w.im ∧ g i₀ w ≠ 0 :=
    (hU.eventually_mem hw₀).and (hca.eventually_ne hg₀)
  obtain ⟨r, hr, hB⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : Metric.ball w₀ r ⊆ {w : ℂ | T < w.im} := fun w hw => (hB w hw).1
  have hcq : ∀ w ∈ Metric.ball w₀ r, c w = f i₀ w / g i₀ w := fun w hw => by
    rw [(h i₀ w (hB w hw).1).1, mul_div_cancel_right₀ _ (hB w hw).2]
  have hcd : DifferentiableOn ℂ c (Metric.ball w₀ r) :=
    (((hd i₀).1.mono hsub).div ((hd i₀).2.mono hsub) fun w hw => (hB w hw).2).congr hcq
  have hcn : ∀ w ∈ Metric.ball w₀ r, ‖c w‖ = K := fun w hw => by
    rw [hcq w hw, norm_div, (h i₀ w (hB w hw).1).2,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 (hB w hw).2)]
  have hm : w₀ ∈ Metric.ball w₀ r := Metric.mem_ball_self hr
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball w₀ r).isPreconnected Metric.isOpen_ball hcd hm
    (fun w hw => by
      show ‖c w‖ ≤ ‖c w₀‖
      rw [hcn w hw, hcn w₀ hm])
  refine ⟨c w₀, hcn w₀ hm, fun i w hw => ?_⟩
  have ha : AnalyticOnNhd ℂ (f i) {w : ℂ | T < w.im} := (hd i).1.analyticOnNhd hU
  have hb : AnalyticOnNhd ℂ (fun w => c w₀ * g i w) {w : ℂ | T < w.im} :=
    ((hd i).2.const_mul (c w₀)).analyticOnNhd hU
  have he : f i =ᶠ[nhds w₀] fun w => c w₀ * g i w := by
    filter_upwards [Metric.ball_mem_nhds w₀ hr] with z hz
    rw [(h i z (hB z hz).1).1, hconst hz]
    rfl
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb hUc hw₀ he hw

end GlobalTheory
end

section

namespace GlobalTheory.SummableExpNegAbsSum

theorem summable_int : Summable fun n : ℤ ↦ Real.exp (-|(n : ℝ)|) := by
  have h : Summable fun n : ℕ ↦ Real.exp (-(n : ℝ)) := Real.summable_exp_neg_nat
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h

theorem summable_exp_neg_sum_abs {ι : Type} [inst : Fintype ι] :
    Summable fun (m : ι → ℤ) ↦ Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) := by
  classical
  set g : ℤ → ℝ := fun n ↦ Real.exp (-|(n : ℝ)|) with hg
  have hgpos : ∀ n, 0 ≤ g n := fun n => (Real.exp_pos _).le
  have hgs : Summable g := summable_int
  have hprod : ∀ m : ι → ℤ, Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) = ∏ i : ι, g (m i) := by
    intro m
    simp only [hg]
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  simp_rw [hprod]
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' n : ℤ, g n)
    (fun m => Finset.prod_nonneg fun i _ => hgpos _) fun s => ?_
  set T : ι → Finset ℤ := fun i => s.image (fun m : ι → ℤ => m i) with hT
  have hsub : s ⊆ Fintype.piFinset T := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hm
  calc ∑ m ∈ s, ∏ i : ι, g (m i)
      ≤ ∑ m ∈ Fintype.piFinset T, ∏ i : ι, g (m i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          Finset.prod_nonneg fun i _ => hgpos _
    _ = ∏ i : ι, ∑ n ∈ T i, g n := (Finset.prod_univ_sum T (fun _ n => g n)).symm
    _ ≤ ∏ _i : ι, ∑' n : ℤ, g n := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => hgpos _)
          fun i _ => ?_
        exact hgs.sum_le_tsum _ fun _ _ => hgpos _

end GlobalTheory.SummableExpNegAbsSum
end

section

namespace GlobalTheory.SpanSingleInlMembership

theorem mem_span_single_inl_iff {g : ℕ} (S : Finset (Fin g)) (u : Fin g ⊕ Fin g → ℤ) :
    u ∈ Submodule.span ℤ ((fun (k : Fin g) ↦ Pi.single (Sum.inl k) (1 : ℤ)) '' (↑S : Set (Fin g))) ↔
      (∀ (k : Fin g), u (Sum.inr k) = (0 : ℤ)) ∧ ∀ k ∉ S, u (Sum.inl k) = (0 : ℤ) := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      refine ⟨fun k => by simp, fun k hk => ?_⟩
      have hne : k ≠ j := fun e => hk (e ▸ hj)
      simp [hne]
    | zero => simp
    | add x y _ _ hx hy =>
      exact ⟨fun k => by simp [hx.1 k, hy.1 k], fun k hk => by simp [hx.2 k hk, hy.2 k hk]⟩
    | smul a x _ hx =>
      exact ⟨fun k => by simp [hx.1 k], fun k hk => by simp [hx.2 k hk]⟩
  · rintro ⟨h1, h2⟩
    have hu : u = ∑ k ∈ S, u (Sum.inl k) • (Pi.single (Sum.inl k) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) := by
      funext i
      rcases i with j | j
      · by_cases hj : j ∈ S
        · simp [Finset.sum_apply, Pi.single_apply, hj]
        · simp [Finset.sum_apply, Pi.single_apply, hj, h2 j hj]
      · simp [Finset.sum_apply, h1 j]
    rw [hu]
    exact Submodule.sum_mem _ fun k hk =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)

end GlobalTheory.SpanSingleInlMembership
end
