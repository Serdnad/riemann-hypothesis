module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

section

private theorem UpperTheory.Reformulated.B.MovedPointDeterminant.exists_moved_ne {a : ℕ} {σ : Equiv.Perm (Fin a)} (hσ : σ ≠ 1)
    (i : Fin a) : ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra h
  push Not at h
  apply hσ
  ext1 j
  by_cases hj : j = i
  · subst hj
    by_contra hne
    exact hne (σ.injective (h _ hne))
  · exact h j hj

theorem UpperTheory.Reformulated.B.MovedPointDeterminant.cv_det :
    ∀ {a : ℕ} {m : ℝ → Matrix (Fin a) (Fin a) ℂ}
    {Y : Matrix (Fin a) (Fin a) ℂ},
    m (0 : ℝ) = (1 : Matrix (Fin a) (Fin a) ℂ) →
      (∀ (i j : Fin a), HasDerivAt (fun (s : ℝ) ↦ m s i j) (Y i j) (0 : ℝ)) →
        HasDerivAt (fun (s : ℝ) ↦ (m s).det) (∑ i : Fin a, Y i i) (0 : ℝ) := by
  intro a m Y h0 hd
  have key : HasDerivAt
      (fun s : ℝ ↦ ∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, m s (σ i) i)
      (∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, m 0 (σ j) j) • Y (σ i) i) 0 :=
    HasDerivAt.fun_sum fun σ _ ↦
      (HasDerivAt.fun_finsetProd (f := fun i s ↦ m s (σ i) i)
        (fun i _ ↦ hd (σ i) i)).const_mul _
  have hval : (∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, m 0 (σ j) j) • Y (σ i) i) = ∑ i, Y i i := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin a))]
    · simp [h0]
    · intro σ _ hσ
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ ↦ ?_)
      obtain ⟨j, hj, hm⟩ := UpperTheory.Reformulated.B.MovedPointDeterminant.exists_moved_ne hσ i
      rw [Finset.prod_eq_zero (i := j) (by simp [hj]) (by rw [h0, Matrix.one_apply_ne hm]),
        zero_smul]
    · simp
  rw [hval] at key
  simpa only [Matrix.det_apply'] using key
end

section

open Filter Topology in
theorem UpperTheory.Reformulated.B.GaloisBoundFirst.main :
    ∀ (B : ℂ → ℂ),
      Differentiable ℂ B →
        (∃ (z : ℂ), B z ≠ (0 : ℂ)) →
          ∀ (a : ℂ), ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ (0 : ℂ) ∧ ∀ (z : ℂ), B z = (z - a) ^ k * v z := by
  rintro B hB ⟨z0, hz0⟩ a
  have han : AnalyticOnNhd ℂ B Set.univ := hB.differentiableOn.analyticOnNhd isOpen_univ
  have hnot : ¬ ∀ᶠ z in 𝓝 a, B z = 0 := fun h => hz0
    (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
      (Set.mem_univ z0))
  obtain ⟨k, g, hg, hga, hev⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff (han a (Set.mem_univ a))).2 hnot
  have hev' : ∀ᶠ z in 𝓝 a, z ≠ a → B z / (z - a) ^ k = g z := by
    filter_upwards [hev] with z hz hne
    have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hne)
    rw [hz, smul_eq_mul]
    field_simp
  let v : ℂ → ℂ := fun z => if z = a then g a else B z / (z - a) ^ k
  have hva : v a = g a := by simp [v]
  have hvne : ∀ z, z ≠ a → v z = B z / (z - a) ^ k := fun z hz => by simp [v, hz]
  refine ⟨k, v, ?_, by rwa [hva], ?_⟩
  · intro z
    by_cases hz : z = a
    · subst hz
      have : v =ᶠ[𝓝 z] g := by
        filter_upwards [hev'] with w hw
        by_cases hwz : w = z
        · rw [hwz, hva]
        · rw [hvne w hwz, hw hwz]
      exact (hg.differentiableAt.congr_of_eventuallyEq this)
    · have hd : DifferentiableAt ℂ (fun w => B w / (w - a) ^ k) z :=
        (hB z).div (((differentiableAt_id).sub (differentiableAt_const a)).pow k)
          (pow_ne_zero _ (sub_ne_zero.2 hz))
      have : v =ᶠ[𝓝 z] fun w => B w / (w - a) ^ k := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        exact hvne w hw
      exact hd.congr_of_eventuallyEq this
  · intro z
    by_cases hz : z = a
    · subst hz
      have hB0 : B z = (z - z) ^ k * g z := by
        simpa [smul_eq_mul] using hev.self_of_nhds
      rw [hva]; exact hB0
    · rw [hvne z hz]
      have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
      field_simp
end

section

noncomputable def UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm :
    {g : ℕ} → Matrix (Fin g) (Fin g) ℂ → (Fin g → ℂ) → (Fin g → ℂ) → ℂ :=
    fun {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) ↦ z ⬝ᵥ Hm.mulVec (Star.star w)

noncomputable def UpperTheory.Reformulated.B.HermitianFormImEqSum.hv :
    {n : ℕ} → Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → (Fin n → ℂ) → ℂ :=
    fun {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) ↦ Star.star y ⬝ᵥ M.mulVec x

private theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span {V : Type} [AddCommGroup V] [Module ℝ V]
    (f h : V → ℝ) (S : Set V) (hS : Submodule.span ℝ S = ⊤)
    (fa : ∀ x y, f (x + y) = f x + f y) (fs : ∀ (c : ℝ) x, f (c • x) = c * f x)
    (ha : ∀ x y, h (x + y) = h x + h y) (hs : ∀ (c : ℝ) x, h (c • x) = c * h x)
    (H : ∀ a ∈ S, f a = h a) (x : V) : f x = h x := by
  have hx : x ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem a ha => exact H a ha
  | zero =>
    have h1 := fs 0 0
    have h2 := hs 0 0
    simp only [zero_smul, zero_mul] at h1 h2
    rw [h1, h2]
  | add a b _ _ h1 h2 => rw [fa, ha, h1, h2]
  | smul c a _ h1 => rw [fs, hs, h1]

private theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos (c : ℝ) (a b : ℂ) : (a * (c • b)).re = c * (a * b).re := by
  rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]

theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.bil_eq :
    ∀ {P : Type} [inst : Fintype P] [DecidableEq P] {n g : ℕ} (R : (P → Fin n → ℂ) ≃ₗ[ℝ] Fin g → ℂ)
      (Hm : Matrix (Fin g) (Fin g) ℂ) (M : P → Matrix (Fin n) (Fin n) ℂ) (s : P → ℂ) (r : P → ℝ) (S : Set (P → Fin n → ℂ)),
      Submodule.span ℝ S = ⊤ →
        (∀ a ∈ S,
            ∀ b ∈ S,
              (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm ((R : (P → Fin n → ℂ) → Fin g → ℂ) a) ((R : (P → Fin n → ℂ) → Fin g → ℂ) b)).im =
                ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (b v)).re) →
          ∀ (x y : P → Fin n → ℂ),
            (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm ((R : (P → Fin n → ℂ) → Fin g → ℂ) x) ((R : (P → Fin n → ℂ) → Fin g → ℂ) y)).im =
              ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (x v) (y v)).re := by
  intro P _ _ n g R Hm M s r S hS H x y
  have step : ∀ a ∈ S, ∀ y : P → Fin n → ℂ,
      (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R a) (R y)).im =
        ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (y v)).re := by
    intro a ha y
    refine UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span (fun y => (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R a) (R y)).im)
      (fun y => ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (y v)).re)
      S hS ?_ ?_ ?_ ?_ (H a ha) y
    · intro u w
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add,
        Complex.add_im]
    · intro c u
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_smul, star_smul, star_trivial, Matrix.mulVec_smul,
        dotProduct_smul, Complex.smul_im, smul_eq_mul]
    · intro u w
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.add_apply, star_add, add_dotProduct, mul_add,
        Complex.add_re, Finset.sum_add_distrib]
    · intro c u
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct,
        UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos, Finset.mul_sum, mul_left_comm c]
  refine UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span (fun x => (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R x) (R y)).im)
    (fun x => ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (x v) (y v)).re)
    S hS ?_ ?_ ?_ ?_ (fun a ha => step a ha y) x
  · intro u w
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_add (f := _), add_dotProduct, Complex.add_im]
  · intro c u
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_smul, smul_dotProduct, Complex.smul_im, smul_eq_mul]
  · intro u w
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.add_apply, Matrix.mulVec_add, dotProduct_add, mul_add,
      Complex.add_re, Finset.sum_add_distrib]
  · intro c u
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul,
      UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos, Finset.mul_sum, mul_left_comm c]
end

section

namespace ZbYhc5Helpers

private lemma key {g : ℕ} (c : ℂ) (u u' : Fin g → ℂ) :
    c • (u + Complex.I • u') = (c.re • u - c.im • u') + Complex.I • (c.im • u + c.re • u') := by
  funext i
  apply Complex.ext <;> simp [Complex.real_smul] <;> ring

end ZbYhc5Helpers

theorem UpperTheory.Reformulated.B.Yhc5.main :
    ∀ {g : ℕ} {T : Set (Fin g → ℂ)} {w : Fin g → ℂ},
      w ∈ Submodule.span ℂ T → ∃ u ∈ Submodule.span ℝ T, ∃ u' ∈ Submodule.span ℝ T, w = u + Complex.I • u' := by
  intro g T w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨x, Submodule.subset_span hx, 0, Submodule.zero_mem _, by simp⟩
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    obtain ⟨b, hb, b', hb', rfl⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', by
      rw [smul_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    refine ⟨c.re • a - c.im • a', ?_, c.im • a + c.re • a', ?_, ZbYhc5Helpers.key c a a'⟩
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
end

section

private theorem exists_ker {n g : ℕ} (f : (Fin n → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (U : Submodule ℂ (Fin g → ℂ)) (hU : ∀ y, f y ∈ U)
    (hI : ∀ y, f y = 0 → f (Complex.I • y) = 0) :
    ∃ K : Submodule ℂ (Fin n → ℂ), (∀ y, y ∈ K ↔ f y = 0) ∧
      n ≤ Module.finrank ℂ K + Module.finrank ℂ U := by
  let K : Submodule ℂ (Fin n → ℂ) :=
    { carrier := {y | f y = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add (f := _), ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun z y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        have hz : z • y = z.re • y + z.im • (Complex.I • y) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im z]
          ring
        rw [hz, map_add (f := _), map_smul, map_smul, hy, hI y hy, smul_zero, smul_zero, add_zero] }
  refine ⟨K, fun y => Iff.rfl, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : LinearMap.ker f = K.restrictScalars ℝ := by
    ext y
    rfl
  have h3 : LinearMap.range f ≤ U.restrictScalars ℝ := by
    rintro _ ⟨y, rfl⟩
    exact hU y
  have h4 := Submodule.finrank_mono h3
  have h5 : Module.finrank ℝ (U.restrictScalars ℝ) = 2 * Module.finrank ℂ U :=
    finrank_real_of_complex U
  have h6 : Module.finrank ℝ (K.restrictScalars ℝ) = 2 * Module.finrank ℂ K :=
    finrank_real_of_complex K
  have h7 : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [finrank_real_of_complex]; simp
  rw [h2, h6, h7] at h1
  omega

theorem UpperTheory.hermitian_positive_symplectic :
    ∀ {g j j' : ℕ} (p : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ)
        (S : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (c : ℝ) (U U' : Submodule ℂ (Fin g → ℂ)),
        (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (dotProduct z (H.mulVec (star z))).re) →
        IsUnit S.det → 0 < c →
        (∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
          2 * (Complex.I * (c : ℂ) * dotProduct (star y') (S.mulVec y)).re) →
        Module.finrank ℂ U = j' → Module.finrank ℂ U' = j →
        (∀ y, p y - Complex.I • p (Complex.I • y) ∈ U) →
        (∀ y, p y + Complex.I • p (Complex.I • y) ∈ U') →
        ∃ K K' : Submodule ℂ (Fin (j + j') → ℂ),
          j ≤ Module.finrank ℂ K ∧ j' ≤ Module.finrank ℂ K' ∧
          (∀ y ∈ K, p y - Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K', p y + Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) ∧
          (∀ y ∈ K', y ≠ 0 → (dotProduct (star y) (S.mulVec y)).re < 0) ∧
          ∀ y ∈ K, ∀ y' ∈ K', dotProduct (star y') (S.mulVec y) = 0 := by
  intro g j j' p H S c U U' hH hS hc hp hU hU' hA hB
  let Q : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun y => Complex.I • p (Complex.I • y)
      map_add' := fun a b => by rw [smul_add, map_add (f := _), smul_add]
      map_smul' := fun r a => by
        rw [smul_comm Complex.I r a, map_smul, smul_comm Complex.I r]; rfl }
  have hII : ∀ {m : ℕ} (v : Fin m → ℂ), Complex.I • Complex.I • v = -v := by
    intro m v
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  have eA : ∀ y, p y - Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = -(Complex.I • p y) := by
    intro y hy
    rw [sub_eq_zero.mp hy, hII, neg_neg]
  have eB : ∀ y, p y + Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = Complex.I • p y := by
    intro y hy
    rw [eq_neg_of_add_eq_zero_left hy, smul_neg, hII, neg_neg]
  obtain ⟨K, hK, dK⟩ := exists_ker (p - Q) U hA (by
    intro y hy
    change p (Complex.I • y) - Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eA y hy, smul_neg, sub_self])
  obtain ⟨K', hK', dK'⟩ := exists_ker (p + Q) U' hB (by
    intro y hy
    change p (Complex.I • y) + Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eB y hy, smul_neg, add_neg_cancel])
  have hp' : ∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
      -(2 * c * (dotProduct (star y') (S.mulVec y)).im) := by
    intro y y'
    rw [hp]
    simp
    ring
  have hinj : ∀ y, y ≠ 0 → p y ≠ 0 := by
    intro y hy h0
    apply hy
    have hz : ∀ y', (dotProduct (star y') (S.mulVec y)).im = 0 := by
      intro y'
      have h := hp' y y'
      rw [h0, zero_dotProduct, Complex.zero_im] at h
      have : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hc.ne'
    have hSy : S.mulVec y = 0 := by
      ext i
      have h1 := hz (Pi.single i 1)
      have h2 := hz (Pi.single i Complex.I)
      simp [← Pi.single_star] at h1 h2
      apply Complex.ext <;> simp [h1, h2]
    exact Matrix.eq_zero_of_mulVec_eq_zero hS.ne_zero hSy
  refine ⟨K, K', by omega, by omega, fun y hy => (hK y).mp hy, fun y hy => (hK' y).mp hy,
    ?_, ?_, ?_⟩
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eA y ((hK y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (neg_nonneg.mpr (not_lt.mp hn))
    linarith
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eB y ((hK' y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (not_lt.mp hn)
    linarith
  · intro y hy y' hy'
    have e1 := eA y ((hK y).mp hy)
    have e2 := eB y' ((hK' y').mp hy')
    have h1 := hp' y y'
    have h2 := hp' (Complex.I • y) y'
    have h3 := hp' y (Complex.I • y')
    have h4 := hp' (Complex.I • y) (Complex.I • y')
    rw [e1] at h2 h4
    rw [e2] at h3 h4
    simp [Matrix.mulVec_smul, Matrix.mulVec_neg] at h2 h3 h4
    have r1 : c * (dotProduct (star y') (S.mulVec y)).re = 0 := by linarith
    have r2 : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
    exact Complex.ext ((mul_eq_zero.mp r1).resolve_left hc.ne')
      ((mul_eq_zero.mp r2).resolve_left hc.ne')
end

section

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh1.map_involution_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (φ : G ≃ₜ* G) (hφ : ∀ x, φ (φ x) = x) :
    μ.map φ = μ := by
  have h1 : φ.trans φ = ContinuousMulEquiv.refl G := by
    ext x
    exact hφ x
  have h2 : mulEquivHaarChar φ * mulEquivHaarChar φ = 1 := by
    rw [← mulEquivHaarChar_trans, h1, mulEquivHaarChar_refl]
  have h3 : mulEquivHaarChar φ = 1 := by
    have h : (mulEquivHaarChar φ) ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h
  have h4 := mulEquivHaarChar_smul_map μ φ
  rwa [h3, one_smul] at h4

theorem UpperTheory.Reformulated.B.Qh1.twist_general.{u_1} :
    ∀ {G : Type u_1} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [inst_5 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G)
    [Countable ↥Γ] {F : Set G},
    MeasureTheory.IsFundamentalDomain (↥Γ) F μ →
      ∀ (θ : G →* G),
        Continuous (⇑θ : G → G) →
          (∀ (x : G), (θ : G → G) ((θ : G → G) x) = x) →
            (∀ γ ∈ Γ, (θ : G → G) γ ∈ Γ) →
              ∀ (f : G → ℂ),
                (∀ (γ : ↥Γ) (x : G), f ((↑γ : G) * x) = f x) →
                  MeasureTheory.Integrable f (μ.restrict F) →
                    MeasureTheory.Integrable (fun (x : G) ↦ f ((θ : G → G) x)) (μ.restrict F) ∧
                      ∫ (x : G) in F, f ((θ : G → G) x) ∂μ = ∫ (x : G) in F, f x ∂μ := by
  intro G _ _ _ _ _ _ _ μ _ Γ _ F hF θ hθc hθθ hθΓ f hf hfi
  let φ : G ≃ₜ* G :=
    { toFun := θ
      invFun := θ
      left_inv := hθθ
      right_inv := hθθ
      map_mul' := map_mul θ
      continuous_toFun := hθc
      continuous_invFun := hθc }
  have hmp : MeasureTheory.MeasurePreserving θ μ μ :=
    ⟨hθc.measurable, UpperTheory.Reformulated.B.Qh1.map_involution_eq μ φ hθθ⟩
  have hemb : MeasurableEmbedding (θ : G → G) := φ.toHomeomorph.measurableEmbedding
  let e : Γ → Γ := fun γ => ⟨θ γ, hθΓ γ γ.2⟩
  have he : Function.Involutive e := fun γ => Subtype.ext (hθθ γ)
  have hF' : MeasureTheory.IsFundamentalDomain Γ (θ ⁻¹' F) μ := by
    refine hF.preimage_of_equiv hmp.quasiMeasurePreserving he.bijective ?_
    intro γ x
    change θ (θ γ * x) = γ * θ x
    rw [map_mul, hθθ]
  have hg : ∀ (γ : Γ) (x : G), f (θ (γ • x)) = f (θ x) := by
    intro γ x
    change f (θ (γ * x)) = f (θ x)
    rw [map_mul]
    exact hf (e γ) (θ x)
  refine ⟨?_, ?_⟩
  · have h1 : MeasureTheory.IntegrableOn (fun x => f (θ x)) (θ ⁻¹' F) μ :=
      (hmp.integrableOn_comp_preimage hemb).2 hfi
    exact (hF.integrableOn_iff hF' (f := fun x => f (θ x)) hg).2 h1
  · rw [hF.setIntegral_eq hF' (f := fun x => f (θ x)) hg]
    exact hmp.setIntegral_preimage_emb hemb f F
end

section

theorem UpperTheory.mean_value_uniqueness :
    ∀ {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace K] [CompactSpace K]
        [MeasurableSpace K] [OpensMeasurableSpace K] (κ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure κ]
        (a : K → G) (p : K → ℂ), Continuous a → Continuous p → ∀ φ ψ : G → ℂ, Continuous φ → Continuous ψ →
        (∀ g, ∫ k, p k * φ (g * a k) ∂κ = φ g) → (∀ g, ∫ k, p k * ψ (g * a k) ∂κ = ψ g) →
        ∀ g, ∫ k, p k * (φ + ψ) (g * a k) ∂κ = (φ + ψ) g := by
  intro G K _ _ _ _ _ _ _ κ _ a p ha hp φ ψ hφ hψ h1 h2 g
  have key : ∀ f : G → ℂ, Continuous f →
      MeasureTheory.Integrable (fun k => p k * f (g * a k)) κ := by
    intro f hf
    have hc : Continuous (fun k => p k * f (g * a k)) :=
      hp.mul (hf.comp (continuous_const.mul ha))
    exact (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable κ
  simp only [Pi.add_apply, mul_add]
  rw [MeasureTheory.integral_add (key φ hφ) (key ψ hψ), h1 g, h2 g]
end
