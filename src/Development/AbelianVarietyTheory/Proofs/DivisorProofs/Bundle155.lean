module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section
open scoped ContDiff
open Set MeasureTheory

namespace GlobalTheory.ParamIntCut

theorem hasDerivAt_snd {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F)) (s y : ℝ) :
    HasDerivAt (F s) (fderiv ℝ (Function.uncurry F) (s, y) (0, 1)) y := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (s, y)) (s, y) :=
    (hF.differentiable one_ne_zero (s, y)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) y :=
    (hasDerivAt_const y s).prodMk (hasDerivAt_id y)
  exact h1.comp_hasDerivAt y h2

theorem hasDerivAt_intervalIntegral {F : ℝ → ℝ → ℝ} (a b : ℝ)
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ s in a..b, F s y)
      (∫ s in a..b, fderiv ℝ (Function.uncurry F) (s, y₀) (0, 1)) y₀ := by
  set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
  have hPc : Continuous (Function.uncurry P) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hFc : Continuous (Function.uncurry F) := hF.continuous
  have hsec : ∀ (G : ℝ → ℝ → ℝ), Continuous (Function.uncurry G) → ∀ y, Continuous (fun s => G s y) :=
    fun G hG y => hG.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ (uIcc a b) ×ˢ (Metric.closedBall y₀ 1), ‖Function.uncurry P p‖ ≤ C :=
    (isCompact_uIcc.prod (isCompact_closedBall y₀ 1)).exists_bound_of_continuousOn hPc.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := volume)
    (a := a) (b := b) (F := fun y s => F s y) (F' := fun y s => P s y) (x₀ := y₀)
    (bound := fun _ => C) (s := Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ one_pos)
    (Filter.Eventually.of_forall fun y => (hsec F hFc y).aestronglyMeasurable)
    ((hsec F hFc y₀).intervalIntegrable _ _)
    ((hsec P hPc y₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht y hy =>
      hC (t, y) ⟨uIoc_subset_uIcc ht, Metric.ball_subset_closedBall hy⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ y _ => hasDerivAt_snd hF t y)
  exact key.2

theorem contDiff_nat_intervalIntegral (a b : ℝ) :
    ∀ (n : ℕ) (F : ℝ → ℝ → ℝ), ContDiff ℝ ∞ (Function.uncurry F) →
      ContDiff ℝ n (fun y => ∫ s in a..b, F s y)
  | 0, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun y => (hasDerivAt_intervalIntegral a b h1 y).continuousAt
  | n + 1, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
    have hPs : ContDiff ℝ ∞ (Function.uncurry P) :=
      (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hc : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hc, contDiff_succ_iff_deriv]
    refine ⟨fun y => (hasDerivAt_intervalIntegral a b h1 y).differentiableAt, by simp, ?_⟩
    have hd : deriv (fun y => ∫ s in a..b, F s y) = fun y => ∫ s in a..b, P s y :=
      funext fun y => (hasDerivAt_intervalIntegral a b h1 y).deriv
    rw [hd]
    exact contDiff_nat_intervalIntegral a b n P hPs

end GlobalTheory.ParamIntCut

namespace GlobalTheory.PsCo.Pc1

theorem isCutFn_intervalIntegral_and_deriv :
    ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) →
      (∃ R : ℝ, ∀ s ∈ Set.uIcc a b, ∀ y, R ≤ y → F s y = 0) →
      GlobalTheory.PsCo.Pc1.IsCutFn (fun y => ∫ s in a..b, F s y) ∧
        ∀ y, deriv (fun y => ∫ s in a..b, F s y) y = ∫ s in a..b, deriv (F s) y := by
  intro F a b hF ⟨R, hR⟩
  have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
  refine ⟨⟨contDiff_infty.2 fun n => GlobalTheory.ParamIntCut.contDiff_nat_intervalIntegral a b n F hF, R, fun y hy => ?_⟩,
    fun y => ?_⟩
  · show ∫ s in a..b, F s y = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => hR s hs y hy)]
    simp
  · rw [(GlobalTheory.ParamIntCut.hasDerivAt_intervalIntegral a b h1 y).deriv]
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact ((GlobalTheory.ParamIntCut.hasDerivAt_snd h1 s y).deriv).symm

end GlobalTheory.PsCo.Pc1
end
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

noncomputable section

namespace GlobalTheory.PsCo.HomotDeriv

theorem ev_rP {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by

  simp only [rP, rM, map_sum, map_mul, ev, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem hasDerivAt_scale (G : ℝ → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (k : ℕ) (r t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => iteratedDeriv k (fun y => G (s * y)) r)
      (t⁻¹ * (k * iteratedDeriv k (fun y => G (t * y)) r + r * iteratedDeriv (k + 1) (fun y => G (t * y)) r)) t := by
  have hc : ∀ m : ℕ, ContDiff ℝ m G := fun m => hG.of_le (by exact_mod_cast le_top)
  have e : ∀ (m : ℕ) (s : ℝ), iteratedDeriv m (fun y => G (s * y)) r = s ^ m * iteratedDeriv m G (s * r) :=
    fun m s => congrFun (iteratedDeriv_comp_const_mul (hc m) s) r
  simp only [e]
  have hD : HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G (t * r)) (t * r) := by
    rw [iteratedDeriv_succ]
    exact ((hc (k + 1)).differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => s * r) r t := by simpa using (hasDerivAt_id t).mul_const r
  have h2 : HasDerivAt (fun s : ℝ => s ^ k * iteratedDeriv k G (s * r))
      (k * t ^ (k - 1) * iteratedDeriv k G (t * r) + t ^ k * (iteratedDeriv (k + 1) G (t * r) * r)) t :=
    by
    have h3 := (hasDerivAt_pow k t).mul (hD.comp t h1)
    exact h3
  refine h2.congr_deriv ?_
  rcases k with _ | k
  · simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, pow_one]
    field_simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

theorem sum_shift (N : ℕ) (a e : ℕ → ℂ) (r : ℂ) (he : e (N + 1) = 0) :
    ∑ k ∈ Finset.range (N + 1), ((k : ℂ) * a k + r * a (k + 1)) * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1) + r * e k) := by
  have h1 : ∑ k ∈ Finset.range (N + 1), (k : ℂ) * a k * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1)) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), he]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  simp only [add_mul (_ * a _), mul_add (a _), Finset.sum_add_distrib, h1]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_prev {n : ℕ} (g : Mat n) (N : ℕ) (a : ℕ → ℂ) (q : ℕ → Poly n) (hq : q N = 0) (R : ℂ) :
    ∑ k ∈ Finset.range (N + 1), a (k + 1) * (R * ev g (prev q k)) =
      ∑ k ∈ Finset.range (N + 1), a (k + 1 + 1) * (R * ev g (q k)) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), hq]
  simp [prev]

theorem famF_hasDerivAt : ∀ {n : ℕ} (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → GlobalTheory.PsCo.Pc1.Poly n) (q : GlobalTheory.PsCo.Pc1.Mode ε → ℕ → GlobalTheory.PsCo.Pc1.Poly n), ContDiff ℝ (⊤ : ℕ∞) G → GlobalTheory.PsCo.Pc1.IsKoszul ε p q → ∀ t : ℝ, 0 < t → ∀ g : GlobalTheory.PsCo.Pc1.Mat n, HasDerivAt (fun s : ℝ => GlobalTheory.PsCo.Pc1.famF ε G p s g) (((t⁻¹ : ℝ) : ℂ) * ∑ x : GlobalTheory.PsCo.Pc1.Mode ε, ∑ j ∈ Finset.range (GlobalTheory.PsCo.Pc1.nMode ε + 1), GlobalTheory.PsCo.Pc1.adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g) t := by
  intro n ε G p q hG hK t ht g
  obtain ⟨hrec, hp, hq⟩ := hK
  let a : ℕ → ℂ := fun j => ((iteratedDeriv j (fun y => G (t * y)) (rM ε g) : ℝ) : ℂ)
  have hd : ∀ k ∈ Finset.range (nMode ε + 1),
      HasDerivAt (fun s : ℝ => bas ε (iteratedDeriv k fun x => G (s * x)) (p k) g)
        (((t⁻¹ : ℝ) : ℂ) * (((k : ℂ) * a k + (rM ε g : ℂ) * a (k + 1)) * ev g (p k))) t := by
    intro k _
    refine (((hasDerivAt_scale G hG k (rM ε g) t ht.ne').ofReal_comp).mul_const (ev g (p k))).congr_deriv ?_
    simp only [a]
    push_cast
    ring
  refine (HasDerivAt.fun_sum hd).congr_deriv ?_
  rw [← Finset.mul_sum]
  congr 1
  have hA : ∀ (x : Mode ε) (j : ℕ),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g =
        a (j + 1) * ev g (dM ε x (q x j)) + a (j + 1 + 1) * (ev g (dM ε x (rP ε)) * ev g (q x j)) := by
    intro x j
    simp only [adBas, bas, dM, ← iteratedDeriv_succ, map_mul, a]
    ring
  have hR : ∀ j : ℕ, ((j : ℂ) + 1) * ev g (p (j + 1)) + (rM ε g : ℂ) * ev g (p j) =
      ∑ x, (ev g (dM ε x (q x j)) + ev g (dM ε x (rP ε)) * ev g (prev (q x) j)) := by
    intro j
    have := congrArg (ev g) (hrec j)

    simpa only [map_sum, map_add (f := _), map_mul, ev_rP, map_natCast, map_one] using this
  rw [sum_shift (nMode ε) a (fun k => ev g (p k)) (rM ε g : ℂ) (by simp [hp (nMode ε + 1) (Nat.lt_succ_self _)])]
  simp only [hA, hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_prev g (nMode ε) a (q x) (hq x _ le_rfl)]

end GlobalTheory.PsCo.HomotDeriv
end
end

section

open GlobalTheory.LKTorus

namespace GlobalTheory

lemma LKTorus.rat_int_of_isIntegral {q : ℚ} (h : IsIntegral ℤ q) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by simpa using hn⟩

theorem LKTorus.simT_integral_finite (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L)
    (hc : ∀ (τ : L →+* ℂ) (x : L), τ (c x) = (starRingEnd ℂ) (τ x)) :
    {x : Lˣ | x ∈ simT ℚ c ∧ IsIntegral ℤ (x : L) ∧ IsIntegral ℤ ((x⁻¹ : Lˣ) : L)}.Finite := by
  have hF := NumberField.Embeddings.finite_of_norm_le L ℂ 1
  refine (hF.preimage (Set.injOn_of_injective Units.val_injective)).subset ?_
  rintro x ⟨⟨t, ht⟩, hx, hxi⟩
  have hinv : x⁻¹ ∈ simT ℚ c := (simT ℚ c).inv_mem ⟨t, ht⟩
  obtain ⟨t', ht'⟩ := hinv
  have hcint : ∀ y : L, IsIntegral ℤ y → IsIntegral ℤ (c y) := fun y hy =>
    hy.map (c.toRingHom.toIntAlgHom)
  have hinj : Function.Injective (algebraMap ℚ L) := (algebraMap ℚ L).injective
  have htI : IsIntegral ℤ ((t : ℚ)) := by
    rw [← isIntegral_algebraMap_iff (B := L), ← ht]
    exact hx.mul (hcint _ hx)
  have ht'I : IsIntegral ℤ ((t' : ℚ)) := by
    rw [← isIntegral_algebraMap_iff (B := L), ← ht']
    exact hxi.mul (hcint _ hxi)
  obtain ⟨n, hn⟩ := LKTorus.rat_int_of_isIntegral htI
  obtain ⟨m, hm⟩ := LKTorus.rat_int_of_isIntegral ht'I
  have hprod : (t : ℚ) * t' = 1 := by
    apply hinj
    rw [map_mul, ← ht, ← ht', map_one]
    have h1 : ((x⁻¹ : Lˣ) : L) * (x : L) = 1 := by simp
    calc (x : L) * c x * (((x⁻¹ : Lˣ) : L) * c ((x⁻¹ : Lˣ) : L))
        = (((x⁻¹ : Lˣ) : L) * (x : L)) * c (((x⁻¹ : Lˣ) : L) * (x : L)) := by rw [map_mul]; ring
      _ = 1 := by rw [h1, map_one, one_mul]
  have hnm : n * m = 1 := by
    have : ((n * m : ℤ) : ℚ) = 1 := by push_cast; rw [hn, hm, hprod]
    exact_mod_cast this
  refine ⟨hx, fun τ => ?_⟩
  have hτ : ((‖τ x‖ ^ 2 : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
    have e := congrArg τ ht
    rw [map_mul, hc, Complex.mul_conj, Complex.normSq_eq_norm_sq, eq_ratCast, map_ratCast, ← hn] at e
    rw [e]; push_cast; rfl
  have hτ' : ‖τ x‖ ^ 2 = (n : ℝ) := by exact_mod_cast hτ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h | h
  · rw [h] at hτ'
    have h0 : 0 ≤ ‖τ x‖ := norm_nonneg _
    push_cast at hτ'
    nlinarith
  · rw [h] at hτ'
    push_cast at hτ'
    nlinarith [sq_nonneg ‖τ x‖]

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh

theorem pull1_restrict_surjective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a) → Function.Surjective (CoefMap.restrict F G).pull1 := by
  intro R _ C _ C' _ F G hsep hglue hvan c
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
  have hb : ∀ T : C, ∃ b : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), b t' (u ≫ G.map a) - mp F (G.map a) (b t u) = y.1 t t' a := fun T ↦
    hvan T (fun t t' _ a ↦ y.1 t t' a) fun t t' t'' _ a a' ↦ Z1.comp y a a'
  choose b hb using hb
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t u, mp F u x = b T t (φ ≫ u) - b T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := hb T t t' (φ ≫ u) a
    have k2 := hb T' t t' u a
    rw [Category.assoc] at k1
    rw [map_sub]
    linear_combination k1 - k2
  choose x hx using hx
  have hxc : x ∈ Z1 F := fun T T' T'' φ ψ ↦ sub_eq_zero.1 (hsep T'' _ fun t u ↦ by
    have k1 := hx T T'' (φ ≫ ψ) t u
    have k2 := hx T T' φ t (ψ ≫ u)
    have k3 := hx T' T'' ψ t u
    rw [mp_comp] at k2
    simp only [map_sub, map_add (f := _), Category.assoc] at k1 k2 ⊢
    linear_combination k1 - k2 - k3)
  refine ⟨H1.mk F ⟨x, hxc⟩, ?_⟩
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
  refine ⟨fun t ↦ -b (G.obj t) t (𝟙 _), ?_⟩
  funext t t' a
  have k1 := hx _ _ (G.map a) t' (𝟙 _)
  have k2 := hb (G.obj t) t t' (𝟙 _) a
  rw [mp_id, Category.comp_id] at k1
  rw [Category.id_comp] at k2
  show -b _ t' (𝟙 _) - mp F (G.map a) (-b _ t (𝟙 _)) = x _ _ (G.map a) - (show F.obj (G.obj t') from y.1 t t' a)
  rw [map_neg]
  linear_combination -k1 - k2

end GlobalTheory.CatCoh
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh

theorem pull2_restrict_injective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → Function.Injective (CoefMap.restrict F G).pull2 := by
  intro R _ C _ C' _ F G hsep hglue hvan
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
  obtain ⟨y0, hy0⟩ := hc
  obtain ⟨y, hy'⟩ : ∃ y : ∀ t t' (_ : t ⟶ t'), F.obj (G.obj t'), ∀ t t' t'' (a : t ⟶ t')
      (b : t' ⟶ t''), mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b
        = z.1 _ _ _ (G.map a) (G.map b) := ⟨y0, fun t t' t'' a b ↦
    congrFun (congrFun (congrFun (congrFun (congrFun hy0 t) t') t'') a) b⟩
  have hg : ∀ T : C, ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u)
        = z.1 _ _ _ u (G.map a) - y t t' a := fun T ↦
    hvan T (fun t t' u a ↦ z.1 _ _ _ u (G.map a) - y t t' a) fun t t' t'' u a b ↦ by
      have k1 := z.2 u (G.map a) (G.map b)
      have k2 := hy' t t' t'' a b
      rw [Functor.map_comp]
      simp only [map_sub]
      linear_combination k2 - k1
  choose g hg using hg
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t (u : T' ⟶ G.obj t),
      mp F u x = z.1 _ _ _ φ u - g T t (φ ≫ u) + g T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := z.2 φ u (G.map a)
    have k2 := hg T t t' (φ ≫ u) a
    have k3 := hg T' t t' u a
    rw [Category.assoc] at k2
    simp only [map_sub, map_add (f := _)]
    linear_combination -k1 - k2 + k3
  choose x hx using hx
  refine H2.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' T'' φ ψ
  refine sub_eq_zero.1 (hsep T'' _ fun t u ↦ ?_)
  have k1 := z.2 φ ψ u
  have k2 := hx T T' φ t (ψ ≫ u)
  have k3 := hx T T'' (φ ≫ ψ) t u
  have k4 := hx T' T'' ψ t u
  rw [mp_comp] at k2
  rw [d1_apply]
  simp only [map_sub, map_add (f := _), Category.assoc] at k2 k3 ⊢
  linear_combination k2 - k3 + k4 - k1

end GlobalTheory.CatCoh
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem pull2_surjective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → Function.Surjective (CoefMap.restrict F G).pull2 := by
  intro R _ C _ C' _ F G sep glue van1 van2 c
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ c
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ t t' t'' : C', (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t''),
      ∀ t t' t'' a b, Y t t' t'' a b = y.1 t t' t'' a b := ⟨y.1, fun _ _ _ _ _ ↦ rfl⟩
  have hy : ∀ t t' t'' t''' (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''),
      mp F (G.map c) (Y t t' t'' a b) + Y t t'' t''' (a ≫ b) c =
        Y t t' t''' a (b ≫ c) + Y t' t'' t''' b c := by
    intro t t' t'' t''' a b c
    simp only [hY]
    exact y.2 a b c
  choose h hh using fun T : C ↦ van2 T (fun t t' t'' _ a b ↦ Y t t' t'' a b)
    (fun t t' t'' t''' _ a b c ↦ hy t t' t'' t''' a b c)
  choose m hm using fun (T T' : C) (φ : T ⟶ T') ↦
    van1 T' (fun t t' u a ↦ h T t t' (φ ≫ u) a - h T' t t' u a) (fun t t' t'' u a b ↦ by
      have k1 := hh T t t' t'' (φ ≫ u) a b
      have k2 := hh T' t t' t'' u a b
      simp only [map_sub, Category.assoc] at k1 ⊢
      linear_combination k2 - k1)
  choose x hx using fun (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') ↦
    glue T'' (fun t u ↦ m T T' φ t (ψ ≫ u) + m T' T'' ψ t u - m T T'' (φ ≫ ψ) t u)
      (fun t t' u a ↦ by
        have k1 := hm T T' φ t t' (ψ ≫ u) a
        have k2 := hm T' T'' ψ t t' u a
        have k3 := hm T T'' (φ ≫ ψ) t t' u a
        simp only [map_sub, map_add (f := _), Category.assoc] at k1 k3 ⊢
        linear_combination k1 + k2 - k3)
  refine ⟨H2.mk F ⟨fun T T' T'' φ ψ ↦ x T T' T'' φ ψ,
    fun T T' T'' T''' φ ψ χ ↦ sub_eq_zero.1 (sep T''' _ fun t u ↦ ?_)⟩, ?_⟩
  · have k1 := hx _ _ _ φ ψ t (χ ≫ u)
    have k2 := hx _ _ _ (φ ≫ ψ) χ t u
    have k3 := hx _ _ _ φ (ψ ≫ χ) t u
    have k4 := hx _ _ _ ψ χ t u
    simp only [map_sub, map_add (f := _), Category.assoc, mp_comp] at k1 k2 k3 k4 ⊢
    linear_combination k1 + k2 - k3 - k4
  · rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
    refine ⟨fun t t' a ↦ m _ _ (G.map a) t' (𝟙 _) - h _ t t' (𝟙 _) a, ?_⟩
    funext t t' t'' a b
    simp only [Pi.sub_apply]
    rw [← hY]
    have k1 := hx _ _ _ (G.map a) (G.map b) t'' (𝟙 _)
    have k2 := hm _ _ (G.map a) t' t'' (𝟙 _) b
    have k3 := hh _ t t' t'' (𝟙 _) a b
    simp only [mp_id, Category.id_comp, Category.comp_id] at k1 k2 k3
    change mp F (G.map b) (m _ _ (G.map a) t' (𝟙 _) - h _ t t' (𝟙 _) a) -
        (m _ _ (G.map (a ≫ b)) t'' (𝟙 _) - h _ t t'' (𝟙 _) (a ≫ b)) +
        (m _ _ (G.map b) t'' (𝟙 _) - h _ t' t'' (𝟙 _) b) =
      x _ _ _ (G.map a) (G.map b) - Y t t' t'' a b
    rw [G.map_comp]
    simp only [map_sub]
    linear_combination -k1 - k2 - k3

end GlobalTheory.CatCoh.Desc
end

section

open IsDedekindDomain

namespace GlobalTheory.LKTrip

theorem AfP.continuous_restr (p : ℕ) : Continuous (AfP.restr p) :=
  RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ) Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ RingHom.id _) (Filter.Eventually.of_forall fun _ ↦ Set.mapsTo_id _)
    (fun _ ↦ continuous_id)

end GlobalTheory.LKTrip
end
