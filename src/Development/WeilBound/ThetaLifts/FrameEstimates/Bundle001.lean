module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst.UMGS

open Filter Topology Function

theorem hasFDerivAt_of_partials {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) :
    ∀ (Φ : (Fin k → ℝ) → V) (D : Fin k → (Fin k → ℝ) → V), (∀ i, Continuous (D i)) →
      (∀ i t, HasDerivAt (fun s => Φ (update t i (t i + s))) (D i t) 0) →
      ∀ t, HasFDerivAt Φ (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i t)) t := by
  induction k with
  | zero =>
    intro Φ D _ _ t
    simpa using hasFDerivAt_of_subsingleton (𝕜 := ℝ) Φ t
  | succ k ih =>
    intro Φ D hc hd t
    have hcons : Continuous fun v : ℝ × (Fin k → ℝ) => (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ) := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp continuous_snd
    have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (t 0, Fin.tail t))
      (f := fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u))
      (f₁ := fun s u => (ContinuousLinearMap.id ℝ ℝ).smulRight (D 0 (Fin.cons s u)))
      (f₂ := fun s u => ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i.succ (Fin.cons s u)))
      (Eventually.of_forall fun v => by
        have h := hd 0 (Fin.cons v.1 v.2)
        simp only [Fin.update_cons_zero, Fin.cons_zero] at h
        have h0 : HasDerivAt (fun s => Φ (Fin.cons (v.1 + s) v.2)) (D 0 (Fin.cons v.1 v.2)) (v.1 - v.1) := by
          simpa using h
        have h1 := h0.comp_sub_const v.1 v.1
        simp only [add_sub_cancel] at h1
        exact h1.hasFDerivAt)
      (Eventually.of_forall fun v => ih (fun u => Φ (Fin.cons v.1 u)) (fun i u => D i.succ (Fin.cons v.1 u))
        (fun i => (hc i.succ).comp (hcons.comp (continuous_const.prodMk continuous_id)))
        (fun i u => by
          have h := hd i.succ (Fin.cons v.1 u)
          simpa only [Fin.cons_update, Fin.cons_succ] using h) v.2)
      (((StrongDual.smulRightL ℝ ℝ V (ContinuousLinearMap.id ℝ ℝ)).continuous.comp
        ((hc 0).comp hcons)).continuousAt)
      ((continuous_finsetSum Finset.univ fun i _ =>
        (StrongDual.smulRightL ℝ (Fin k → ℝ) V (ContinuousLinearMap.proj i)).continuous.comp
          ((hc i.succ).comp hcons)).continuousAt)
    let e : (Fin (k + 1) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
      (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.succ i))
    have h2 := HasFDerivAt.comp (f := e) t key.hasFDerivAt e.hasFDerivAt
    have h3 : (↿fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u)) ∘ e = Φ := by
      funext x
      exact congrArg Φ (Fin.cons_self_tail x)
    rw [h3] at h2
    refine h2.congr_fderiv ?_
    ext1 x
    simp [e, HasUncurry.uncurry, Fin.sum_univ_succ, Fin.cons_self_tail]

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {ι : Type} [Fintype ι]

def pr {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (t : Fin k → ℝ) : G :=
  (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod

omit [TopologicalSpace G] [ContinuousMul G] in
theorem pr_succ {k : ℕ} (γ : Fin (k + 1) → (Multiplicative ℝ →* G)) (t : Fin (k + 1) → ℝ) :
    pr γ t = γ 0 (Multiplicative.ofAdd (t 0)) * pr (fun i => γ i.succ) (fun i => t i.succ) := by
  simp [pr, List.ofFn_succ]

omit [TopologicalSpace G] [ContinuousMul G] in
theorem pr_zero (γ : Fin 0 → (Multiplicative ℝ →* G)) (t : Fin 0 → ℝ) : pr γ t = 1 := by
  simp [pr]

def Gn (m : ι → G →* A) (γ : Multiplicative ℝ →* G) (Y : ι → A) : Prop :=
  ∀ w (t : ℝ), m w (γ (Multiplicative.ofAdd t)) = NormedSpace.exp (t • Y w)

theorem continuous_pr (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, Continuous (γ i)) → Continuous (pr γ) := by
  induction k with
  | zero => intro γ _; exact continuous_const.congr fun t => (pr_zero γ t).symm
  | succ k ih =>
    intro γ hγ
    refine Continuous.congr ?_ fun t => (pr_succ γ t).symm
    exact ((hγ 0).comp (continuous_ofAdd.comp (continuous_apply 0))).mul
      ((ih _ fun i => hγ i.succ).comp (continuous_pi fun i => continuous_apply _))

theorem contDiff_exp_smul (Y : A) (n : WithTop ℕ∞) : ContDiff ℝ n fun t : ℝ => NormedSpace.exp (t • Y) := by
  have h : ContDiff ℝ n (NormedSpace.exp : A → A) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact h.comp (contDiff_id.smul contDiff_const)

theorem contDiff_tail (k : ℕ) (n : WithTop ℕ∞) : ContDiff ℝ n fun (t : Fin (k + 1) → ℝ) (i : Fin k) => t i.succ :=
  contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℝ) i.succ

omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι] in
theorem contDiff_pr (m : ι → G →* A) (n : WithTop ℕ∞) (w : ι) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G),
    (∀ i, ∃ Y, Gn m (γ i) Y) → ContDiff ℝ n (fun t => m w (pr γ t)) ∧ ContDiff ℝ n (fun t => m w (pr γ t)⁻¹) := by
  induction k with
  | zero => intro γ _; simp only [pr_zero]; exact ⟨contDiff_const, contDiff_const⟩
  | succ k ih =>
    intro γ hγ
    obtain ⟨h1, h2⟩ := ih (fun i => γ i.succ) fun i => hγ i.succ
    obtain ⟨Y, hY⟩ := hγ 0
    simp only [pr_succ, mul_inv_rev, map_mul, ← map_inv, ← ofAdd_neg, hY w]
    exact ⟨((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ (fun _ => ℝ) 0)).mul (h1.comp (contDiff_tail k n)),
      (h2.comp (contDiff_tail k n)).mul ((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ (fun _ => ℝ) 0).neg)⟩

def cj (x : G) (γ : Multiplicative ℝ →* G) : Multiplicative ℝ →* G := (MulAut.conj x⁻¹).toMonoidHom.comp γ

omit [TopologicalSpace G] [ContinuousMul G] in
theorem cj_apply (x : G) (γ : Multiplicative ℝ →* G) (s : Multiplicative ℝ) : cj x γ s = x⁻¹ * γ s * x := by
  simp [cj]

omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι] in
theorem Gn.cj {m : ι → G →* A} {γ : Multiplicative ℝ →* G} {Y : ι → A} (h : Gn m γ Y) (x : G) :
    Gn m (cj x γ) fun w => m w x⁻¹ * Y w * m w x := by
  intro w t
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let u : Aˣ := Units.map (m w) (toUnits x⁻¹)
  have h1 : (u : A) = m w x⁻¹ := rfl
  have h2 : ((u⁻¹ : Aˣ) : A) = m w x := by simp [u]
  have := NormedSpace.exp_units_conj u (t • Y w)
  rw [h1, h2] at this
  rw [cj_apply, map_mul, map_mul, h w t, ← this, mul_smul_comm, smul_mul_assoc]

omit [TopologicalSpace G] [ContinuousMul G] in
theorem exists_partial (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G)) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L)
    (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y) (n : WithTop ℕ∞) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, γ i ∈ L) →
    ∀ i, ∃ Z : (Fin k → ℝ) → ι → A, ContDiff ℝ n Z ∧ ∀ t, ∃ γ' ∈ L, Gn m γ' (Z t) ∧
      ∀ s, pr γ (update t i (t i + s)) = pr γ t * γ' (Multiplicative.ofAdd s) := by
  induction k with
  | zero => intro γ _ i; exact i.elim0
  | succ k ih =>
    intro γ hγ i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨Y, hY⟩ := hg _ (hγ 0)
      refine ⟨fun t w => m w (pr (fun i => γ i.succ) fun i => t i.succ)⁻¹ * Y w *
        m w (pr (fun i => γ i.succ) fun i => t i.succ), contDiff_pi.2 fun w => ?_, fun t =>
        ⟨_, hcj _ (hγ 0) _, hY.cj _, fun s => ?_⟩⟩
      · obtain ⟨h1, h2⟩ := contDiff_pr m n w k (fun i => γ i.succ) fun i => hg _ (hγ i.succ)
        exact ((h2.comp (contDiff_tail k n)).mul contDiff_const).mul (h1.comp (contDiff_tail k n))
      · simp only [pr_succ, cj_apply, update_self, ne_eq, Fin.succ_ne_zero, not_false_eq_true, update_of_ne,
          ofAdd_add, map_mul]
        group
    · obtain ⟨Z, hZ, h⟩ := ih (fun i => γ i.succ) (fun i => hγ i.succ) j
      refine ⟨fun t => Z fun i => t i.succ, hZ.comp (contDiff_tail k n), fun t => ?_⟩
      obtain ⟨γ', h1, h2, h3⟩ := h fun i => t i.succ
      refine ⟨γ', h1, h2, fun s => ?_⟩
      have e : (fun i : Fin k => update t j.succ (t j.succ + s) i.succ) =
          update (fun i : Fin k => t i.succ) j (t j.succ + s) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp
        · simp [hi]
      rw [pr_succ, pr_succ, e, h3, update_of_ne (Fin.succ_ne_zero j).symm, mul_assoc]

theorem contDiff_comp_pr [FiniteDimensional ℝ A] (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G))
    (hc : ∀ γ ∈ L, Continuous γ) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L) (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y)
    {r : ℕ} (β : Fin r → (Multiplicative ℝ →* G)) (c : Fin r → (ι → A) →ₗ[ℝ] ℝ) (hβ : ∀ j, β j ∈ L)
    (hl : ∀ (f : G → ℂ) (f' : Fin r → G → ℂ), (∀ j, Continuous (f' j) ∧
      ∀ h, HasDerivAt (fun t : ℝ => f (h * β j (Multiplicative.ofAdd t))) (f' j h) 0) → ∀ γ ∈ L, ∀ Y, Gn m γ Y →
      ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ j, (c j Y : ℂ) * f' j h) 0)
    (S : Set (G → ℂ)) (hS : ∀ f ∈ S, Continuous f ∧
      ∀ γ ∈ L, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0)
    {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (hγ : ∀ i, γ i ∈ L) (g : G) (n : ℕ) :
    ∀ f ∈ S, ContDiff ℝ n fun t => f (g * pr γ t) := by
  induction n with
  | zero =>
    intro f hf
    exact contDiff_zero.2 ((hS f hf).1.comp (continuous_const.mul (continuous_pr k γ fun i => hc _ (hγ i))))
  | succ n ih =>
    intro f hf
    choose f' hf'S hf' using fun j => (hS f hf).2 _ (hβ j)
    choose Z hZ hZ' using exists_partial m L hcj hg n k γ hγ
    have hD : ∀ i, ContDiff ℝ n fun t => ∑ j, (c j (Z i t) : ℂ) * f' j (g * pr γ t) := fun i =>
      ContDiff.sum fun j _ => (Complex.ofRealCLM.contDiff.comp
        ((LinearMap.toContinuousLinearMap (c j)).contDiff.comp (hZ i))).mul (ih _ (hf'S j))
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ?_, hasFDerivAt_of_partials k _ _ (fun i => (hD i).continuous) fun i t => ?_⟩
    · exact ContDiff.sum fun i _ =>
        (StrongDual.smulRightL ℝ (Fin k → ℝ) ℂ (ContinuousLinearMap.proj i)).contDiff.comp (hD i)
    · obtain ⟨γ', h1, h2, h3⟩ := hZ' i t
      simp only [h3, ← mul_assoc]
      exact hl f f' (fun j => ⟨(hS _ (hf'S j)).1, hf' j⟩) γ' h1 _ h2 _

end PositivityTheory.ThKEst.UMGS

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst.RealFourierCoefficientBounds

open MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def q (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (M N : ℕ) : Seminorm ℂ (SchwartzMap V ℂ) :=
  (Finset.Iic (M, N)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2

theorem q_cont (M N : ℕ) : Continuous (q V M N) := by
  unfold q
  exact Seminorm.continuous_finsetSup (E := SchwartzMap V ℂ) (s := Finset.Iic (M, N))
    fun m _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm m

def H (f₁ f₂ : SchwartzMap V ℂ) (x : V) (u : V) : ℂ := f₁ (u + x) * (starRingEnd ℂ) (f₂ u)

theorem conj_smooth (f : SchwartzMap V ℂ) : ContDiff ℝ ∞ fun u => (starRingEnd ℂ) (f u) :=
  Complex.conjCLE.contDiff.comp (f.smooth ⊤)

theorem shift_smooth (f : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ fun u => f (u + x) :=
  (f.smooth ⊤).comp (contDiff_id.add contDiff_const)

theorem H_smooth (f₁ f₂ : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ (H f₁ f₂ x) :=
  (shift_smooth f₁ x).mul (conj_smooth f₂)

omit [InnerProductSpace ℝ V] in
theorem peetre (x u : V) : 1 + ‖x‖ ≤ (1 + ‖u + x‖) * (1 + ‖u‖) := by
  have h : ‖x‖ ≤ ‖u + x‖ + ‖u‖ := by simpa using norm_sub_le (u + x) u
  nlinarith [norm_nonneg (u + x), norm_nonneg u, mul_nonneg (norm_nonneg (u + x)) (norm_nonneg u)]

theorem H_bound (N D : ℕ) (f₁ f₂ : SchwartzMap V ℂ) (x u : V) {j : ℕ} (hj : j ≤ N) :
    (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D * ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      2 ^ N * ((2 ^ (N + D) * q V (N + D) N f₁) * (2 ^ (N + D) * q V (N + D) N f₂)) := by
  set A := 2 ^ (N + D) * q V (N + D) N f₁ with hA
  set B := 2 ^ (N + D) * q V (N + D) N f₂ with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (shift_smooth f₁ x) (conj_smooth f₂) u (n := j)
    (by exact_mod_cast le_top)
  have key : ∀ i ∈ Finset.range (j + 1), (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D *
      ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u => f₁ (u + x)) u‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖) ≤ (j.choose i : ℝ) * (A * B) := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖ = ‖iteratedFDeriv ℝ (j - i) f₂ u‖ :=
      Complex.conjLIE.norm_iteratedFDeriv_comp_left f₂ u (j - i)
    rw [e1, iteratedFDeriv_comp_add_right (f := f₁)]
    have b1 : (1 + ‖u + x‖) ^ N * ‖iteratedFDeriv ℝ i f₁ (u + x)‖ ≤ A :=
      one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N + D, N)) (by simp) (by simp; omega) f₁ (u + x)
    have b2 : (1 + ‖u‖) ^ (N + D) * ‖iteratedFDeriv ℝ (j - i) f₂ u‖ ≤ B :=
      one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N + D, N)) (by simp) (by simp; omega) f₂ u
    have b3 : (1 + ‖x‖) ^ N ≤ (1 + ‖u + x‖) ^ N * (1 + ‖u‖) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (peetre x u) N
    calc _ ≤ ((1 + ‖u + x‖) ^ N * (1 + ‖u‖) ^ N) * (1 + ‖u‖) ^ D *
          ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f₁ (u + x)‖ * ‖iteratedFDeriv ℝ (j - i) f₂ u‖) := by
          gcongr
      _ = (j.choose i : ℝ) * (((1 + ‖u + x‖) ^ N * ‖iteratedFDeriv ℝ i f₁ (u + x)‖) *
          ((1 + ‖u‖) ^ (N + D) * ‖iteratedFDeriv ℝ (j - i) f₂ u‖)) := by ring
      _ ≤ _ := by gcongr
  calc _ ≤ (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D * ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u => f₁ (u + x)) u‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * B) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum key
    _ = 2 ^ j * (A * B) := by
        rw [← Finset.sum_mul]; congr 1; exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ N * (A * B) := by gcongr; norm_num

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem wt_int : Integrable fun u : V => ((1 + ‖u‖) ^ (Module.finrank ℝ V + 1))⁻¹ := by
  have h := integrable_one_add_norm (E := V) (μ := volume) (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ))
    (by push_cast; linarith)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem H_int (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x : V) (j : ℕ), j ≤ N →
    Integrable (fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖) ∧
    (1 + ‖x‖) ^ N * ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by
  set D := Module.finrank ℝ V + 1 with hD
  refine ⟨2 ^ N * 2 ^ (N + D) * 2 ^ (N + D) * ∫ u : V, ((1 + ‖u‖) ^ D)⁻¹, ?_, fun f₁ f₂ x j hj => ?_⟩
  · have : 0 ≤ ∫ u : V, ((1 + ‖u‖) ^ D)⁻¹ := integral_nonneg fun u => by positivity
    positivity
  set C := 2 ^ N * ((2 ^ (N + D) * q V (N + D) N f₁) * (2 ^ (N + D) * q V (N + D) N f₂)) with hC
  have hb : ∀ u, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤ C * ((1 + ‖u‖) ^ D)⁻¹ := by
    intro u
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have := H_bound N D f₁ f₂ x u hj
    linarith [mul_right_comm ((1 + ‖x‖) ^ N) ((1 + ‖u‖) ^ D) ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖]
  have hw : Integrable fun u : V => C * ((1 + ‖u‖) ^ D)⁻¹ := (wt_int (V := V)).const_mul C
  have hc : Continuous fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ :=
    ((H_smooth f₁ f₂ x).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hi : Integrable fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ := by
    refine hw.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_norm]
    refine le_trans ?_ (hb u)
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg x]))
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  refine (integral_mono (hi.const_mul _) hw hb).trans (le_of_eq ?_)
  rw [integral_const_mul, hC]; ring

theorem fourier_bound (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x w : V),
    ‖𝓕 (H f₁ f₂ x) w‖ * (1 + ‖x‖ + ‖w‖) ^ N ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by
  obtain ⟨K, hK, h⟩ := H_int (V := V) N
  refine ⟨2 ^ N * (2 * (2 ^ N * ((N + 1) * K))), by positivity, fun f₁ f₂ x w => ?_⟩
  set Q := q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have step : ∀ n ≤ N, (1 + ‖x‖) ^ N * (‖w‖ ^ n * ‖𝓕 (H f₁ f₂ x) w‖) ≤ 2 ^ N * ((N + 1) * K) * Q := by
    intro n hn
    have h1 := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := (N : ℕ∞)) (f := H f₁ f₂ x)
      ((H_smooth f₁ f₂ x).of_le (by exact_mod_cast le_top))
      (fun k m hk hm => by
        have hk0 : k = 0 := by simpa using hk
        subst hk0
        simpa using (h f₁ f₂ x m (by exact_mod_cast hm)).1)
      (k := 0) (n := n) (by simp) (by exact_mod_cast hn) w
    simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
      Finset.range_one, Finset.singleton_product, Finset.sum_map, Function.Embedding.sectR_apply] at h1
    calc _ ≤ (1 + ‖x‖) ^ N * (2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), (1 + ‖x‖) ^ N * ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ := by
          rw [← Finset.mul_sum]; ring
      _ ≤ 2 ^ n * ∑ _j ∈ Finset.range (n + 1), K * Q := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
          exact (h f₁ f₂ x j ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hn)).2
      _ = 2 ^ n * ((n + 1) * K) * Q := by simp; ring
      _ ≤ _ := by gcongr; norm_num
  have s0 := step 0 (Nat.zero_le _)
  have sN := step N le_rfl
  have e1 : (1 + ‖x‖ + ‖w‖) ^ N ≤ (1 + ‖x‖) ^ N * (1 + ‖w‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg w)]) N
  have e2 : (1 + ‖w‖) ^ N ≤ 2 ^ N * (1 + ‖w‖ ^ N) := by
    have := add_pow_le (zero_le_one' ℝ) (norm_nonneg w) N
    rw [one_pow] at this
    refine this.trans ?_
    gcongr
    · norm_num
    · omega
  calc _ ≤ ‖𝓕 (H f₁ f₂ x) w‖ * ((1 + ‖x‖) ^ N * (2 ^ N * (1 + ‖w‖ ^ N))) := by
        gcongr
        exact e1.trans (by gcongr)
    _ = 2 ^ N * ((1 + ‖x‖) ^ N * (‖w‖ ^ 0 * ‖𝓕 (H f₁ f₂ x) w‖) +
          (1 + ‖x‖) ^ N * (‖w‖ ^ N * ‖𝓕 (H f₁ f₂ x) w‖)) := by ring
    _ ≤ 2 ^ N * (2 ^ N * ((N + 1) * K) * Q + 2 ^ N * ((N + 1) * K) * Q) := by gcongr
    _ = _ := by ring

theorem main (N : ℕ) : ∃ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x y : V),
    ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)‖ *
      (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂ := by
  obtain ⟨K, hK, h⟩ := fourier_bound (V := V) N
  let c : NNReal := ⟨Real.sqrt K, Real.sqrt_nonneg K⟩
  refine ⟨c • q V (N + (Module.finrank ℝ V + 1)) N, ?_, fun f₁ f₂ x y => ?_⟩
  · exact (q_cont _ _).const_smul c
  have e : (∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) *
      (starRingEnd ℂ) (f₂ u)) = 𝓕 (H f₁ f₂ x) (-y) := by
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [H, inner_neg_right, smul_eq_mul, mul_assoc]
    congr 2
    push_cast; ring
  have h1 := h f₁ f₂ x (-y)
  rw [norm_neg] at h1
  rw [e]
  refine h1.trans (le_of_eq ?_)
  have hc : (c : ℝ) * c = K := Real.mul_self_sqrt hK
  simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  rw [← hc]; ring

end PositivityTheory.ThKEst.RealFourierCoefficientBounds

end
end
