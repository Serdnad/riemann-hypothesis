module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem norm_orbit_apply (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (t : ℝ) (w : H) : ‖σ (NormedSpace.exp ((t : ℂ) • X)) w‖ = ‖w‖ :=
  hσ.2.1 _ (exp_smul_mem_UJset hX t) w

theorem hasDerivAt_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) ((actM E X v : D) : H)) t := by

  have key : (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) =
      fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) (v : H)) := by
    funext s
    have hc : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X) :=
      ((Commute.refl X).smul_left _).smul_right _
    have hsum : ((s : ℂ) • X) = (t : ℂ) • X + ((s - t : ℝ) : ℂ) • X := by
      rw [← add_smul]; congr 1; push_cast; ring
    rw [hsum, Matrix.exp_add_of_commute _ _ hc,
      hσ.1.2 _ (exp_smul_mem_UJset hX t) _ (exp_smul_mem_UJset hX (s - t))]
    rfl
  rw [key]
  have h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H))
      ((actM E X v : D) : H) (t - t) := by
    rw [sub_self]; exact hD.deriv X hX v
  have h1 := HasDerivAt.comp_sub_const t t h0
  exact ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1

theorem iteratedDeriv_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) ((((actM E X) ^ m) v : D) : H) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).deriv, pow_succ', Module.End.mul_apply]

theorem contDiff_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (N : ℕ) :
    ContDiff ℝ N (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_orbit hσ hD hX v m]
  exact fun t => (hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).differentiableAt

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem actM_mem_layer_succ (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {k : ℕ} {x : M} (hx : x ∈ layer ε E V k) :
    actM E X x ∈ layer ε E V (k + 1) := by
  unfold actM
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (apply_mem_layer_succ hE hV a b hx)

theorem sqrt_sub_le_add {y d : ℝ} (hy : 0 ≤ y) : √(y ^ 2 - d) ≤ y + √(max 0 (-d)) := by
  have hs := Real.sqrt_nonneg (max 0 (-d))
  have hs2 : √(max 0 (-d)) ^ 2 = max 0 (-d) := Real.sq_sqrt (le_max_left _ _)
  have hm : -d ≤ max 0 (-d) := le_max_right _ _
  rw [Real.sqrt_le_left (by positivity)]
  · nlinarith

theorem norm_actM_le {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k) :
    ‖actM E X x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
  set f : Fin n × Fin n → ℝ := fun p => ‖X p.1 p.2‖ with hf
  set g : Fin n × Fin n → ℝ := fun p => if ε p.1 ≠ ε p.2 then ‖E p.1 p.2 x‖ else 0 with hg
  have h1 : ‖actM E X x‖ ≤ ∑ p : Fin n × Fin n, f p * g p := by
    unfold actM
    rw [LinearMap.sum_apply, Fintype.sum_prod_type]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [LinearMap.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [LinearMap.smul_apply, norm_smul]
    by_cases hab : ε a = ε b
    · simp [hf, hg, hab, inP_apply_eq_zero hX hab]
    · simp [hf, hg, hab]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin n × Fin n)) f g
  have hfs : ∑ p : Fin n × Fin n, f p ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hgs : ∑ p : Fin n × Fin n, g p ^ 2 =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : ε a = ε b <;> simp [hg, hab]
  rw [hfs, hgs] at h2
  set y : ℝ := R + √2 * k with hy
  have hy0 : 0 ≤ y := by positivity
  have h3 : √(∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2) ≤
      (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
    calc _ ≤ √((y ^ 2 - d) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt (hR k x hx)
      _ ≤ √(max 0 (y ^ 2 - d)) * ‖x‖ := by
          rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (le_max_left _ _),
            Real.sqrt_sq (norm_nonneg x)]
          exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      _ ≤ (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          have := sqrt_sub_le_add (d := d) hy0
          rcases le_total 0 (y ^ 2 - d) with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h, Real.sqrt_zero]; positivity
  calc ‖actM E X x‖ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * ((R + √(max 0 (-d)) + √2 * k) * ‖x‖) :=
        mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem actM_pow_mem_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {k : ℕ} {x : M} (hx : x ∈ layer ε E V k)
    (m : ℕ) : ((actM E X) ^ m) x ∈ layer ε E V (k + m) := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact actM_mem_layer_succ hE hV hX ih

theorem norm_actM_pow_le (hE : IsGlRep E) (hV : IsKStableSub ε E V) {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k)
    (m : ℕ) :
    ‖((actM E X) ^ m) x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
      (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := norm_actM_le hR0 hR hX (k + m) (actM_pow_mem_layer hE hV hX hx m)
    have hc : 0 ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) := by
      positivity
    calc _ ≤ _ := h
      _ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) *
          (√(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
            (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = _ := by
          rw [Finset.prod_range_succ, pow_succ]
          push_cast
          ring

end Unitary

end ReciprocityTheory.ChartRestriction.DS
end
end
