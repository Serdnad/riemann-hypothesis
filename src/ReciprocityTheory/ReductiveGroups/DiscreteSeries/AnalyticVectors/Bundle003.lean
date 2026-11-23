module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.WeightBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem casimir_apply_eq_casimirK_add (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (x : M) :
    casimir E x = casimirK ε E x +
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), E a b (E b a x) := by
  simp only [casimir, casimirK, LinearMap.sum_apply, Module.End.mul_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun b => ε b = ε a)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun b _ => ?_) fun _ _ => rfl
  exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩

theorem sum_nc_swap (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), f b a =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), f a b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε a = ε b
  · simp [h]
  · simp [h, Ne.symm h]

theorem re_inner_casimir_eq (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hU : IsInfUnitary ε E) (x : M) :
    RCLike.re (inner ℂ (casimir E x) x) = RCLike.re (inner ℂ (casimirK ε E x) x) -
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 := by

  rw [casimir_apply_eq_casimirK_add ε E x, inner_add_left, map_add (f := _), sum_inner, map_sum]
  have key : ∀ a, RCLike.re (inner ℂ (∑ b ∈ univ.filter (fun b => ε a ≠ ε b), E a b (E b a x)) x) =
      -∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E b a x‖ ^ 2 := by
    intro a

    rw [sum_inner, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hab : ε a ≠ ε b := (Finset.mem_filter.1 hb).2
    rw [hU a b (E b a x) x, adjSign, if_neg hab, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  simp only [key, Finset.sum_neg_distrib]
  rw [sum_nc_swap ε (fun a b => ‖E a b x‖ ^ 2)]
  ring

theorem re_inner_smul_self (c : ℝ) (x : M) :
    RCLike.re (inner ℂ ((c : ℂ) • x) x) = c * ‖x‖ ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

private theorem casimir_eq_smul_on_layer {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) {V : Submodule ℂ M} {c : ℝ} (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∀ k : ℕ, ∀ x ∈ layer ε E V k, casimir E x = (c : ℂ) • x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    exact hc x hx
  | succ k ih =>
    intro x hx
    have hle : layer ε E V (k + 1) ≤ LinearMap.ker (casimir E - (c : ℂ) • 1) := by
      show layer ε E V k ⊔ _ ≤ _
      refine sup_le (fun y hy => ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
      · rw [LinearMap.mem_ker, LinearMap.sub_apply, ih y hy]
        simp
      · rw [Submodule.map_le_iff_le_comap]
        intro y hy
        rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply]
        have e := congrArg (fun f => f y) (casimir_comm hE a b)
        simp only [Module.End.mul_apply] at e
        rw [e, ih y hy, map_smul]
        simp
    have h1 := hle hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
    simpa using h1

theorem exists_sum_nc_norm_sq_le (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤
        ((R + √2 * k) ^ 2 - nsq (rhoC ε) - c) * ‖x‖ ^ 2 := by
  obtain ⟨R, hR, hK⟩ := exists_re_inner_casimirK_layer_le hE hU hVf hVK
  refine ⟨R, hR, fun k x hx => ?_⟩
  have h1 := re_inner_casimir_eq ε hU x
  rw [casimir_eq_smul_on_layer hE hc k x hx, re_inner_smul_self] at h1
  have h2 := hK k x hx
  nlinarith

end Unitary

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem actM_mem_layer_of_inK {V : Submodule ℂ D} (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {k : ℕ} {x : D} (hx : x ∈ layer ε E V k) :
    actM E Z x ∈ layer ε E V k := by
  have hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hZ.2 a) b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h ⊢ <;>
      first | exact h | linear_combination h / 2 | linear_combination -h / 2
  rw [actM, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [LinearMap.smul_apply]
  by_cases hab : ε a = ε b
  · exact Submodule.smul_mem _ _ (layer_kStable hE hV k a b hab x hx)
  · rw [hZ0 a b hab, zero_smul]
    exact zero_mem _

theorem actM_pow_mem_layer_of_inK {V : Submodule ℂ D} (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {k : ℕ} {x : D} (hx : x ∈ layer ε E V k) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ layer ε E V k := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact actM_mem_layer_of_inK hE hV hZ ih

theorem exists_norm_actM_pow_le_of_inK {V : Submodule ℂ D} (hE : IsGlRep E)
    (hV : IsKStableSub ε E V) (hVf : FiniteDimensional ℂ V) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : inK ε Z) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ layer ε E V k, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by
  haveI : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hVf k
  let T : layer ε E V k →ₗ[ℂ] layer ε E V k :=
    (actM E Z).restrict (fun x hx => actM_mem_layer_of_inK hE hV hZ hx)
  let T' := LinearMap.toContinuousLinearMap T
  refine ⟨‖T'‖, norm_nonneg _, fun x hx m => ?_⟩
  have hpow : ∀ m : ℕ, ((actM E Z) ^ m) x = (((T ^ m) ⟨x, hx⟩ : layer ε E V k) : D) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      rfl
  have hnorm : ∀ (m : ℕ) (y : layer ε E V k), ‖(T ^ m) y‖ ≤ ‖T'‖ ^ m * ‖y‖ := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply]
      calc ‖T ((T ^ m) y)‖ = ‖T' ((T ^ m) y)‖ := rfl
        _ ≤ ‖T'‖ * ‖(T ^ m) y‖ := T'.le_opNorm _
        _ ≤ ‖T'‖ * (‖T'‖ ^ m * ‖y‖) := by gcongr; exact ih y
        _ = ‖T'‖ ^ (m + 1) * ‖y‖ := by ring
  rw [hpow]
  exact hnorm m ⟨x, hx⟩

theorem exp_inK_apply_mem_closure (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {v : D} (hv : v ∈ genSub E V) :
    σ (NormedSpace.exp Z) (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have hE := hD.glRep
  have hv' := hv
  rw [genSub_eq_iSup_layer hE hVK] at hv'
  obtain ⟨k, hk⟩ : ∃ k, v ∈ layer ε E V k :=
    (Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun i j hij => layer_mono hij)).mp hv'
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_inK hE hVK hVf hZ k
  have hs : Summable fun m : ℕ => C ^ m * ‖v‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_left ‖v‖
    refine this.congr fun m => ?_
    simp only [sub_zero, abs_one, one_pow, mul_one]
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖)
    (fun m => by simpa using hC v hk m) 0 1 hs
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, Complex.ofReal_one,
    one_smul, ContinuousLinearMap.one_apply, sub_zero, one_pow] at hsum
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  exact Submodule.mem_map_of_mem
    (layer_le_genSub (ε := ε) k (actM_pow_mem_layer_of_inK hE hVK hZ hk m))

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end
