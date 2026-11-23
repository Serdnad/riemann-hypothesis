module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.BinomRight

theorem prod_monomial' {R σ ι : Type} [CommRing R] (s : Finset ι) (n : ι → σ →₀ ℕ) (c : ι → R) :
    ∏ i ∈ s, (monomial (n i) (c i) : MvPowerSeries σ R) =
      monomial (∑ i ∈ s, n i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [monomial_zero_eq_C]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, ih, monomial_mul_monomial, Finset.sum_insert hj, Finset.prod_insert hj]

theorem add_pow_X' {R σ : Type} [CommRing R] (u v : σ) (k : ℕ) :
    ((X u + X v : MvPowerSeries σ R)) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        monomial (Finsupp.single u j + Finsupp.single v (k - j)) (k.choose j : R) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, ← map_natCast (C (σ := σ) (R := R)),
    ← monomial_zero_eq_C, monomial_mul_monomial, add_zero]
  simp only [one_mul]

end GlobalTheory.BinomRight

namespace GlobalTheory.BinomRight

variable {R : Type} [CommRing R] {d : ℕ}

def expo (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ :=
  (∑ i, Finsupp.single (Sum.inl i) (α (Sum.inl i))) +
    ∑ i, (Finsupp.single (Sum.inr (Sum.inl i)) (J i) +
      Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i) - J i))

theorem expo_inl (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) (i : Fin d) :
    expo α J (Sum.inl i) = α (Sum.inl i) := by
  classical
  simp [expo, Finsupp.single_apply]

theorem expo_inr_inl (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) (i : Fin d) :
    expo α J (Sum.inr (Sum.inl i)) = J i := by
  classical
  simp [expo, Finsupp.single_apply]

theorem expo_inr_inr (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) (i : Fin d) :
    expo α J (Sum.inr (Sum.inr i)) = α (Sum.inr i) - J i := by
  classical
  simp [expo, Finsupp.single_apply]
  rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
  simp

theorem prod_eq_sum (α : Fin d ⊕ Fin d →₀ ℕ) :
    (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) =
      ∑ J ∈ Fintype.piFinset (fun i => Finset.range (α (Sum.inr i) + 1)),
        monomial (expo α J) (∏ i, ((α (Sum.inr i)).choose (J i) : R)) := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, x1, x2, x3, X_pow_eq, add_pow_X', prod_monomial']
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [prod_monomial', monomial_mul_monomial, Finset.prod_const_one, one_mul, expo]

end GlobalTheory.BinomRight

namespace GlobalTheory.BinomRight

variable {R : Type} [CommRing R] {d : ℕ}

theorem sumElim_eq_expo_iff (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) (J : Fin d → ℕ)
    (hJ : ∀ i, J i ≤ α (Sum.inr i)) :
    Finsupp.sumElim a (Finsupp.sumElim b e) = expo α J ↔
      α = Finsupp.sumElim a (b + e) ∧ J = ⇑b := by
  constructor
  · intro h
    have h1 := fun i => DFunLike.congr_fun h (Sum.inl i)
    have h2 := fun i => DFunLike.congr_fun h (Sum.inr (Sum.inl i))
    have h3 := fun i => DFunLike.congr_fun h (Sum.inr (Sum.inr i))
    simp only [expo_inl, expo_inr_inl, expo_inr_inr, Finsupp.sumElim_apply, Sum.elim_inl,
      Sum.elim_inr] at h1 h2 h3
    have hJb : J = ⇑b := funext fun i => (h2 i).symm
    refine ⟨Finsupp.ext fun s => ?_, hJb⟩
    rcases s with i | i
    · simp [h1 i]
    · have := h3 i; have := hJ i; have := h2 i
      simp only [Finsupp.sumElim_apply, Sum.elim_inr, Finsupp.add_apply]
      omega
  · rintro ⟨rfl, rfl⟩
    refine Finsupp.ext fun s => ?_
    rcases s with i | i | i
    · simp [expo_inl]
    · simp [expo_inr_inl]
    · simp [expo_inr_inr]

end GlobalTheory.BinomRight

namespace GlobalTheory.BinomRight

theorem coeff_prod_pow_second_add_third_threeGroups {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ)
    (a b e : Fin d →₀ ℕ) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e))
        (α.prod fun s k => (Sum.elim x1
          (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) =
      if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [prod_eq_sum, map_sum]
  simp only [coeff_monomial]
  have hmem : ∀ J ∈ Fintype.piFinset (fun i => Finset.range (α (Sum.inr i) + 1)),
      ∀ i, J i ≤ α (Sum.inr i) := fun J hJ i =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hJ i))
  by_cases hα : α = Finsupp.sumElim a (b + e)
  · rw [if_pos hα]
    have hb : ⇑b ∈ Fintype.piFinset (fun i => Finset.range (α (Sum.inr i) + 1)) := by
      refine Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 ?_
      rw [hα]; simp
    rw [Finset.sum_eq_single_of_mem (⇑b) hb]
    · rw [if_pos ((sumElim_eq_expo_iff α a b e _ (hmem _ hb)).2 ⟨hα, rfl⟩)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hα]; simp
    · intro J hJ hJb
      rw [if_neg fun h => hJb ((sumElim_eq_expo_iff α a b e J (hmem J hJ)).1 h).2]
  · rw [if_neg hα]
    refine Finset.sum_eq_zero fun J hJ => ?_
    rw [if_neg fun h => hα ((sumElim_eq_expo_iff α a b e J (hmem J hJ)).1 h).1]

end GlobalTheory.BinomRight
end
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.BinomLeft

variable {R : Type} [CommRing R] {d : ℕ}

theorem natCast_eq_monomial {σ : Type} (n : ℕ) : ((n : ℕ) : MvPowerSeries σ R) = monomial 0 (n : R) := by
  rw [monomial_zero_eq_C_apply, map_natCast]

theorem pow_threeGroupsFirst_add_second_expansion (i : Fin d) (k : ℕ) :
    ((x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        monomial (Finsupp.single (Sum.inl i) j + Finsupp.single (Sum.inr (Sum.inl i)) (k - j)) (k.choose j : R) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [x1, x2, X_pow_eq, monomial_mul_monomial, one_mul, natCast_eq_monomial, add_zero, mul_one]

theorem expo_iff (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) (p : Fin d → ℕ)
    (hp : ∀ i, p i ≤ α (Sum.inl i)) :
    Finsupp.sumElim a (Finsupp.sumElim b e) =
        (∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) ↔
      α = Finsupp.sumElim (a + b) e ∧ p = ⇑a := by
  classical
  have hv : ∀ s, ((∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ) s =
        Sum.elim p (Sum.elim (fun i => α (Sum.inl i) - p i) (fun i => α (Sum.inr i))) s := by
    intro s
    rcases s with i | i | i
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj, Ne.symm hj]) (by simp)]
      simp
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  constructor
  · intro h
    have h1 : ∀ i, a i = p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inl i); rw [hv] at this; simpa using this
    have h2 : ∀ i, b i = α (Sum.inl i) - p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inl i)); rw [hv] at this; simpa using this
    have h3 : ∀ i, e i = α (Sum.inr i) := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inr i)); rw [hv] at this; simpa using this
    refine ⟨?_, funext fun i => (h1 i).symm⟩
    ext s
    rcases s with i | i
    · have := hp i; have := h1 i; have := h2 i; simp; omega
    · simp [h3 i]
  · rintro ⟨rfl, rfl⟩
    ext s
    rw [hv]
    rcases s with i | i | i <;> simp

theorem coeff_prod_pow_add (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e))
        (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) =
      if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, pow_threeGroupsFirst_add_second_expansion]
  rw [Finset.prod_univ_sum]

  simp only [x3, X_pow_eq, prod_monomial, Finset.sum_mul, monomial_mul_monomial, mul_one, map_sum,
  coeff_monomial, Finset.prod_const_one]
  have hmem : ∀ p ∈ Fintype.piFinset fun i => Finset.range (α (Sum.inl i) + 1), ∀ i, p i ≤ α (Sum.inl i) := by
    intro p hp i
    have := Fintype.mem_piFinset.1 hp i
    rw [Finset.mem_range] at this
    omega
  split_ifs with hα
  · rw [Finset.sum_congr rfl fun p hp => by rw [if_congr (expo_iff α a b e p (hmem p hp)) rfl rfl]]
    simp only [hα, true_and]
    rw [Finset.sum_ite_eq']
    rw [if_pos]
    · simp
    · rw [Fintype.mem_piFinset]
      intro i
      simp only [Finset.mem_range, Finsupp.sumElim_apply, Sum.elim_inl, Finsupp.coe_add, Pi.add_apply]
      omega
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg]
    intro h
    exact hα ((expo_iff α a b e p (hmem p hp)).1 h).1

end GlobalTheory.BinomLeft
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.IdealAt2

theorem coeff_powerSeriesEvalTwoGroups_mem_ideal : ∀ (R : Type) [CommRing R] (d : ℕ) (τ : Type) (I : Ideal R)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
    (∀ α, coeff α t ∈ I) → ∀ α, coeff α (at2 t u v) ∈ I := by
  intro R _ d τ I t u v hu hv ht α
  have hs : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]
  rw [at2, coeff_subst hs]
  refine finsum_induction (fun x => x ∈ I) I.zero_mem (fun x y hx hy => I.add_mem hx hy) ?_
  intro e
  rw [smul_eq_mul]
  exact I.mul_mem_right _ (ht e)

end GlobalTheory.IdealAt2
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

namespace Katz

namespace CoefChange

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (r : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map r (at2 c u v) = at2 (map r c) (fun i => map r (u i)) (fun i => map r (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun j => by
    cases j with
    | inl i => exact hu i
    | inr i => exact hv i))]
  congr 1
  funext j
  cases j <;> rfl

theorem map_subst' (r : R →+* S) {σ : Type} [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    map r (subst a f) = subst (fun i => map r (a i)) (map r f) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero ha)]

theorem map_inL (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inL f) = inL (map r f) := by
  unfold inL
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem map_inR (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inR f) = inR (map r f) := by
  unfold inR
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem inL_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inL f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

theorem inR_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inR f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

end CoefChange


open CoefChange in
theorem map_cob_swap_pull : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (S : Type) [CommRing S] (r : R →+* S), (∀ f, map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f)) ∧ (∀ c, map r (cob2 μ c) = cob2 (fun i => map r (μ i)) (map r c)) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, map r (Katz.swap c) = Katz.swap (map r c)) ∧ (∀ f : MvPowerSeries (Fin d) R, lin (map r f) = fun i => r (lin f i)) ∧ ∀ φ : Fin d → MvPowerSeries (Fin d) R, (∀ i, constantCoeff (φ i) = 0) → (∀ c, map r (pull2 φ c) = pull2 (fun i => map r (φ i)) (map r c)) ∧ ∀ f : MvPowerSeries (Fin d) R, map r (subst φ f) = subst (fun i => map r (φ i)) (map r f) := by
  intro R _ d μ hμ S _ r
  have hX : ∀ {τ : Type} (i : τ), constantCoeff (X i : MvPowerSeries τ R) = 0 :=
    fun i => constantCoeff_X i
  have hop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    unfold op at2
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i)) (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i) (hμ i)
  have mapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (fun i => map r (op μ u v i)) =
        op (fun i => map r (μ i)) (fun i => map r (u i)) (fun i => map r (v i)) := by
    intro u v hu hv
    funext i
    exact mvPowerSeriesMap_evalTwoGroups r (μ i) u v hu hv
  have mx1 : (fun i => map r ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x1 := by
    funext i; exact map_X r _
  have mx2 : (fun i => map r ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x2 := by
    funext i; exact map_X r _
  have mx3 : (fun i => map r ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x3 := by
    funext i; exact map_X r _
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold cob1
    rw [map_sub, map_sub, map_subst' r μ hμ, map_inL, map_inR]
  · intro c
    unfold cob2
    rw [map_sub, map_add (f := _), map_sub, mvPowerSeriesMap_evalTwoGroups r c _ _ h2 h3, mvPowerSeriesMap_evalTwoGroups r c _ _ (hop _ _ h1 h2) h3,
      mvPowerSeriesMap_evalTwoGroups r c _ _ h1 (hop _ _ h2 h3), mvPowerSeriesMap_evalTwoGroups r c _ _ h1 h2, mapop _ _ h1 h2,
      mapop _ _ h2 h3, mx1, mx2, mx3]
  · intro c
    unfold Katz.swap
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun _ => hX _) (fun _ => hX _)]
    congr 1 <;> funext i <;> exact map_X r _
  · intro f
    funext i
    unfold lin
    rw [coeff_map]
  · intro φ hφ
    refine ⟨?_, fun f => map_subst' r φ hφ f⟩
    intro c
    unfold pull2
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun i => inL_const (hφ i)) (fun i => inR_const (hφ i))]
    congr 1 <;> funext i
    · exact map_inL r (φ i)
    · exact map_inR r (φ i)

end Katz

end GlobalTheory
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

namespace Katz

namespace ExtCoeff

variable {O E : Type} [CommRing O] [CommRing E] {d : ℕ}

theorem hasSubst_XL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_XR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem map_inL (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inL f) = inL (map h f) := by
  unfold inL
  rw [map_subst hasSubst_XL]
  congr 1
  funext i
  exact map_X h _

theorem map_inR (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inR f) = inR (map h f) := by
  unfold inR
  rw [map_subst hasSubst_XR]
  congr 1
  funext i
  exact map_X h _

theorem map_formalGroupLawCoboundaryOne_eq (h : O →+* E) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (s : MvPowerSeries (Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    cob1 (fun i => map h (μ i)) (map h s) = map h (cob1 μ s) := by
  unfold cob1
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ), map_inL, map_inR]

end ExtCoeff

end Katz

end GlobalTheory
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

theorem coeff_at2_x1_x2_eq_zero_of_third_ne_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ) (he : e ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  classical
  let g : Fin d ⊕ Fin d → Fin d ⊕ (Fin d ⊕ Fin d) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hg : (Sum.elim x1 x2 : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = X ∘ g := by
    funext s; rcases s with s | s <;> rfl
  have h1 : at2 c x1 x2 = rename g c := by
    rw [rename_eq_subst, ← hg]; rfl
  rw [h1]
  apply coeff_rename_eq_zero
  rintro ⟨v, hv⟩
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h; push_neg at h; exact he (Finsupp.ext h)
  apply hi
  have h2 := congrArg (fun w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ => w (Sum.inr (Sum.inr i))) hv
  rw [Finsupp.mapDomain_notin_range] at h2
  · simpa using h2.symm
  · rintro ⟨s, hs⟩; rcases s with s | s <;> simp [g] at hs

end GlobalTheory
end
