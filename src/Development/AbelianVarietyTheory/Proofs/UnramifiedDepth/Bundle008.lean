module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle007
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle005
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Expand
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle001
import ReciprocityTheory.DualLattices.Bundle001
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem exists_integral_combination_of_mem_HaO :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] (e : K →+* C) (R : Subring C), (∀ x : V, e (algebraMap V K x) ∈ R) → ∀ (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C), P ∈ HaO r n C R cc isX a → ∃ (s : ℕ) (c : Fin s → C) (Q : Fin s → MvPolynomial (Letter T r n) K), (∀ j, c j ∈ R) ∧ (∀ j, Q j ∈ HaO r n K (algebraMap V K).range cc isX a) ∧ P = ∑ j, MvPolynomial.C (c j) * MvPolynomial.map e (Q j) := by
  intro T r n V K C _ _ _ _ _ _ _ e R hR cc isX a P hP
  classical
  let _ : Algebra K C := e.toAlgebra
  obtain ⟨hH, hO⟩ := hP
  obtain ⟨s, c, φ, hc, hφ⟩ := GlobalTheory.exists_integral_basis_linear_coordinates V K C R hR (P.support.image fun μ => P.coeff μ) (by
    intro x hx
    obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
    exact hO μ)
  let Q : Fin s → MvPolynomial (Letter T r n) K := fun j =>
    ∑ μ ∈ P.support, MvPolynomial.monomial μ (φ j (P.coeff μ))
  have hQ : ∀ j μ, (Q j).coeff μ = φ j (P.coeff μ) := by
    intro j μ
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
  refine ⟨s, c, Q, hc, fun j => ⟨GlobalTheory.CoeffFunctional.mem_HHa_of_coeff_functional T r n K C (φ j) cc isX a P (Q j) (hQ j) hH, ?_⟩, ?_⟩
  · intro μ
    rw [hQ]
    by_cases h : μ ∈ P.support
    · exact (hφ _ (Finset.mem_image_of_mem _ h)).1 j
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
      exact zero_mem _
  · ext μ
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hQ]
    by_cases h : μ ∈ P.support
    · refine (hφ _ (Finset.mem_image_of_mem _ h)).2.trans ?_
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · rw [MvPolynomial.notMem_support_iff.mp h]
      simp

end GlobalTheory
end

section

open ReciprocityTheory.PGsh

namespace GlobalTheory.ExpWeight

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ)


variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ) in
theorem _root_.GlobalTheory.ExpWeight.weight_exp :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (h : MvPowerSeries σ C), MvPowerSeries.constantCoeff h = 0 →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (PowerSeries.subst (h) (PowerSeries.exp C))))) := by
  intro C _ _ v l hl hvl σ _ _ ρ h h0 hh
  set c : ℝ := 1 / ((l : ℝ) - 1) with hc
  set w : (σ →₀ ℕ) → ℝ := fun α => α.sum (fun j e => ρ j * (e : ℝ)) with hw
  have hwadd : ∀ α β : σ →₀ ℕ, w (α + β) = w α + w β := fun α β => by
    simp only [hw]
    exact Finsupp.sum_add_index' (fun j => by simp) (fun j a b => by push_cast; ring)
  have hsumle : ∀ {ι : Type} (s : Finset ι) (f : ι → C) (r : ℝ),
      (∀ i ∈ s, ((r : ℝ) : WithTop ℝ) ≤ v (f i)) → ((r : ℝ) : WithTop ℝ) ≤ v (∑ i ∈ s, f i) := by
    intro ι s f r hf
    refine Finset.sum_induction f (fun x => ((r : ℝ) : WithTop ℝ) ≤ v x) (fun a b ha hb => ?_) ?_ hf
    · exact le_trans (le_min ha hb) (v.map_add a b)
    · simp
  have hpow : ∀ (d : ℕ) (α : σ →₀ ℕ), (((d : ℝ) * c - w α : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h ^ d)) := by
    intro d
    induction d with
    | zero =>
      intro α
      rw [pow_zero, MvPowerSeries.coeff_one]
      split_ifs with hα
      · subst hα
        simp [hw]
      · simp
    | succ d ih =>
      intro α
      rw [pow_succ, MvPowerSeries.coeff_mul]
      refine hsumle _ _ _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [v.map_mul]
      have e : ((((d + 1 : ℕ) : ℝ) * c - w α : ℝ) : WithTop ℝ) =
          (((d : ℝ) * c - w p.1 : ℝ) : WithTop ℝ) + ((1 / ((l : ℝ) - 1) - w p.2 : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add, ← hp, hwadd, hc]
        congr 1
        push_cast
        ring
      rw [e]
      exact add_le_add (ih p.1) (hh p.2)
  intro α
  have hsub : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero h0
  rw [PowerSeries.coeff_subst hsub]
  refine finsum_induction (fun x => (((0 : ℝ) - w α : ℝ) : WithTop ℝ) ≤ v x) (by simp)
    (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b)) fun d => ?_
  simp only [PowerSeries.coeff_exp, smul_eq_mul, v.map_mul]
  have hf : (d.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hinv : algebraMap ℚ C (1 / (d.factorial : ℚ)) = ((d.factorial : C))⁻¹ := by simp
  rw [hinv]
  obtain ⟨y, hy⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.exists_real v (inv_ne_zero hf)
  have hfact := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hvl (Nat.factorial_ne_zero d)
  have hprod : v ((d.factorial : C))⁻¹ + v (d.factorial : C) = 0 := by
    rw [← v.map_mul, inv_mul_cancel₀ hf, v.map_one]
  rw [hy, hfact, ← WithTop.coe_add, WithTop.coe_eq_zero] at hprod
  have hle := _root_.GlobalTheory.LegendreBounds.upper l hl d
  have hyr : y = -((d.factorial.factorization l : ℕ) : ℝ) := by linarith
  simp only [Nat.padicValNat_def, ← Nat.factorization_def _ hl] at hle
  have hdc : (d : ℝ) / ((l : ℝ) - 1) = d * c := by rw [hc]; ring
  rw [hy]
  calc (((0 : ℝ) - w α : ℝ) : WithTop ℝ) ≤ ((y + ((d : ℝ) * c - w α) : ℝ) : WithTop ℝ) :=
        WithTop.coe_le_coe.mpr (by linarith)
    _ = ((y : ℝ) : WithTop ℝ) + (((d : ℝ) * c - w α : ℝ) : WithTop ℝ) := WithTop.coe_add _ _
    _ ≤ _ := add_le_add le_rfl (hpow d α)

end GlobalTheory.ExpWeight
end

section

open ReciprocityTheory.PGsh

theorem _root_.GlobalTheory.T.legendre_bounds_factorial_multiIndex_capelli : (∀ (l : ℕ), l.Prime → (∀ N : ℕ, 1 ≤ N → (N : ℝ) / (l - 1) - (Real.logb l N + 1) ≤ padicValNat l N.factorial ∧ (padicValNat l N.factorial : ℝ) ≤ (N - 1) / (l - 1)) ∧
    (∀ (κ : Type) [Fintype κ] (A : κ → ℕ), 1 ≤ ∑ j, A j → ((∑ j, A j : ℕ) : ℝ) / (l - 1) - Fintype.card κ * (Real.logb l ((∑ j, A j : ℕ) : ℝ) + 1) ≤ padicValNat l (∏ j, (A j).factorial)) ∧
    ∀ n₀ x : ℕ, (padicValNat l (∏ c ∈ Finset.range n₀, (x + c).factorial) : ℝ) - padicValNat l (∏ c ∈ Finset.range n₀, c.factorial) ≤
      n₀ * x / (l - 1) + n₀ * (Real.logb l n₀ + 1)) := by
  first | exact @GlobalTheory.LegendreBounds.legendre_bounds | exact GlobalTheory.LegendreBounds.legendre_bounds | (intros; apply GlobalTheory.LegendreBounds.legendre_bounds <;> assumption)
end

section

open ReciprocityTheory.PGsh

namespace GlobalTheory

theorem factorization_le_four_fifteenths {l B : ℕ} (hl : 5 ≤ l) (hB : B ≠ 0) :
    (B.factorization l : ℝ) ≤ 4 / 15 * (B : ℝ) := by
  have h1 : l ^ B.factorization l ≤ B := Nat.ordProj_le l hB
  have h2 : 5 ^ B.factorization l ≤ l ^ B.factorization l := Nat.pow_le_pow_left hl _
  have h3 : ∀ k : ℕ, 4 * k + 1 ≤ 5 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have h4 : 4 * B.factorization l + 1 ≤ B := le_trans (h3 _) (le_trans h2 h1)
  have h5 : (4 : ℝ) * (B.factorization l : ℝ) + 1 ≤ B := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ (B.factorization l : ℝ) := Nat.cast_nonneg _
  linarith

theorem four_fifteenths_le_slope_gap {x : ℝ} (hx : 5 ≤ x) {i : ℕ} (hi : 1 ≤ i) :
    4 / 15 ≤ (1 / (x ^ 2 - 1) + 1 / 2 - 1 / (8 * x ^ i)) - 1 / (x - 1) := by
  have h1 : x ≤ x ^ i := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) hi
  have h2 : 1 / (8 * x ^ i) ≤ 1 / 40 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hq : 0 < x - 1 := by linarith
  have h3 : 1 / (x - 1) - 1 / (x ^ 2 - 1) = x / (x ^ 2 - 1) := by
    have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [this]
    have hr : 0 < x + 1 := by linarith
    field_simp
    ring
  have h4 : x / (x ^ 2 - 1) ≤ 5 / 24 := by
    rw [div_le_div_iff₀ hp (by norm_num)]
    nlinarith
  linarith

theorem weight_of_weight_pderiv :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 5 ≤ l → ∀ (i : ℕ) (κ κ' : Type) [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] (h₁ : MvPowerSeries (κ ⊕ κ') C), 1 ≤ i →
    (∀ α, MvPowerSeries.coeff α h₁ ≠ 0 → ∃ q, α (Sum.inr q) ≠ 0) → (∀ b, (∀ α, (((0) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) - 1)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (MvPowerSeries.pderiv (R := C) (Sum.inr b) h₁)))) →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h₁)))) := by
  intro C _ _ v l hl hv h5 i κ κ' _ _ _ _ h₁ hi hsupp hder α
  by_cases h0 : MvPowerSeries.coeff α h₁ = 0
  · rw [h0, v.map_zero]; exact le_top
  obtain ⟨b, hb⟩ := hsupp α h0
  obtain ⟨β, rfl⟩ : ∃ β : κ ⊕ κ' →₀ ℕ, α = β + Finsupp.single (Sum.inr b) 1 := by
    refine ⟨α - Finsupp.single (Sum.inr b) 1, ?_⟩
    rw [tsub_add_cancel_of_le]
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hb)
  have h := hder b β
  have hc : ((β (Sum.inr b) : C) + 1) = ((β (Sum.inr b) + 1 : ℕ) : C) := by push_cast; rfl
  rw [MvPowerSeries.coeff_pderiv, hc, v.map_mul,
    ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hv (Nat.succ_ne_zero _)] at h
  have hf := factorization_le_four_fifteenths h5 (Nat.succ_ne_zero (β (Sum.inr b)))
  have hg := four_fifteenths_le_slope_gap (x := (l : ℝ)) (by exact_mod_cast h5) hi
  generalize v (MvPowerSeries.coeff (β + Finsupp.single (Sum.inr b) 1) h₁) = w at h ⊢
  induction w using WithTop.recTopCoe with
  | top => exact le_top
  | coe w =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h
    rw [WithTop.coe_le_coe]
    rw [Finsupp.sum_add_index' (by intro j; simp) (by intro j e e'; push_cast; ring),
      Finsupp.sum_single_index (by simp)]
    rw [Finsupp.sum_fintype _ _ (by intro j; simp), Fintype.sum_sum_type] at h ⊢
    simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum] at h ⊢
    have hJ : (β (Sum.inr b) : ℝ) ≤ ∑ q, (β (Sum.inr q) : ℝ) :=
      Finset.single_le_sum (f := fun q => (β (Sum.inr q) : ℝ))
        (fun q _ => Nat.cast_nonneg _) (Finset.mem_univ b)
    have hJ0 : (0 : ℝ) ≤ β (Sum.inr b) := Nat.cast_nonneg _
    push_cast at hf ⊢
    generalize (∑ q, (β (Sum.inr q) : ℝ)) = J at h hJ ⊢
    generalize (1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) = c' at hg ⊢
    generalize 1 / ((l : ℝ) - 1) = c at h hg ⊢
    have hm : 4 / 15 * (J + 1) ≤ (c' - c) * (J + 1) :=
      mul_le_mul_of_nonneg_right hg (by linarith)
    nlinarith

end GlobalTheory
end

section

open scoped BigOperators

namespace GlobalTheory.CubeFib

theorem exists_pow_eq_of_pderiv_eq_zero {k : Type} [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] {σ : Type} [DecidableEq σ] (F : MvPowerSeries σ k)
    (hF : ∀ i, MvPowerSeries.pderiv (R := k) i F = 0) : ∃ g : MvPowerSeries σ k, g ^ p = F := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : ExpChar k p := ExpChar.prime Fact.out
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  let g : MvPowerSeries σ k :=
    fun d => (frobeniusEquiv k p).symm (MvPowerSeries.coeff (p • d) F)
  have hg : ∀ d, MvPowerSeries.coeff d g =
      (frobeniusEquiv k p).symm (MvPowerSeries.coeff (p • d) F) := fun d => rfl
  refine ⟨g, ?_⟩
  rw [← MvPowerSeries.map_frobenius_expand p hp]
  ext n
  rw [MvPowerSeries.coeff_map]
  by_cases! h : ∀ i, p ∣ n i
  · obtain ⟨m, hm⟩ : ∃ m, p • m = n := ⟨n.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm, MvPowerSeries.coeff_expand_smul, hg]
    exact (frobeniusEquiv k p).apply_symm_apply _
  · obtain ⟨i, hi⟩ := h
    rw [MvPowerSeries.coeff_expand_of_not_dvd p hp _ hi, map_zero]
    have hni : n i ≠ 0 := fun h0 => hi (h0 ▸ dvd_zero p)
    have hle : Finsupp.single i 1 ≤ n := by
      rw [Finsupp.single_le_iff]; omega
    have h1 := congrArg (MvPowerSeries.coeff (n - Finsupp.single i 1)) (hF i)
    rw [MvPowerSeries.coeff_pderiv, map_zero, tsub_add_cancel_of_le hle] at h1
    have h2 : (((n - Finsupp.single i 1 : σ →₀ ℕ) i : k) + 1) = (n i : k) := by
      rw [← Nat.cast_succ]; congr 1; simp; omega
    rw [h2] at h1
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact h3.symm
    · exact absurd ((CharP.cast_eq_zero_iff k p _).mp h3) hi

theorem derivation_mem_pow_smul_top {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] (D : Derivation R A M) (I : Ideal A) (m : ℕ) :
    ∀ a ∈ I ^ (m + 1), D a ∈ (I ^ m • ⊤ : Submodule A M) := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [Derivation.leibniz]
      refine add_mem (Submodule.smul_mem_smul hx Submodule.mem_top) ?_
      rw [pow_succ', ← smul_eq_mul, Submodule.smul_assoc]
      exact Submodule.smul_mem_smul hy (ih x hx)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy

theorem derivation_algebraMap_perfect {k K : Type} [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [Field K] [Algebra k K] (D : Derivation ℤ K K) (c : k) :
    D (algebraMap k K c) = 0 := by
  haveI : ExpChar k p := ExpChar.prime Fact.out
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  obtain ⟨b, rfl⟩ := (frobeniusEquiv k p).surjective c
  rw [frobeniusEquiv_apply, frobenius_def, map_pow, Derivation.leibniz_pow, nsmul_eq_mul,
    CharP.cast_eq_zero, zero_mul]

theorem derivation_eq_zero_of_kaehler {k A K : Type} [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [CommRing A] [Algebra k A] [Field K] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] (f : A) (hd : KaehlerDifferential.D k A f = 0) (D : Derivation ℤ K K) :
    D (algebraMap A K f) = 0 := by
  let L : A →ₗ[k] K :=
    { toFun := fun a => D (algebraMap A K a)
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c a => by
        rw [Algebra.smul_def, map_mul, Derivation.leibniz,
          ← IsScalarTower.algebraMap_apply, derivation_algebraMap_perfect p D c, smul_zero,
          add_zero, RingHom.id_apply, Algebra.smul_def c, smul_eq_mul] }
  let D' : Derivation k A K := Derivation.mk' L (fun a b => by
    change D (algebraMap A K (a * b)) =
      a • D (algebraMap A K b) + b • D (algebraMap A K a)
    rw [map_mul, Derivation.leibniz, Algebra.smul_def a, Algebra.smul_def b, smul_eq_mul,
      smul_eq_mul])
  have h := D'.liftKaehlerDifferential_comp_D f
  rw [hd, map_zero] at h
  exact h.symm

theorem exists_pow_eq_fractionRing_of_pderiv_eq_zero : ∀ (k : Type) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra k A] [Algebra.EssFiniteType k A] (σ : Type) [Fintype σ] [DecidableEq σ] (j : A →ₐ[k] MvPowerSeries σ k), (∀ (m : ℕ) (a : A), j a ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ m ↔ a ∈ IsLocalRing.maximalIdeal A ^ m) → (∀ (m : ℕ) (s : MvPowerSeries σ k), ∃ a : A, j a - s ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ m) → ∀ f : A, (∀ i, MvPowerSeries.pderiv (R := k) i (j f) = 0) → ∃ h : FractionRing A, h ^ p = algebraMap A (FractionRing A) f := by
  intro k _ _ p _ _ A _ _ _ _ _ σ _ _ j hj hsurj f hf
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing k A
  haveI : CharP (FractionRing A) p :=
    charP_of_injective_algebraMap (algebraMap k (FractionRing A)).injective p
  haveI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  haveI : CharP (MvPowerSeries σ k) p :=
    charP_of_injective_algebraMap (algebraMap k (MvPowerSeries σ k)).injective p
  obtain ⟨g, hg⟩ := exists_pow_eq_of_pderiv_eq_zero p (j f) hf
  have hd : KaehlerDifferential.D k A f = 0 := by
    have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Ω[A⁄k])
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    rw [← Submodule.mem_bot A, ← key, Submodule.mem_iInf]
    intro m
    obtain ⟨a, ha⟩ := hsurj (m + 1) g
    have h1 : a ^ p - f ∈ IsLocalRing.maximalIdeal A ^ (m + 1) := by
      rw [← hj, map_sub, map_pow, ← hg, ← sub_pow_char]
      exact Ideal.pow_mem_of_mem _ ha p (Nat.pos_of_ne_zero hp)
    have h2 := derivation_mem_pow_smul_top (KaehlerDifferential.D k A) _ m _ h1
    rw [map_sub, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero,
      zero_smul, zero_sub] at h2
    exact (neg_mem_iff).mp h2
  apply GlobalTheory.T.exists_pth_root_of_derivation_zero
  intro D
  exact derivation_eq_zero_of_kaehler p f hd D

end GlobalTheory.CubeFib
end
