module

import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem dvr_fraction_field_char_zero_prime {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  apply Formalism.MainNotions.G.GLWeightTheory.dvr_fraction_field_charZero_prime <;> assumption

section field

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_scalar {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  unfold weightSp
  simp [Submodule.mem_iInf, sub_eq_zero]

theorem inv_factorial_prod_eq_choose [CharZero K] (m : ℤ) (k : ℕ) :
    ((k.factorial : K)⁻¹) * ∏ j ∈ range k, ((m : K) - (j : K)) = ((Ring.choose m k : ℤ) : K) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose m k
  rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h1
  have h2 := congrArg (fun z : ℤ => (z : K)) h1
  push_cast at h2
  rw [h2, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_mul]

theorem binomial_diagonal_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (k : ℕ) : binomE E a k x = ((Ring.choose (mu a) k : ℤ) : K) • x := by
  have hx' := (mem_weightSpace_iff_diag_scalar.mp hx) a
  unfold binomE
  rw [LinearMap.smul_apply, ← inv_factorial_prod_eq_choose (mu a) k, mul_smul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx']
    rw [← sub_smul, map_smul, ih, smul_smul]
    congr 1
    ring

def shiftedBinomialOperator (E : GLOps n K V) (a : Fin n) (c : ℤ) (d : ℕ) : Module.End K V :=
  ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : K) • binomE E a ij.1

theorem shifted_binomial_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (c : ℤ) (d : ℕ) : shiftedBinomialOperator E a c d x = ((Ring.choose (mu a + c) d : ℤ) : K) • x := by
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, binomial_diagonal_on_weight hx, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Ring.add_choose_eq d (Commute.all _ _)]
  push_cast
  apply Finset.sum_congr rfl
  intro ij _
  ring

end field

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem intCast_smul_mem_submodule (M : Submodule O V) (z : ℤ) {x : V} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem shifted_binomial_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M) (a : Fin n) (c : ℤ)
    (d : ℕ) {x : V} (hx : x ∈ M) : shiftedBinomialOperator E a c d x ∈ M := by
  unfold UZStable at hM
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro ij _
  rw [LinearMap.smul_apply]
  exact intCast_smul_mem_submodule M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)

theorem lattice_stable_weight_separator [CharZero (KK O)] (E : GLOps n (KK O) V) {lam nu : Fin n → ℤ} (h : nu ≠ lam) :
    ∃ (T : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g lam = 1 ∧ g nu = 0 ∧
      (∀ mu, ∀ x ∈ weightSp E mu, T x = ((g mu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, T x ∈ M := by
  have hex : ∃ a, nu a ≠ lam a := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  obtain ⟨a, ha⟩ := hex
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, lam a - nu a = δ := ⟨(lam a - nu a).toNat, by omega⟩
    refine ⟨shiftedBinomialOperator E a (-nu a) δ, fun mu => Ring.choose (mu a + -nu a) δ, ?_, ?_, ?_, ?_⟩
    · show Ring.choose (lam a + -nu a) δ = 1
      rw [show lam a + -nu a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one]
    · show Ring.choose (nu a + -nu a) δ = 0
      rw [show nu a + -nu a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · intro mu x hx
      exact shifted_binomial_on_weight hx a (-nu a) δ
    · exact fun M hM x hx => shifted_binomial_preserves_lattice hM a (-nu a) δ hx
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, nu a - lam a = δ := ⟨(nu a - lam a).toNat, by omega⟩
    refine ⟨1 - shiftedBinomialOperator E a (-lam a) δ, fun mu => 1 - Ring.choose (mu a + -lam a) δ, ?_, ?_, ?_, ?_⟩
    · show 1 - Ring.choose (lam a + -lam a) δ = 1
      rw [show lam a + -lam a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, sub_zero]
    · show 1 - Ring.choose (nu a + -lam a) δ = 0
      rw [show nu a + -lam a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, sub_self]
    · intro mu x hx
      rw [LinearMap.sub_apply, Module.End.one_apply, shifted_binomial_on_weight hx a (-lam a) δ]
      push_cast
      rw [sub_smul, one_smul]
    · intro M hM x hx
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact M.sub_mem hx (shifted_binomial_preserves_lattice hM a (-lam a) δ hx)

theorem lattice_weight_components_mem [CharZero (KK O)] (E : GLOps n (KK O) V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) : lam ∉ F → ∀ (y0 : V) (f : (Fin n → ℤ) → V),
      y0 ∈ weightSp E lam → (∀ nu ∈ F, f nu ∈ weightSp E nu) → y0 + ∑ nu ∈ F, f nu ∈ M → y0 ∈ M := by
  induction F using Finset.induction_on with
  | empty =>
    intro _ y0 f _ _ hmem
    simpa using hmem
  | @insert a F ha ih =>
    intro hl y0 f hy0 hf hmem
    have hal : a ≠ lam := fun h => hl (h ▸ Finset.mem_insert_self a F)
    obtain ⟨T, g', hg1, hg0, hT, hTM⟩ := lattice_stable_weight_separator E hal
    have hlF : lam ∉ F := fun h => hl (Finset.mem_insert_of_mem h)
    have h2 := hTM M hM _ hmem

    rw [map_add (f := _), map_sum, Finset.sum_insert ha] at h2
    rw [hT lam y0 hy0, hg1, hT a (f a) (hf a (Finset.mem_insert_self a F)), hg0] at h2
    have h3 : ∀ nu ∈ F, T (f nu) = ((g' nu : ℤ) : KK O) • f nu :=
      fun nu hnu => hT nu (f nu) (hf nu (Finset.mem_insert_of_mem hnu))
    rw [Finset.sum_congr rfl h3] at h2
    simp only [Int.cast_one, one_smul, Int.cast_zero, zero_smul, zero_add] at h2
    exact ih hlF y0 (fun nu => ((g' nu : ℤ) : KK O) • f nu) hy0
      (fun nu hnu => Submodule.smul_mem _ _ (hf nu (Finset.mem_insert_of_mem hnu))) h2

theorem weight_component_decomposition (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (lam : Fin n → ℤ) (y : V) :
    ∃ (y0 : V) (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), lam ∉ F ∧ y0 ∈ weightSp E lam ∧
      (∀ nu ∈ F, f nu ∈ weightSp E nu) ∧ y = y0 + ∑ nu ∈ F, f nu := by
  have hy : y ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by
    rw [hE]; exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ y).mp hy
  refine ⟨c lam, c.support.erase lam, c, by simp, hc lam, fun nu _ => hc nu, ?_⟩
  rw [← hsum]
  simp only [Finsupp.sum]
  by_cases h : lam ∈ c.support
  · exact (Finset.add_sum_erase _ _ h).symm
  · have h0 : c lam = 0 := by simpa using h
    rw [Finset.erase_eq_self.mpr h, h0, zero_add]

theorem integral_enveloping_preserves_submodule {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    {u : Module.End (KK O) V} (hu : u ∈ UZmon E) : ∀ x ∈ M, u x ∈ M := by
  unfold UZmon at hu
  unfold UZStable at hM
  induction hu using Submonoid.closure_induction with
  | mem u hu => exact hM u hu
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem sum_other_weights_mem (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) (hl : lam ∉ F)
    (f : (Fin n → ℤ) → V) (hf : ∀ nu ∈ F, f nu ∈ weightSp E nu) : ∑ nu ∈ F, f nu ∈ otherWts E lam := by
  unfold otherWts
  apply Submodule.sum_mem
  intro nu hnu
  have hne : nu ≠ lam := fun h => hl (h ▸ hnu)
  exact (le_iSup₂ (f := fun mu (_ : mu ∈ {mu | mu ≠ lam}) => weightSp E mu) nu hne) (hf nu hnu)

theorem highest_weight_lattice_bounds [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (lam : Fin n → ℤ) (v : V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (hl : ∀ x, (x ∈ M ∧ x ∈ weightSp E lam) ↔ ∃ c : O, x = c • v) :
    Delta (O := O) E v ≤ M ∧ (M : Set V) ⊆ Nabla (O := O) E lam v := by
  unfold Delta Nabla
  have hv : v ∈ M := ((hl v).mpr ⟨1, (one_smul O v).symm⟩).1
  constructor
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact integral_enveloping_preserves_submodule hM hu v hv
  · intro x hx u hu
    have hux : u x ∈ M := integral_enveloping_preserves_submodule hM hu x hx
    obtain ⟨y0, F, f, hlF, hy0, hf, hdec⟩ := weight_component_decomposition E hE lam (u x)
    have hy0M : y0 ∈ M := lattice_weight_components_mem E M hM lam F hlF y0 f hy0 hf (by rw [← hdec]; exact hux)
    obtain ⟨c, hc⟩ := (hl y0).mp ⟨hy0M, hy0⟩
    refine ⟨c, ?_⟩
    rw [algebraMap_smul, hdec, hc, add_sub_cancel_left]
    exact sum_other_weights_mem E lam F hlF f hf

end lattice

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem coeff_binomial_power_divisibility (p P : ℕ) (hP : 0 < P) (h : ℤ[X]) (l : ℕ) : ∀ (f : ℤ[X]) (j : ℕ),
    (p : ℤ) ^ (l - j / P) ∣ (f * (X ^ P + C (p : ℤ) * h) ^ l).coeff j := by
  induction l with
  | zero => intro f j; simp
  | succ l ih =>
    intro f j
    have e : f * (X ^ P + C (p : ℤ) * h) ^ (l + 1) =
        X ^ P * (f * (X ^ P + C (p : ℤ) * h) ^ l) + C (p : ℤ) * ((f * h) * (X ^ P + C (p : ℤ) * h) ^ l) := by
      ring
    rw [e, coeff_add, coeff_X_pow_mul', coeff_C_mul]
    refine dvd_add ?_ ?_
    · split_ifs with hj
      · obtain ⟨q, rfl⟩ : ∃ q, j = q + P := ⟨j - P, by omega⟩
        rw [Nat.add_sub_cancel, Nat.add_div_right _ hP]
        exact dvd_trans (pow_dvd_pow _ (by omega)) (ih f q)
      · exact dvd_zero _
    · refine dvd_trans (pow_dvd_pow _ (show l + 1 - j / P ≤ l - j / P + 1 by omega)) ?_
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih (f * h) j)

def binomialExpansionCoeff (P rho M l : ℕ) : ℤ := (((1 + X) ^ rho * ((1 + X) ^ P - 1) ^ l : ℤ[X])).coeff M

theorem binomial_expansion_coeff_padic_dvd (p t : ℕ) (hp : p.Prime) (rho M l : ℕ) :
    (p : ℤ) ^ (l - M / p ^ t) ∣ binomialExpansionCoeff (p ^ t) rho M l := by
  have hP : 0 < p ^ t := pow_pos hp.pos t

  obtain ⟨h, hh⟩ : ∃ h : ℤ[X], (1 + X) ^ (p ^ t) - 1 = X ^ (p ^ t) + C (p : ℤ) * h := by
    have hd : C (p : ℤ) ∣ ((1 + X) ^ (p ^ t) - 1 - X ^ (p ^ t) : ℤ[X]) := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      simp only [coeff_sub, coeff_one_add_X_pow, coeff_one, coeff_X_pow]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [hP.ne']
        rw [if_neg (ne_of_lt hP)]
        exact dvd_zero _
      · by_cases hiP : i = p ^ t
        · subst hiP
          simp [hP.ne']
          rw [if_neg (by simp [hp.ne_zero])]
          exact dvd_zero _
        · by_cases hlt : i < p ^ t
          · have hdv := hp.dvd_choose_pow hi.ne' hiP
            simp only [if_neg hi.ne', if_neg hiP, sub_zero]
            exact_mod_cast hdv
          · rw [Nat.choose_eq_zero_of_lt (by omega)]
            simp [hi.ne', hiP]
    obtain ⟨h, hh⟩ := hd
    exact ⟨h, by rw [← hh]; ring⟩
  unfold binomialExpansionCoeff
  rw [hh]
  exact coeff_binomial_power_divisibility p (p ^ t) hP h l _ M

theorem binomial_expansion_coeff_zero_of_gt (P rho M l : ℕ) (h : M < l) : binomialExpansionCoeff P rho M l = 0 := by
  unfold binomialExpansionCoeff
  obtain ⟨q, hq⟩ : X ∣ ((1 + X) ^ P - 1 : ℤ[X]) := by
    rw [X_dvd_iff]
    simp [coeff_one_add_X_pow]
  rw [hq, mul_pow, show (1 + X : ℤ[X]) ^ rho * (X ^ l * q ^ l) = X ^ l * ((1 + X) ^ rho * q ^ l) by ring,
    coeff_X_pow_mul', if_neg (by omega)]

theorem binomial_expansion_coeff_zero_of_deg (P rho M l : ℕ) (h : rho + P * l < M) : binomialExpansionCoeff P rho M l = 0 := by
  unfold binomialExpansionCoeff
  apply coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt ?_ h
  have h1 : ((1 + X : ℤ[X])).natDegree ≤ 1 := (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
  have h2 : ((1 + X : ℤ[X]) ^ P - 1).natDegree ≤ P := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    exact natDegree_pow_le.trans ((Nat.mul_le_mul_left P h1).trans (by simp))
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · exact natDegree_pow_le.trans ((Nat.mul_le_mul_left rho h1).trans (by simp))
  · exact natDegree_pow_le.trans ((Nat.mul_le_mul_left l h2).trans (le_of_eq (mul_comm _ _)))

theorem choose_shift_binomial_expansion (P rho M e : ℕ) :
    (((rho + P * e).choose M : ℕ) : ℤ) = ∑ l ∈ range (M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by

  have hpoly : ((1 + X : ℤ[X])) ^ (rho + P * e) =
      ∑ l ∈ range (e + 1), C ((e.choose l : ℕ) : ℤ) * ((1 + X) ^ rho * ((1 + X) ^ P - 1) ^ l) := by
    rw [pow_add, pow_mul, show ((1 + X : ℤ[X]) ^ P) = ((1 + X) ^ P - 1) + 1 by ring,
      add_pow ((1 + X : ℤ[X]) ^ P - 1) 1 e, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [one_pow, mul_one, C_eq_natCast, add_sub_cancel_right]
    ring
  have hc := congrArg (fun q : ℤ[X] => q.coeff M) hpoly
  simp only [coeff_one_add_X_pow, finsetSum_coeff, coeff_C_mul] at hc
  rw [hc]
  calc ∑ l ∈ range (e + 1), ((e.choose l : ℕ) : ℤ) * ((1 + X : ℤ[X]) ^ rho * ((1 + X) ^ P - 1) ^ l).coeff M
      = ∑ l ∈ range (e + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) :=
        Finset.sum_congr rfl (fun l _ => by rw [mul_comm]; rfl)
    _ = ∑ l ∈ range (e + M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)
        simp only [Finset.mem_range] at hl hn
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    _ = ∑ l ∈ range (M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by
        refine (Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)).symm
        simp only [Finset.mem_range] at hl hn
        rw [binomial_expansion_coeff_zero_of_gt P rho M l (by omega)]
        simp

theorem derivative_digit_expansion (D : Formalism.BasicNotions.D7) : DerivativeDigitExpansion D := by
  intro p hp _ t σ _ rho M _ c
  classical
  have hP : 0 < p ^ t := pow_pos hp.pos t
  let a : σ → ℕ → ℤ := fun k l => binomialExpansionCoeff (p ^ t) (rho k) (M k) l

  let good : (σ → ℕ) → Prop := fun l => (∀ k, M k ≤ rho k + p ^ t * l k) ∧ ∑ k, (l k - M k / p ^ t) < c
  let B : Finset (σ → ℕ) := Fintype.piFinset (fun k => range (M k + 1))
  refine ⟨B.filter good, fun l => ∏ k, a k (l k), ?_, ?_, ?_⟩
  · intro l hl
    have hl' := (Finset.mem_filter.1 hl).2.2
    have h1 : ∑ k, l k ≤ ∑ k, (l k - M k / p ^ t) + ∑ k, M k / p ^ t := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun k _ => le_tsub_add)
    have h2 : (∑ k, M k / p ^ t) ≤ (∑ k, M k) / p ^ t := by
      rw [Nat.le_div_iff_mul_le hP, Finset.sum_mul]
      exact Finset.sum_le_sum (fun k _ => Nat.div_mul_le_self _ _)
    have h3 : ((((∑ k, M k) / p ^ t : ℕ)) : ℝ) ≤ ((∑ k, M k : ℕ) : ℝ) / ((p ^ t : ℕ) : ℝ) := Nat.cast_div_le
    have h4 : ∑ k, l k ≤ c + (∑ k, M k) / p ^ t := by omega
    have h5 : ((∑ k, l k : ℕ) : ℝ) ≤ (c : ℝ) + ((((∑ k, M k) / p ^ t : ℕ)) : ℝ) := by exact_mod_cast h4
    linarith
  · intro l hl k
    exact (Finset.mem_filter.1 hl).2.1 k
  · intro e'
    have hexp : ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) =
        ∑ l ∈ B, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)) := by
      calc ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ)
          = ∏ k, ∑ j ∈ range (M k + 1), a k j * (((e' k).choose j : ℕ) : ℤ) :=
            Finset.prod_congr rfl (fun k _ => choose_shift_binomial_expansion (p ^ t) (rho k) (M k) (e' k))
        _ = _ := Finset.prod_univ_sum _ _
    have hT : ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ) =
        ∑ l ∈ B.filter good, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)) :=
      Finset.sum_congr rfl (fun l _ => Finset.prod_mul_distrib.symm)
    have hsplit := Finset.sum_filter_add_sum_filter_not B good
      (fun l => ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)))
    show (p : ℤ) ^ c ∣ ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) -
      ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ)
    rw [hexp, hT, ← hsplit, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro l hl
    have hng := (Finset.mem_filter.1 hl).2
    rw [Finset.prod_mul_distrib]
    apply Dvd.dvd.mul_right
    by_cases hdeg : ∀ k, M k ≤ rho k + p ^ t * l k
    · have hc : c ≤ ∑ k, (l k - M k / p ^ t) := by
        by_contra hh
        exact hng ⟨hdeg, by omega⟩
      refine dvd_trans (pow_dvd_pow _ hc) ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun k _ => binomial_expansion_coeff_padic_dvd p t hp (rho k) (M k) (l k))
    · push_neg at hdeg
      obtain ⟨k, hk⟩ := hdeg
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (binomial_expansion_coeff_zero_of_deg (p ^ t) (rho k) (M k) (l k) hk)]
      exact dvd_zero _

theorem unit_product_eq_choose (P n rho : ℕ) : dUnit P n rho = (((rho + P * n).choose rho : ℕ) : ℚ) := by
  induction rho with
  | zero => simp [dUnit]
  | succ r ih =>
    show (∏ y ∈ Finset.Icc 1 (r + 1), (1 + (P : ℚ) * n / y)) = _
    rw [Finset.prod_Icc_succ_top (by omega)]
    have ih' : (∏ y ∈ Finset.Icc 1 r, (1 + (P : ℚ) * n / y)) = (((r + P * n).choose r : ℕ) : ℚ) := ih
    rw [ih', show r + 1 + P * n = r + P * n + 1 by ring]

    have hc : (((r + P * n + 1 : ℕ) : ℚ)) * (((r + P * n).choose r : ℕ) : ℚ) =
        (((r + P * n + 1).choose (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (r + P * n) r
    have hr : ((r : ℚ) + 1) ≠ 0 := by positivity
    push_cast at hc ⊢
    field_simp
    linear_combination hc

theorem hdU_proved {p : ℕ} (hp : p.Prime) : HdU p := by
  intro t rho hrho
  refine ⟨fun l => binomialExpansionCoeff (p ^ (t + 1)) rho rho l, fun n => ?_, fun l => ?_⟩
  · rw [unit_product_eq_choose]
    exact_mod_cast choose_shift_binomial_expansion (p ^ (t + 1)) rho rho n
  · have h := binomial_expansion_coeff_padic_dvd p (t + 1) hp rho rho l
    rw [Nat.div_eq_of_lt hrho, Nat.sub_zero] at h
    exact h

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Wt

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem operator_pow_shifts_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (a b : Fin n) (ν : Fin n → ℤ) (k : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : ((E a b) ^ k) x ∈ weightSp E (ν + (k : ℤ) • rootW a b) := by
  unfold OperatorsShiftWeightsByRoots at hs
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h1 := hs a b _ _ ih
    convert h1 using 2
    rw [Nat.cast_succ, add_smul, one_smul, add_assoc]

end Wt

section Lattice

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem binomial_subring_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    (u : Module.End (KK O) V) (hu : u ∈ binomialDiagonalSubring E) : ∀ x ∈ M, u x ∈ M := by
  unfold binomialDiagonalSubring at hu
  unfold UZStable at hM
  induction hu using Subring.closure_induction with
  | mem u hu => obtain ⟨a, k, rfl⟩ := hu; exact hM _ (Or.inr ⟨a, k, rfl⟩)
  | zero => intro x _; simp
  | one => intro x hx; simpa using hx
  | add u v _ _ hu hv => intro x hx; rw [LinearMap.add_apply]; exact M.add_mem (hu x hx) (hv x hx)
  | neg u _ hu => intro x hx; rw [LinearMap.neg_apply]; exact M.neg_mem (hu x hx)
  | mul u v _ _ hu hv => intro x hx; rw [Module.End.mul_apply]; exact hu _ (hv x hx)

end Lattice

end Formalism.MainNotions.G.GLWeightTheory
end
end
