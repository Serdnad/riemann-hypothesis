module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle012
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
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
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Artinian.Ring

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private lemma order_of_mem_sq {O σ : Type} [CommRing O] (I : Ideal (MvPowerSeries σ O))
    (hI : ∀ f ∈ I, constantCoeff f = 0) : ∀ f ∈ I ^ 2, ((2 : ℕ) : ℕ∞) ≤ f.order := by
  intro x hx
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
  · refine le_trans ?_ le_order_mul
    have h := add_le_add (one_le_order_iff_constCoeff_eq_zero.2 (hI a ha))
      (one_le_order_iff_constCoeff_eq_zero.2 (hI b hb))
    rwa [one_add_one_eq_two] at h
  · intro f g hf hg
    exact le_trans (le_min hf hg) min_order_le_add

private lemma mem_sq_of_coeff {O σ : Type} [CommRing O] [Fintype σ] (I : Ideal (MvPowerSeries σ O))
    (hI : ∀ i, (X i : MvPowerSeries σ O) ∈ I) (f : MvPowerSeries σ O)
    (hf : ∀ m : σ →₀ ℕ, m.degree < 2 → coeff m f = 0) : f ∈ I ^ 2 := by
  classical
  have key : ∃ μ : Finset (σ →₀ ℕ), (μ : Set _) ⊆ {m : σ →₀ ℕ | 2 ≤ m.degree} ∧
      ∀ f : MvPowerSeries σ O, (∀ m, m ∉ {m : σ →₀ ℕ | 2 ≤ m.degree} → coeff m f = 0) →
      ∃ b : (σ →₀ ℕ) → MvPowerSeries σ O, (∀ m, b m ∈ wtPart O (fun _ : σ => (0 : ℤ)) 0) ∧
        f = ∑ m ∈ μ, b m * monomial m 1 :=
    part_span O (MvPowerSeries σ O) ℤ (WPres.free O fun _ : σ => (0 : ℤ))
      {m : σ →₀ ℕ | 2 ≤ m.degree} 0 (fun (m : σ →₀ ℕ) _ => by
        show Finsupp.weight (fun _ : σ => (0 : ℤ)) m = 0
        simp [Finsupp.weight_apply, Finsupp.sum])
  obtain ⟨μ, hμ, hs⟩ := key
  obtain ⟨b, -, hb⟩ := hs f (fun m hm => hf m (not_le.1 hm))
  rw [hb]
  refine Ideal.sum_mem _ fun m hm => Ideal.mul_mem_left _ _ ?_
  have hm2 : 2 ≤ m.degree := hμ hm
  refine Ideal.pow_le_pow_right hm2 ?_
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hI i) _

private lemma low_degree {σ : Type} (m : σ →₀ ℕ) (hm : m.degree < 2) : m = 0 ∨ ∃ i, m = Finsupp.single i 1 := by
  rcases (show m.degree = 0 ∨ m.degree = 1 by omega) with h | h
  · exact Or.inl ((Finsupp.degree_eq_zero_iff m).1 h)
  · have : m ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]; exact h
    obtain ⟨i, hi⟩ := this
    exact Or.inr ⟨i, hi.symm⟩

theorem UpperTheory.mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero :
    ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) [Fintype σ] (wt : σ → ℤ) (f : FA O wt),
        f ∈ satSq (x0 O wt) ↔ constantCoeff (ser f) = 0 ∧ ∀ i, coeff (Finsupp.single i 1) (ser f) = 0 := by
  intro O _ _ σ _ wt f
  classical
  have hk := (ker_pow O (MvPowerSeries σ O) ℤ (WPres.free O wt) (freeOrigin O wt) 2).1
  have ho : ∀ g : MvPowerSeries σ O, (WPres.free O wt).origin (freeOrigin O wt) g = constantCoeff g :=
    fun g => (WPres.free O wt).origin_π (freeOrigin O wt) g
  have hiff : ∀ g : FA O wt, g ∈ RingHom.ker (x0 O wt) ^ 2 ↔
      ser g ∈ RingHom.ker ((WPres.free O wt).origin (freeOrigin O wt)) ^ 2 := fun g => by
    show g ∈ RingHom.ker ((WPres.free O wt).originA (freeOrigin O wt)) ^ 2 ↔ _
    rw [← hk]
    rfl
  constructor
  · rintro ⟨c, hc, hf⟩
    have h2 := order_of_mem_sq _ (fun g hg => by rw [← ho]; exact hg) _ ((hiff _).1 hf)
    have h3 : ∀ m : σ →₀ ℕ, m.degree < 2 → coeff m (ser f) = 0 := fun m hm => by
      have h4 : coeff m (c • ser f) = 0 :=
        coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hm) h2)
      rw [map_smul, smul_eq_mul] at h4
      exact (mul_eq_zero.1 h4).resolve_left hc
    exact ⟨h3 0 (by simp), fun i => h3 _ (by simp)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul, hiff]
    refine mem_sq_of_coeff _ (fun i => ?_) _ (fun m hm => ?_)
    · rw [RingHom.mem_ker, ho]; simp
    · rcases low_degree m hm with rfl | ⟨i, rfl⟩
      · exact h0
      · exact h1 i
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

private theorem tc_conj_mat {R D : Type} [CommRing R] [Group D] (r : D →* GG (m := 3) (R := R)) (h : GL (Fin 3) R) (g : D)
    (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

private theorem tc_res {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h) :
    (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 ∧
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
  have h1 : (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hh a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases e : a = b <;> simp [Matrix.one_apply, e]
  refine ⟨h1, ?_⟩
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h).map (residue R) = 1 := by
    rw [Units.inv_mul]; simp
  rwa [Matrix.map_mul, h1, Matrix.mul_one] at this

private theorem tc_res_conj {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h)
    (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    residue R ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h) a b) = residue R (X a b) := by
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h).map (residue R) = X.map (residue R) := by
    rw [Matrix.map_mul, Matrix.map_mul, (tc_res h hh).1, (tc_res h hh).2, Matrix.one_mul, Matrix.mul_one]
  exact congrFun (congrFun this a) b

private theorem tc_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : O) - 1) := by
    rw [show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring] at ht
    exact isUnit_of_mul_isUnit_left ht
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have := ht.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-(t : O)) * e
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have := h1.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-1 : O) * e
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg,
      Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption

private theorem tc_up {R : Type} [CommRing R] (Δ k U : Matrix (Fin 3) (Fin 3) R) (e : Δ * k = k * U)
    (hΔ : Δ.IsDiag) (hU : ∀ a b, wt a b < 0 → U a b = 0) (hu : ∀ a b, a ≠ b → IsUnit (Δ a a - U b b)) :
    ∀ a b, wt a b < 0 → k a b = 0 := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have d10 : Δ 1 0 = 0 := hΔ (by decide)
  have d12 : Δ 1 2 = 0 := hΔ (by decide)
  have d20 : Δ 2 0 = 0 := hΔ (by decide)
  have d21 : Δ 2 1 = 0 := hΔ (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, d10, d12, d20, d21] at e10 e20 e21
  have k10 : k 1 0 = 0 := (hu 1 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e10)
  have k20 : k 2 0 = 0 := (hu 2 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e20)
  have k21 : k 2 1 = 0 := (hu 2 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e21; linear_combination e21)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem tc_low {R : Type} [CommRing R] (Δ k U : Matrix (Fin 3) (Fin 3) R) (e : Δ * k = k * U)
    (hΔ : Δ.IsDiag) (hU : ∀ a b, 0 < wt a b → U a b = 0) (hu : ∀ a b, a ≠ b → IsUnit (Δ a a - U b b)) :
    ∀ a b, 0 < wt a b → k a b = 0 := by
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  have u01 := hU 0 1 (by decide)
  have u02 := hU 0 2 (by decide)
  have u12 := hU 1 2 (by decide)
  have d10 : Δ 1 0 = 0 := hΔ (by decide)
  have d12 : Δ 1 2 = 0 := hΔ (by decide)
  have d02 : Δ 0 2 = 0 := hΔ (by decide)
  have d01 : Δ 0 1 = 0 := hΔ (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, d10, d12, d02, d01] at e01 e02 e12
  have k12 : k 1 2 = 0 := (hu 1 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e12)
  have k02 : k 0 2 = 0 := (hu 0 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e02)
  have k01 : k 0 1 = 0 := (hu 0 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k02] at e01; linear_combination e01)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem tc_up' {R : Type} [CommRing R] (M k U : Matrix (Fin 3) (Fin 3) R) (e : M * k = k * U)
    (hk : ∀ a b, wt a b < 0 → k a b = 0) (hU : ∀ a b, wt a b < 0 → U a b = 0) (hu : ∀ a, IsUnit (k a a)) :
    (∀ a b, wt a b < 0 → M a b = 0) ∧ ∀ a, M a a = U a a := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  have e22 := congrFun (congrFun e 2) 2
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have k10 := hk 1 0 (by decide)
  have k20 := hk 2 0 (by decide)
  have k21 := hk 2 1 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, k10, k20, k21] at e10 e20 e21 e00 e11 e22
  have m10 : M 1 0 = 0 := (hu 0).mul_left_eq_zero.1 (by linear_combination e10)
  have m20 : M 2 0 = 0 := (hu 0).mul_left_eq_zero.1 (by linear_combination e20)
  have m21 : M 2 1 = 0 := (hu 1).mul_left_eq_zero.1 (by rw [m20] at e21; linear_combination e21)
  have m00 : M 0 0 = U 0 0 := sub_eq_zero.1 ((hu 0).mul_left_eq_zero.1 (by linear_combination e00))
  have m11 : M 1 1 = U 1 1 := sub_eq_zero.1 ((hu 1).mul_left_eq_zero.1 (by
    rw [m10] at e11; linear_combination e11))
  have m22 : M 2 2 = U 2 2 := sub_eq_zero.1 ((hu 2).mul_left_eq_zero.1 (by
    rw [m20, m21] at e22; linear_combination e22))
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)
  · fin_cases a <;> assumption

private theorem tc_low' {R : Type} [CommRing R] (M k U : Matrix (Fin 3) (Fin 3) R) (e : M * k = k * U)
    (hk : ∀ a b, 0 < wt a b → k a b = 0) (hU : ∀ a b, 0 < wt a b → U a b = 0) (hu : ∀ a, IsUnit (k a a)) :
    ∀ a b, 0 < wt a b → M a b = 0 := by
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  have u01 := hU 0 1 (by decide)
  have u02 := hU 0 2 (by decide)
  have u12 := hU 1 2 (by decide)
  have k01 := hk 0 1 (by decide)
  have k02 := hk 0 2 (by decide)
  have k12 := hk 1 2 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, k01, k02, k12] at e01 e02 e12
  have m12 : M 1 2 = 0 := (hu 2).mul_left_eq_zero.1 (by linear_combination e12)
  have m02 : M 0 2 = 0 := (hu 2).mul_left_eq_zero.1 (by linear_combination e02)
  have m01 : M 0 1 = 0 := (hu 1).mul_left_eq_zero.1 (by rw [m02] at e01; linear_combination e01)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem tc_rel {R : Type} [CommRing R] (h h' : GL (Fin 3) R) (X : Matrix (Fin 3) (Fin 3) R) :
    (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h) * (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') =
      (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') *
        (((h'⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h') := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (h : Matrix (Fin 3) (Fin 3) R), ← Matrix.mul_assoc (h' : Matrix (Fin 3) (Fin 3) R),
    Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.one_mul]

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.cond_iff_canon :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG (m := 3) (R := R)) (x : D) (h : GL (Fin 3) R), Red η Ψ r → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → Canon (r x).mat h →
      (CondT η Ψ I r ↔ TriIn η Ψ I r h) ∧ (CondD η Ψ I r ↔ DiagIn η Ψ I r h) := by
  intro O R D _ _ _ _ _ _ η Ψ I r x h hr hx hΨ hc
  have cm : ∀ (h : GL (Fin 3) R) (g : D), η g = 1 →
      (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h :=
    fun h g hg => tc_conj_mat r h g ((hr.mult g).trans hg)
  have hX : ∀ a, residue R ((r x).mat a a) = residue R (algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O)) := by
    intro a
    have := (residue_eq_zero_iff _).2 (hr.red x a a)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this]
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]
  have hu : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a b, a ≠ b →
      IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h) a a -
        (((h'⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h') b b) := by
    intro h' hh' a b hab
    rw [← residue_ne_zero_iff_isUnit, map_sub, tc_res_conj h hc.hat, tc_res_conj h' hh', hX, hX, ← map_sub,
      ← map_sub, residue_ne_zero_iff_isUnit]
    exact (tc_unit (Ψ x) hΨ a b hab).map _
  have hk : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a,
      IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') a a) := by
    intro h' hh' a
    have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h').map (residue R) = 1 := by
      rw [Matrix.map_mul, (tc_res h hc.hat).2, (tc_res h' hh').1, Matrix.one_mul]
    have := congrFun (congrFun this a) a
    rw [Matrix.map_apply, Matrix.one_apply_eq] at this
    rw [← residue_ne_zero_iff_isUnit, this]
    exact one_ne_zero
  have hT : ∀ h' : GL (Fin 3) R, InHat h' → TriIn η Ψ I r h' → TriIn η Ψ I r h := by
    intro h' hh' ht
    have k1 := tc_up _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.tri x hx) (hu h' hh')
    have k2 := fun g (hg : η g = 1) => tc_up' _ _ _ (tc_rel h h' (r g).mat) k1
      (by rw [← cm h' g hg]; exact ht.tri g hg) (hk h' hh')
    refine ⟨fun g hg => ?_, fun s hs hg a => ?_⟩
    · rw [cm h g hg]; exact (k2 g hg).1
    · rw [cm h s hg, (k2 s hg).2, ← cm h' s hg]; exact ht.ine s hs hg a
  refine ⟨⟨fun ⟨h', hh', ht⟩ => hT h' hh' ht, fun ht => ⟨h, hc.hat, ht⟩⟩,
    ⟨fun ⟨h', hh', ht⟩ => ⟨hT h' hh' ht.toTriIn, fun g hg => ?_⟩, fun ht => ⟨h, hc.hat, ht⟩⟩⟩
  have k1 := tc_low _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.low x hx) (hu h' hh')
  rw [cm h g hg]
  exact tc_low' _ _ _ (tc_rel h h' (r g).mat) k1 (by rw [← cm h' g hg]; exact ht.low g hg) (hk h' hh')
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
open LaurentPolynomial

private theorem exists_coact {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] :
    ∃ φ : R →+* R[T;T⁻¹], ∀ (j : ℤ) (x : R), x ∈ 𝒜 j ↔ φ x = C x * T j := by
  let t : Multiplicative ℤ →* (R[T;T⁻¹])ˣ := (AddMonoidAlgebra.of R ℤ).toHomUnits
  let φ : R →ₐ[O] R[T;T⁻¹] := act 𝒜 t (IsScalarTower.toAlgHom O R R[T;T⁻¹])
  have h1 : ∀ j x, x ∈ 𝒜 j → φ x = C x * T j := fun j x hx => by
    rw [mul_comm]
    exact act_of_mem 𝒜 t _ hx
  have h2 : ∀ x j, (φ x).coeff j = (DirectSum.decompose 𝒜 x j : R) := by
    intro x j
    induction x using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous i m =>
      rw [h1 i m m.2, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
      by_cases hij : i = j
      · subst hij
        rw [DirectSum.decompose_of_mem_same 𝒜 m.2, Finsupp.single_eq_same]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 m.2 hij, Finsupp.single_eq_of_ne' hij]
    | add a b ha hb => simp [ha, hb]
  refine ⟨φ, fun j x => ⟨h1 j x, fun hx => ?_⟩⟩
  have h3 := h2 x j
  have hx' : φ x = C x * T j := hx
  rw [hx', ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at h3
  rw [h3]
  exact Subtype.property _

private theorem eig_unique {S n : Type} [CommRing S] [Fintype n] [DecidableEq n]
    (X h g h' : Matrix n n S) (l l' : n → S) (hg : h * g = 1) (gh : g * h = 1)
    (e : X * h = h * diagonal l) (e' : X * h' = h' * diagonal l')
    (o : ∀ a, h a a = 1) (o' : ∀ a, h' a a = 1) (u : ∀ a b, a ≠ b → IsUnit (l a - l' b)) : h' = h := by
  have e1 : g * X = diagonal l * g := by
    calc g * X = g * (X * h) * g := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, Matrix.mul_one]
      _ = _ := by rw [e, ← Matrix.mul_assoc, gh, Matrix.one_mul]
  have e2 : diagonal l * (g * h') = (g * h') * diagonal l' := by
    rw [← Matrix.mul_assoc, ← e1, Matrix.mul_assoc, e', Matrix.mul_assoc]
  have e3 : (g * h').IsDiag := by
    intro a b hab
    have := congrFun (congrFun e2 a) b
    rw [diagonal_mul, mul_diagonal] at this
    exact (u a b hab).mul_right_eq_zero.1 (by rw [sub_mul, this]; ring)
  have e4 : h' = h * diagonal (diag (g * h')) := by
    rw [e3.diagonal_diag, ← Matrix.mul_assoc, hg, Matrix.one_mul]
  have e5 : diag (g * h') = fun _ => 1 := by
    funext a
    have := congrFun (congrFun e4 a) a
    rw [mul_diagonal, o, o', one_mul] at this
    exact this.symm
  rw [e4, e5, diagonal_one, Matrix.mul_one]

end

open LaurentPolynomial in
theorem UpperTheory.V.UnitaryThreeInertia.canon_graded :
    ∀ {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Finite R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → GrMat 𝒜 X → Canon X h → GrMat 𝒜 h.val ∧ GrMat 𝒜 (h⁻¹).val := by
  intro O R _ _ _ _ _ _ 𝒜 _ X h hu hX hc
  obtain ⟨φ, hφ⟩ := exists_coact 𝒜
  have hnil : ∀ x ∈ maximalIdeal R, IsNilpotent x := by
    intro x hx
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact this
  set l : Fin 3 → R := diag ((h⁻¹).val * X * h.val) with hl
  have e : X * h.val = h.val * diagonal l := by
    rw [hl, hc.diag.diagonal_diag, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hlX : ∀ a, IsNilpotent (l a - X a a) := by
    intro a
    apply hnil
    have e1 : X * (h.val - 1) = h.val * diagonal l - X := by rw [Matrix.mul_sub, e, Matrix.mul_one]
    have e2 := congrFun (congrFun e1 a) a
    rw [Matrix.sub_apply, mul_diagonal, hc.one, one_mul] at e2
    rw [← e2, Matrix.mul_apply]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hc.hat c a)
  let D : Matrix (Fin 3) (Fin 3) R[T;T⁻¹] := diagonal fun a => T (wt1 a)
  let D' : Matrix (Fin 3) (Fin 3) R[T;T⁻¹] := diagonal fun a => T (-wt1 a)
  have DD : D * D' = 1 := by
    simp only [D, D', diagonal_mul_diagonal, ← T_add, add_neg_cancel, T_zero, diagonal_one]
  have DD' : D' * D = 1 := by
    simp only [D, D', diagonal_mul_diagonal, ← T_add, neg_add_cancel, T_zero, diagonal_one]
  have ent : ∀ (M : Matrix (Fin 3) (Fin 3) R[T;T⁻¹]) a b, (D * M * D') a b = M a b * T (wt a b) := by
    intro M a b
    simp only [D, D', mul_diagonal, diagonal_mul, wt, T_sub]
    ring
  have key : ∀ M : Matrix (Fin 3) (Fin 3) R, GrMat 𝒜 M ↔ M.map φ = D * M.map C * D' := by
    intro M
    constructor
    · intro hM
      ext1 a b
      rw [ent]
      exact (hφ _ _).1 (hM a b)
    · intro hM a b
      have := congrFun (congrFun hM a) b
      rw [ent] at this
      exact (hφ _ _).2 this
  have inv1 : ∀ f : R →+* R[T;T⁻¹], h.val.map f * (h⁻¹).val.map f = 1 := fun f => by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one f (map_zero f) (map_one f)]
  have inv2 : ∀ f : R →+* R[T;T⁻¹], (h⁻¹).val.map f * h.val.map f = 1 := fun f => by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one f (map_zero f) (map_one f)]
  have emap : ∀ f : R →+* R[T;T⁻¹], X.map f * h.val.map f = h.val.map f * diagonal fun a => f (l a) := fun f => by
    rw [← Matrix.map_mul, e, Matrix.map_mul, diagonal_map (map_zero f)]
  have can : ∀ M N : Matrix (Fin 3) (Fin 3) R[T;T⁻¹], (D * M * D') * (D * N * D') = D * (M * N) * D' := by
    intro M N
    calc _ = D * M * (D' * D) * N * D' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [DD', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have main : D * h.val.map C * D' = h.val.map φ := by
    refine eig_unique (X.map φ) (h.val.map φ) ((h⁻¹).val.map φ) _ (fun a => φ (l a)) (fun a => C (l a))
      (inv1 φ) (inv2 φ) (emap φ) ?_ (fun a => by simp [hc.one]) (fun a => by rw [ent]; simp [hc.one, wt]) ?_
    · rw [(key X).1 hX, can, emap C]
      have hcomm : (diagonal fun a => C (l a)) * D' = D' * diagonal fun a => C (l a) := by
        simp only [D', diagonal_mul_diagonal, mul_comm]
      simp only [Matrix.mul_assoc]
      rw [hcomm]
    · intro a b hab
      have hXa : φ (X a a) = C (X a a) := by
        have := (hφ _ _).1 (hX a a)
        simpa [wt] using this
      have h1 : IsNilpotent (φ (l a - X a a) - C (l b - X b b)) :=
        (Commute.all _ _).isNilpotent_sub ((hlX a).map φ) ((hlX b).map C)
      have h2 := h1.isUnit_add_right_of_commute ((hu a b hab).map C) (Commute.all _ _)
      convert h2 using 1
      simp only [map_sub, hXa]
      ring
  refine ⟨(key _).2 main.symm, (key _).2 ?_⟩
  have h3 : h.val.map φ * (D * (h⁻¹).val.map C * D') = 1 := by
    rw [← main, can, inv1, Matrix.mul_one, DD]
  calc (h⁻¹).val.map φ = (h⁻¹).val.map φ * (h.val.map φ * (D * (h⁻¹).val.map C * D')) := by
        rw [h3, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, inv2, Matrix.one_mul]
end
