module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PjCong
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExOm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExTop
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

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i then 1 else -1

theorem sgn_mul_self {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : sgn ε i * sgn ε i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem star_sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : star (sgn ε i) = sgn ε i := by
  unfold sgn
  split_ifs <;> simp

theorem star_I' : star Complex.I = -Complex.I := Complex.conj_I

theorem norm_sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : ‖sgn ε i‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem lie_apply {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M) i j = star (M j i) * sgn ε j + sgn ε i * M i j := by
  simp only [Matrix.add_apply, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, sgn]

def cpx {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a : Fin k) (b : Fin m) : ℂ :=
  ⟨u (a, b, true), u (a, b, false)⟩

theorem cpx_add {k m : ℕ} (u v : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a b) :
    cpx (u + v) a b = cpx u a b + cpx v a b := by
  apply Complex.ext <;> simp [cpx]

theorem cpx_smul {k m : ℕ} (c : ℝ) (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a b) :
    cpx (c • u) a b = (c : ℂ) * cpx u a b := by
  apply Complex.ext <;> simp [cpx]

theorem cpx_eq {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) :
    Matrix.of (cpx u) = Matrix.of ((reimE (r := k) (m := m)).symm u) := rfl

theorem cpx_reim {k m : ℕ} (Y : Matrix (Fin k) (Fin m) ℂ) (a b) : cpx (reim Y) a b = Y a b := by
  apply Complex.ext <;> simp [cpx, reim]

theorem norm_cpx_sq {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) :
    ‖u‖ ^ 2 = ∑ a, ∑ b, ‖cpx u a b‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [cpx, Real.norm_eq_abs, sq]

def r2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem inv_sqrt_two_mul : r2 * (Real.sqrt 2 : ℂ) = 1 := by
  rw [r2, ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr two_pos), Complex.ofReal_one]

theorem norm_inv_sqrt_two_sq : ‖r2‖ ^ 2 = 1 / 2 := by
  rw [r2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

variable {n k m : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) (eS : Fin k ≃ {i // i ∈ S})
  (eU : Fin m ≃ {i // i ∉ S}) {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)

def xiF (z : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if hi : i ∈ S then (if hj : j ∈ S then 0 else r2 * cpx z.1 (eS.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))
    else (if hj : j ∈ S then -(sgn ε i * sgn ε j) * star (r2 * cpx z.1 (eS.symm ⟨j, hj⟩) (eU.symm ⟨i, hi⟩))
      else sgn ε i * Complex.I * H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))

def xiL : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := xiF ε S eS eU H
  map_add' a b := by
    ext i j
    simp only [xiF, Matrix.add_apply]
    split_ifs <;> (try simp [cpx_add]) <;> ring
  map_smul' c z := by
    ext i j
    simp only [xiF, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> (try simp [cpx_smul, Complex.real_smul, Complex.conj_ofReal]) <;> ring

theorem xi_SS (z) (a b : Fin k) : xiF ε S eS eU H z (eS a) (eS b) = 0 := by
  simp [xiF, (eS a).2, (eS b).2]

theorem xi_SU (z) (a : Fin k) (b : Fin m) : xiF ε S eS eU H z (eS a) (eU b) = r2 * cpx z.1 a b := by
  simp [xiF, (eS a).2, (eU b).2]

theorem xi_US (z) (a : Fin m) (b : Fin k) :
    xiF ε S eS eU H z (eU a) (eS b) = -(sgn ε (eU a) * sgn ε (eS b)) * star (r2 * cpx z.1 b a) := by
  simp [xiF, (eU a).2, (eS b).2]

theorem xi_UU (z) (a b : Fin m) : xiF ε S eS eU H z (eU a) (eU b) = sgn ε (eU a) * Complex.I * H z.2 a b := by
  simp [xiF, (eU a).2, (eU b).2]

theorem sum_split {M : Type} [AddCommMonoid M] (f : Fin n → M) : ∑ i, f i = ∑ a, f (eS a) + ∑ a, f (eU a) := by
  have h : ∑ i, f i = ∑ x : ↥S, f ↑x + ∑ x : {i // i ∉ S}, f ↑x := by
    convert (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S) f).symm
  exact h.trans (congrArg₂ (· + ·) (eS.sum_comp (fun x => f x)).symm (eU.sum_comp (fun x => f x)).symm)

theorem xi_norm (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (z) :
    ∑ i, ∑ j, ‖xiF ε S eS eU H z i j‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simp only [sum_split S eS eU, xi_SS, xi_SU, xi_US, xi_UU, norm_zero, norm_mul, norm_neg, norm_star,
    norm_sgn, Complex.norm_I, mul_pow, norm_inv_sqrt_two_sq, one_mul, mul_one]
  rw [norm_cpx_sq z.1, ← hn z.2]
  have hc : ∑ x : Fin m, ∑ y : Fin k, ‖cpx z.1 y x‖ ^ 2 = ∑ y : Fin k, ∑ x : Fin m, ‖cpx z.1 y x‖ ^ 2 :=
    Finset.sum_comm
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hc]
  ring

theorem xi_mem (hH : ∀ t, (H t)ᴴ = H t) (z) :
    (xiF ε S eS eU H z)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * xiF ε S eS eU H z = 0 ∧
      ∀ i ∈ S, ∀ j ∈ S, xiF ε S eS eU H z i j = 0 := by
  refine ⟨?_, fun i hi j hj => by simp [xiF, hi, hj]⟩
  have hHe : ∀ a b, star (H z.2 b a) = H z.2 a b := fun a b => by
    have h := congrFun (congrFun (hH z.2) a) b
    rwa [Matrix.conjTranspose_apply] at h
  ext i j
  rw [lie_apply, Matrix.zero_apply]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [xiF, hi, hj]
  · simp only [xiF, dif_pos hi, dif_neg hj, star_mul', star_neg, star_star, star_sgn]
    linear_combination (-(sgn ε i) * (r2 * cpx z.1 (eS.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε j
  · simp only [xiF, dif_pos hj, dif_neg hi, star_mul']
    linear_combination (-(sgn ε j) * (star r2 * star (cpx z.1 (eS.symm ⟨j, hj⟩) (eU.symm ⟨i, hi⟩)))) * sgn_mul_self ε i
  · simp only [xiF, dif_neg hi, dif_neg hj, star_mul', star_sgn, star_I', hHe]
    linear_combination (Complex.I * (H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε i - (Complex.I * (H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε j

theorem xi_onto (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (ξ : Matrix (Fin n) (Fin n) ℂ)
    (h1 : ξᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * ξ = 0) (h2 : ∀ i ∈ S, ∀ j ∈ S, ξ i j = 0) :
    ∃ z, xiF ε S eS eU H z = ξ := by
  have hξ : ∀ i j, star (ξ j i) * sgn ε j + sgn ε i * ξ i j = 0 := fun i j => by
    have h := congrFun (congrFun h1 i) j
    rwa [lie_apply, Matrix.zero_apply] at h
  let u : EuclideanSpace ℝ (Fin k × Fin m × Bool) :=
    reim (Matrix.of fun a b => (Real.sqrt 2 : ℂ) * ξ (eS a) (eU b))
  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a b => -Complex.I * sgn ε (eU a) * ξ (eU a) (eU b)
  have hM : Mᴴ = M := by
    ext a b
    simp only [M, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_neg, star_I', star_sgn]
    linear_combination Complex.I * hξ (eU a) (eU b)
  obtain ⟨t, ht⟩ := hs M hM
  have e2 : ∀ w : ℂ, r2 * ((Real.sqrt 2 : ℂ) * w) = w := fun w => by rw [← mul_assoc, inv_sqrt_two_mul, one_mul]
  refine ⟨(u, t), ?_⟩
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [xiF, hi, hj, h2 i hi j hj]
  · simp only [xiF, dif_pos hi, dif_neg hj, u, cpx_reim, Matrix.of_apply, Equiv.apply_symm_apply, e2]
  · simp only [xiF, dif_neg hi, dif_pos hj, u, cpx_reim, Matrix.of_apply, Equiv.apply_symm_apply, e2]
    linear_combination (-(sgn ε i)) * hξ i j + ξ i j * sgn_mul_self ε i
  · simp only [xiF, dif_neg hi, dif_neg hj, ht, M, Matrix.of_apply, Equiv.apply_symm_apply]
    linear_combination (-(sgn ε i) ^ 2 * ξ i j) * Complex.I_sq + ξ i j * sgn_mul_self ε i

theorem dom_exists {ι : Type} [Fintype ι] (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ x, (L x)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * L x = 0 ∧ ∀ i ∈ S, ∀ j ∈ S, L x i j = 0)
    (hnL : ∀ x, ∑ i, ∑ j, ‖L x i j‖ ^ 2 = ‖x‖ ^ 2)
    (hLs : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 →
      (∀ i ∈ S, ∀ j ∈ S, M i j = 0) → ∃ x, L x = M)
    (hH : ∀ t, (H t)ᴴ = H t) (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    ∃ Λ : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ ι,
      MeasurePreserving Λ volume volume ∧ ∀ z, L (Λ z) = xiF ε S eS eU H z := by
  have hxi : ∀ z, ∃ x, L x = xiL ε S eS eU H z := fun z =>
    hLs _ (xi_mem ε S eS eU H hH z).1 (xi_mem ε S eS eU H hH z).2
  let Λ := liftL L (inj_of_frob L hnL) (xiL ε S eS eU H) hxi
  have hΛ : ∀ z, L (Λ z) = xiF ε S eS eU H z := fun z => liftL_spec L (inj_of_frob L hnL) _ hxi z
  refine ⟨Λ, mp_of_isom_prod Λ (fun a b => ?_) ?_, hΛ⟩
  · rw [← hnL, hΛ]
    exact xi_norm ε S eS eU H hnH (a, b)
  · intro x
    obtain ⟨z, hz⟩ := xi_onto ε S eS eU H hsH (L x) (hL x).1 (hL x).2
    exact ⟨z, inj_of_frob L hnL ((hΛ z).trans hz)⟩

end PI.AprimeInfW
end
end

section

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Chart

variable (P Q : ℕ)

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem two_eq : (1 + 1 : Mat) = (2 : ℂ) • (1 : Mat) := (two_smul ℂ (1 : Mat)).symm

theorem cayCand_mem (g : UpqT P Q) : cayCand P Q g ∈ lieU P Q := by
  set G := UpqT.mat g with hG
  set J := HcS.UG.Jpq P Q
  have hU : Gᴴ * J * G = J := by
    have := (mem_Upq_iff P Q _).1 (toS P Q g).2
    rwa [← mat_eq] at this
  by_cases hu : IsUnit (G + 1).det
  · set K := (G + 1)⁻¹
    set X := cayCand P Q g with hX
    have hXdef : X = (1 + 1) * K * (G - 1) := rfl
    have hKG : K * (G + 1) = 1 := Matrix.nonsing_inv_mul _ hu
    have hGK : (G + 1) * K = 1 := Matrix.mul_nonsing_inv _ hu
    have hXG : X * (G + 1) = (1 + 1) * (G - 1) := by
      have e : (G - 1) * (G + 1) = (G + 1) * (G - 1) := by noncomm_ring
      rw [hXdef, Matrix.mul_assoc, Matrix.mul_assoc, e, ← Matrix.mul_assoc K, hKG, Matrix.one_mul]
    have hu' : IsUnit (G + 1)ᴴ.det := by
      rw [Matrix.det_conjTranspose]
      exact hu.star
    show Xᴴ * J + J * X = 0
    have key : (G + 1)ᴴ * (Xᴴ * J + J * X) * (G + 1) = 0 := by
      have e1 : (G + 1)ᴴ * (Xᴴ * J + J * X) * (G + 1) =
          (X * (G + 1))ᴴ * J * (G + 1) + (G + 1)ᴴ * J * (X * (G + 1)) := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
      have hJ : Jᴴ = J := Jpq_conjTranspose P Q
      have h2 : ((1 : Mat) + 1)ᴴ = 1 + 1 := by simp
      rw [e1, hXG, Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
        Matrix.conjTranspose_one]
      have e2 : (Gᴴ - 1) * (1 + 1) * J * (G + 1) + (Gᴴ + 1) * J * ((1 + 1) * (G - 1)) =
          (1 + 1) * ((1 + 1) * (Gᴴ * J * G - J)) := by noncomm_ring
      rw [e2, hU, sub_self, Matrix.mul_zero, Matrix.mul_zero]
    have e3 : Xᴴ * J + J * X =
        ((G + 1)ᴴ)⁻¹ * ((G + 1)ᴴ * (Xᴴ * J + J * X) * (G + 1)) * K := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu', Matrix.one_mul,
        Matrix.mul_assoc, hGK, Matrix.mul_one]
    rw [e3, key, Matrix.mul_zero, Matrix.zero_mul]
  · have : cayCand P Q g = 0 := by
      show (1 + 1) * (G + 1)⁻¹ * (G - 1) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.mul_zero, Matrix.zero_mul]
    rw [this]
    exact (lieU P Q).zero_mem

theorem cayInv_eq (g : UpqT P Q) : cayInv P Q g = ⟨cayCand P Q g, cayCand_mem P Q g⟩ := by
  unfold cayInv
  rw [dite_eq_left (cayCand_mem P Q g)]

end Chart

theorem cayley_inverse_iff : CayInvIff := by
  intro P Q g X h
  set G := UpqT.mat g with hG
  set Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
  rw [two_eq] at h
  have h4 : (G + 1) * ((2 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - Y) =
      (4 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    rw [add_mul, one_mul, h, show (4 : ℂ) = 2 + 2 by norm_num, add_smul]
    abel
  have hB : (G + 1) * ((1 / 4 : ℂ) • ((2 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - Y)) = 1 := by
    rw [Matrix.mul_smul, h4, smul_smul]
    norm_num
  have hu : IsUnit (G + 1).det := Matrix.isUnit_det_of_right_inverse hB
  have hGY : G * Y = (2 : ℂ) • G - ((2 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) + Y) := by
    rw [← h, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    abel
  have hXY : (G + 1) * Y = (2 : ℂ) • (G - 1) := by
    rw [add_mul, one_mul, hGY, smul_sub]
    abel
  have hc : cayCand P Q g = Y := by
    show (1 + 1) * (G + 1)⁻¹ * (G - 1) = Y
    have eY : Y = (G + 1)⁻¹ * ((G + 1) * Y) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [eY, hXY, Matrix.mul_smul, two_eq, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [cayInv_eq]
  exact Subtype.ext hc

theorem cayley_inverse_measurable : CayInvMeas := by
  intro P Q
  set O : Set (UpqT P Q) := {g | (UpqT.mat g + 1).det ≠ 0}
  have hmat : Continuous (UpqT.mat (P := P) (Q := Q)) := (isInducing_mat P Q).continuous
  have hdet : Continuous fun g : UpqT P Q => (UpqT.mat g + 1).det :=
    (hmat.add continuous_const).matrix_det
  have hO : IsOpen O := isOpen_ne_fun hdet continuous_const
  have hcand : Continuous fun g : O => cayCand P Q g := by
    have hm : Continuous fun g : O => UpqT.mat (g : UpqT P Q) := hmat.comp continuous_subtype_val
    have hd : Continuous fun g : O => (UpqT.mat (g : UpqT P Q) + 1).det :=
      hdet.comp continuous_subtype_val
    have hinv : Continuous fun g : O => (UpqT.mat (g : UpqT P Q) + 1)⁻¹ := by
      have e : (fun g : O => (UpqT.mat (g : UpqT P Q) + 1)⁻¹) =
          fun g : O => ((UpqT.mat (g : UpqT P Q) + 1).det)⁻¹ • (UpqT.mat (g : UpqT P Q) + 1).adjugate := by
        funext g
        rw [Matrix.inv_def, Ring.inverse_eq_inv']
      rw [e]
      exact (hd.inv₀ fun g => g.2).smul (hm.add continuous_const).matrix_adjugate
    exact (continuous_const.matrix_mul hinv).matrix_mul (hm.sub continuous_const)
  have hcont : ContinuousOn (cayInv P Q) O := by
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    show Continuous fun g : O => cayInv P Q g
    have e : (fun g : O => cayInv P Q g) = fun g : O => ⟨cayCand P Q g, cayCand_mem P Q g⟩ := by
      funext g
      exact cayInv_eq P Q g
    rw [e]
    exact Continuous.subtype_mk hcand _
  have hpw : O.piecewise (cayInv P Q) (fun _ => 0) = cayInv P Q := by
    funext g
    by_cases hg : g ∈ O
    · exact Set.piecewise_eq_of_mem _ _ _ hg
    · rw [Set.piecewise_eq_of_notMem _ _ _ hg]
      have hg' : ¬IsUnit (UpqT.mat g + 1).det := fun hu => hg hu.ne_zero
      rw [cayInv_eq]
      apply Subtype.ext
      show 0 = (1 + 1) * (UpqT.mat g + 1)⁻¹ * (UpqT.mat g - 1)
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hg', Matrix.mul_zero, Matrix.zero_mul]
  rw [← hpw]
  classical
  exact hcont.measurable_piecewise continuousOn_const hO.measurableSet

end HcInf
end
end
