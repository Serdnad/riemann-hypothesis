module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.ImgSec

section Alg
variable {k : Type} [CommRing k] {r : ℕ}

def e1 : Fin r → k := fun i => if (i : ℕ) = 0 then 1 else 0

theorem companionMatrixOfCoeffs_pow_mulVec_firstBasisVector (p : Fin r → k) : ∀ (j : ℕ) (hj : j < r),
    (companion p ^ j) *ᵥ e1 = Pi.single (⟨j, hj⟩ : Fin r) 1
  | 0, hj => by
    ext i; simp [e1, Pi.single_apply, Fin.ext_iff]
  | j + 1, hj => by
    rw [pow_succ', ← mulVec_mulVec, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector p j (by omega), Matrix.mulVec_single_one]
    funext i
    have hj' : j + 1 ≠ r := Nat.ne_of_lt hj
    simp [Matrix.col_apply, companion, Pi.single_apply, Fin.ext_iff, hj']

theorem mom_sec_add (a : Inv r k) (n : ℕ) (j : Fin r) :
    mom (sec a) (n + j) = (a.2.1 ᵥ* (companion a.1 ^ n)) j := by
  have h1 : mom (sec a) (n + j) = a.2.1 ⬝ᵥ ((companion a.1 ^ n) *ᵥ ((companion a.1 ^ (j : ℕ)) *ᵥ e1)) := by
    simp only [mom, sec, pow_add, ← mulVec_mulVec]; rfl
  rw [h1, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector a.1 j j.2, dotProduct_mulVec, dotProduct_single_one]

theorem hankel_apply' (a : Inv r k) (i j : Fin r) : hankel a i j = (a.2.1 ᵥ* (companion a.1 ^ (i : ℕ))) j :=
  mom_sec_add a i j

theorem hankel_isSymm (a : Inv r k) : (hankel a).IsSymm := by
  ext i j; simp [hankel, add_comm]

def hankelShift (a : Inv r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => mom (sec a) ((i : ℕ) + (j : ℕ) + 1)

theorem hankelShift_isSymm (a : Inv r k) : (hankelShift a).IsSymm := by
  ext i j; simp [hankelShift]; ring_nf

theorem hankel_mul_companion (a : Inv r k) : hankel a * companion a.1 = hankelShift a := by
  ext i j
  have h2 : hankelShift a i j = mom (sec a) (((i : ℕ) + 1) + j) := by simp [hankelShift]; ring_nf
  rw [h2, mom_sec_add, Matrix.mul_apply, pow_succ, ← Matrix.vecMul_vecMul]
  simp only [Matrix.vecMul, dotProduct, hankel_apply']

theorem companion_map {k' : Type} [CommRing k'] (φ : k →+* k') (p : Fin r → k) :
    (companion p).map φ = companion (fun i => φ (p i)) := by
  ext i j; simp only [companion, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp

end Alg

section Herm
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem map_isSelfAdjoint {N : Matrix (Fin r) (Fin r) F} (hN : N.IsSymm) :
    IsSelfAdjoint (N.map (algebraMap F E)) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext i j
  simp [Matrix.conjTranspose_apply, Unram.star_fix, hN.apply i j]

theorem conjTranspose_map (N : Matrix (Fin r) (Fin r) F) :
    (N.map (algebraMap F E))ᴴ = Nᵀ.map (algebraMap F E) := by
  ext i j; simp [Matrix.conjTranspose_apply, Unram.star_fix]

def mkX (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : Hn r F E :=
  (⟨star h⁻¹ * (hankelShift a).map (algebraMap F E) * h⁻¹, by
      have h1 := (map_isSelfAdjoint (E := E) (hankelShift_isSymm a)).conjugate (star h⁻¹)
      rw [star_star] at h1
      exact h1⟩, h *ᵥ e1, a.2.2)

theorem mkX_snd_fst (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : (mkX a h).2.1 = h *ᵥ e1 := rfl

variable {a : Inv r F} {h : Matrix (Fin r) (Fin r) E}

theorem mkX_fst (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    (mkX a h).1.1 = h * (companion a.1).map (algebraMap F E) * h⁻¹ := by
  have hd' : IsUnit hᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
  simp only [mkX]
  rw [← hankel_mul_companion, Matrix.map_mul, ← hh, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd', Matrix.one_mul]

theorem pow_mulVec_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    ((mkX a h).1.1 ^ (j : ℕ)) *ᵥ (h *ᵥ e1) = h *ᵥ Pi.single j 1 := by
  rw [mkX_fst hh hd]
  have key : ∀ n : ℕ, (h * (companion a.1).map (algebraMap F E) * h⁻¹) ^ n =
      h * ((companion a.1).map (algebraMap F E)) ^ n * h⁻¹ := by
    intro n; induction n with
    | zero => simp [Matrix.mul_nonsing_inv _ hd]
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [key, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    companion_map, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector _ j j.2]

theorem bm_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    Bm (mkX a h).toGl = h := by
  ext i j
  simp only [Bm, Hn.toGl, Matrix.of_apply]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.mulVec_single_one]; rfl

theorem mom_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    mom (mkX a h).toGl j = algebraMap F E (a.2.1 j) := by
  have h0 : 0 < r := j.pos
  simp only [mom, Hn.toGl]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hh]
  have he : star (e1 : Fin r → E) = Pi.single (⟨0, h0⟩ : Fin r) 1 := by
    ext i; by_cases hi : (i : ℕ) = 0 <;> simp [e1, hi, Pi.single_apply, Fin.ext_iff]
  rw [he, Matrix.mulVec_single_one, single_one_dotProduct]
  simp only [Matrix.col_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hankel_apply']
  simp
end Herm

section Top
variable {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {r : ℕ}

theorem continuous_companion : Continuous (fun p : Fin r → k => companion p) :=
  continuous_matrix fun i j => by
    simp only [companion, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const

theorem continuous_mom_sec (n : ℕ) : Continuous (fun a : Inv r k => mom (sec a) n) := by
  simp only [mom, sec]
  exact (continuous_fst.comp continuous_snd).dotProduct
    (((continuous_companion.comp continuous_fst).pow n).matrix_mulVec continuous_const)

theorem continuous_hankel : Continuous (fun a : Inv r k => hankel a) :=
  continuous_matrix fun _ _ => continuous_mom_sec _

theorem continuous_hankelShift : Continuous (fun a : Inv r k => hankelShift a) :=
  continuous_matrix fun _ _ => continuous_mom_sec _

theorem continuous_delta : Continuous (fun a : Inv r k => Delta a) :=
  continuous_hankel.matrix_det

end Top

section Unit
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}


omit [Unram F E] in
theorem continuousStar (F : Type) [NontriviallyNormedField F] [NormedAlgebra F E] [Unram F E] : ContinuousStar E :=
  ⟨(Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous⟩

theorem bm_actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : Bm (actU g X).toGl = g.1 * Bm X.toGl := by
  have hg : star g.1 * g.1 = 1 := (Matrix.mem_unitaryGroup_iff').1 g.2
  have key : ∀ n : ℕ, (g.1 * X.1.1 * star g.1) ^ n * g.1 = g.1 * X.1.1 ^ n := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, Matrix.mul_assoc _ (star g.1), hg, Matrix.mul_one,
        Matrix.mul_assoc, ← pow_succ']
  ext i j
  simp only [Bm, Hn.toGl, actU, Matrix.of_apply]
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Unit

end GlobalTheory.JR.ImgSec
end
end

section

open GlobalTheory.Tw Matrix

namespace GlobalTheory.Tw.PhiConjugateTranspose

variable {n : ℕ} {R : Type} [CommRing R]

theorem phi_apply (i k : Fin n) : Phi n R i k = if k = i.rev then (-1 : R) ^ (i : ℕ) else 0 := by
  simp only [Phi, of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  omega

theorem phi_conj_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Phi n R * A * (Phi n R)ᵀ) i j = (-1 : R) ^ (i : ℕ) * A i.rev j.rev * (-1 : R) ^ (j : ℕ) := by
  simp [Matrix.mul_apply, phi_apply, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  have := phi_conj_apply (n := n) (R := R) 1
  ext i j
  have h := this i j
  rw [Matrix.mul_one] at h
  rw [h, Matrix.one_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp [← mul_pow]
  · simp [hij]

theorem phi_transpose_mul : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp phi_mul_transpose

theorem phi_mul_phi : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i k
  simp only [Matrix.mul_apply, phi_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h : k = i
  · subst h
    simp only [if_true, mul_one]
    rw [← pow_add, Fin.val_rev]
    have hk := k.isLt
    rw [show (k : ℕ) + (n - ((k : ℕ) + 1)) = n - 1 by omega]
  · simp [h, Ne.symm h]

theorem phi_inv : (Phi n R)⁻¹ = (Phi n R)ᵀ := Matrix.inv_eq_left_inv phi_transpose_mul

theorem phi_transpose_inv : ((Phi n R)ᵀ)⁻¹ = Phi n R := Matrix.inv_eq_left_inv phi_mul_transpose

theorem conj_inv (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)⁻¹ = Phi n R * A⁻¹ * (Phi n R)ᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, phi_inv, phi_transpose_inv, Matrix.mul_assoc]

theorem det_conj (A : Matrix (Fin n) (Fin n) R) : (Phi n R * A * (Phi n R)ᵀ).det = A.det := by
  rw [det_mul, det_mul, mul_comm (Phi n R).det, mul_assoc, ← det_mul, phi_mul_transpose, det_one, mul_one]

variable [StarRing R]

theorem phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, Phi, of_apply]
  split_ifs <;> simp

theorem phi_transpose_conjTranspose : ((Phi n R)ᵀ)ᴴ = Phi n R := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, Phi, of_apply]
  split_ifs <;> simp

theorem conj_conjTranspose (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)ᴴ = Phi n R * Aᴴ * (Phi n R)ᵀ := by
  rw [conjTranspose_mul, conjTranspose_mul, phi_conjTranspose, phi_transpose_conjTranspose, Matrix.mul_assoc]

theorem theta_eq (g : Matrix (Fin n) (Fin n) R) : theta g = Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ := rfl

theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta_eq, Matrix.mul_inv_rev, conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), phi_transpose_mul, Matrix.one_mul]

theorem theta_one : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [theta_eq, inv_one, conjTranspose_one, Matrix.mul_one, phi_mul_transpose]

theorem det_theta (g : Matrix (Fin n) (Fin n) R) : (theta g).det = star (g⁻¹).det := by
  rw [theta_eq, det_conj, det_conjTranspose]

theorem theta_isUnit {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : IsUnit (theta g) := by
  rw [isUnit_iff_isUnit_det, det_theta]
  exact (isUnit_nonsing_inv_det _ ((isUnit_iff_isUnit_det g).mp hg)).star

theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  have hd := (isUnit_iff_isUnit_det g).mp hg
  rw [theta_eq (theta g), theta_eq g, conj_inv, conj_conjTranspose, ← conjTranspose_nonsing_inv,
    nonsing_inv_nonsing_inv _ hd, conjTranspose_conjTranspose]
  have h2 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← transpose_mul, phi_mul_phi, transpose_smul, transpose_one]
  calc Phi n R * (Phi n R * g * (Phi n R)ᵀ) * (Phi n R)ᵀ
      = (Phi n R * Phi n R) * g * ((Phi n R)ᵀ * (Phi n R)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = g := by
      rw [phi_mul_phi, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, ← mul_pow]
      simp

theorem theta_blockTriangular {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) (ht : g.BlockTriangular id) :
    (theta g).BlockTriangular id := by
  have : Invertible g := hg.invertible
  have hi : (g⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  intro i j hji
  rw [theta_eq, phi_conj_apply, conjTranspose_apply, hi]
  · simp
  · simpa [Fin.rev_lt_rev] using hji

end GlobalTheory.Tw.PhiConjugateTranspose

open GlobalTheory.Tw.PhiConjugateTranspose in
theorem GlobalTheory.Tw.theta_props : ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R], (Phi n R * (Phi n R)ᵀ = 1) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit (theta g) ∧ theta (theta g) = g) ∧ (∀ g h : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit h → theta (g * h) = theta g * theta h) ∧ (∀ x δ : Matrix (Fin n) (Fin n) R, IsUnit x → IsUnit δ → nrm (twConj x δ) = x⁻¹ * nrm δ * x) ∧ (∀ u δ : Matrix (Fin n) (Fin n) R, IsUnit u → IsUnit δ → nrm (δ * theta u) = nrm δ * ((theta δ)⁻¹ * theta u * theta δ) * u) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → g.BlockTriangular id → (theta g).BlockTriangular id) ∧ ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → (theta g).det * star g.det = 1 := by
  intro n R _ _
  refine ⟨phi_mul_transpose, fun g hg => ⟨theta_isUnit hg, theta_theta hg⟩, fun g h _ _ => theta_mul g h, ?_, ?_,
    fun g hg ht => theta_blockTriangular hg ht, ?_⟩
  · intro x δ hx _
    have hxd := (isUnit_iff_isUnit_det x).mp hx
    simp only [nrm, twConj, theta_mul, theta_theta hx]
    have h1 : theta x * theta x⁻¹ = 1 := by rw [← theta_mul, mul_nonsing_inv _ hxd, theta_one]
    calc x⁻¹ * δ * theta x * (theta x⁻¹ * theta δ * x)
        = x⁻¹ * δ * (theta x * theta x⁻¹) * theta δ * x := by simp only [Matrix.mul_assoc]
      _ = x⁻¹ * (δ * theta δ) * x := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  · intro u δ hu hδ
    have htd := (isUnit_iff_isUnit_det _).mp (theta_isUnit hδ)
    simp only [nrm, theta_mul, theta_theta hu]
    calc δ * theta u * (theta δ * u)
        = δ * (theta δ * (theta δ)⁻¹) * theta u * theta δ * u := by
          rw [mul_nonsing_inv _ htd, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = δ * theta δ * ((theta δ)⁻¹ * theta u * theta δ) * u := by simp only [Matrix.mul_assoc]
  · intro g hg
    have hd := (isUnit_iff_isUnit_det g).mp hg
    rw [det_theta, ← star_mul, ← det_mul, mul_nonsing_inv _ hd, det_one, star_one]
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.BigMoment

theorem norm_dot_le_one {n : ℕ} {k : Type} [NormedField k] [IsUltrametricDist k] (c b : Fin n → k)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) : ‖c ⬝ᵥ b‖ ≤ 1 := by
  unfold dotProduct
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro i _
  rw [norm_mul]
  exact mul_le_one₀ (hc i) (norm_nonneg _) (hb i)

theorem dot_act {n : ℕ} {k : Type} [CommRing k] (g : GL (Fin n) k) (Y : Gl n k) :
    (act g Y).2.2.1 ⬝ᵥ (act g Y).2.1 = Y.2.2.1 ⬝ᵥ Y.2.1 := by
  simp only [act]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem dot_sec {r : ℕ} {k : Type} [CommRing k] (a : Inv (r + 1) k) :
    (sec a).2.2.1 ⬝ᵥ (sec a).2.1 = a.2.1 0 := by
  simp [sec, dotProduct, Fin.sum_univ_succ]

theorem dot_actU {n : ℕ} {E : Type} [CommRing E] [StarRing E] (g : Matrix.unitaryGroup (Fin n) E)
    (b : Fin n → E) : star (g.1 *ᵥ b) ⬝ᵥ (g.1 *ᵥ b) = star b ⬝ᵥ b := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp g.2, Matrix.one_mulVec]

theorem matchAt_unit_of_one_lt_norm :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (a : Inv (r + 1) F), 1 < ‖a.2.1 0‖ →
      MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  intro F E _ _ _ _ hU r M a ha
  haveI := hU.ultraF
  haveI := hU.ultraE
  have hG : orbG M (unitG (r + 1) F) (sec a) = 0 := by
    have h : ∀ g, unitG (r + 1) F (act g (sec a)) = 0 := by
      intro g
      unfold unitG
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨-, hb, hc, -⟩
      have := norm_dot_le_one _ _ hc hb
      rw [dot_act, dot_sec] at this
      exact absurd ha (not_lt.mpr this)
    simp [orbG, h]
  refine ⟨fun X hX => ?_, fun _ => hG⟩
  rw [hG]
  have h0 : star X.2.1 ⬝ᵥ X.2.1 = algebraMap F E (a.2.1 0) := by
    have := congrArg (fun t : Inv (r + 1) E => t.2.1 0) hX
    simpa [inv, mom, Hn.toGl, Inv.map] using this
  have h : ∀ g, unitU (r + 1) F E (actU g X) = 0 := by
    intro g
    unfold unitU
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨-, hb, -⟩
    have := norm_dot_le_one (star (actU g X).2.1) (actU g X).2.1
      (fun i => by rw [Pi.star_apply, hU.norm_star]; exact hb i) hb
    simp only [actU] at this
    rw [dot_actU, h0, norm_algebraMap'] at this
    exact absurd ha (not_lt.mpr this)
  simp [orbU, h]

end GlobalTheory.JR.BigMoment
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourU_isLocallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f →
    (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → IsLocallyConstant (fourU M ψ f) := by
  intro F E _ _ _ _ hU r M ψ hψ htr f hf ⟨U, hU0, hUf⟩
  haveI : IsUltrametricDist E := Unram.ultraE (F := F)

  have htr1 : ∀ d : E, ‖d‖ ≤ 1 → ψ (Algebra.trace F E d) = 1 := by
    intro d hd
    apply hψ.1
    have h1 : ‖algebraMap F E (Algebra.trace F E d)‖ ≤ 1 := by
      rw [htr]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd ?_)
      rw [Unram.norm_star (F := F)]; exact hd
    rwa [norm_algebraMap'] at h1

  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin r → E)).1
    ((hf.2.isCompact.image (continuous_fst.comp continuous_snd)).isBounded)
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X₀
  have hcont : Continuous fun X : Hn r F E => ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) :=
    (continuous_fst.sub continuous_const).prodMk (continuous_const.prodMk
      ((continuous_snd.comp continuous_snd).sub continuous_const))
  have hV1 : ∀ᶠ X in 𝓝 X₀, ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) ∈ U := by
    have : ((X₀.1 - X₀.1, (0 : Fin r → E), X₀.2.2 - X₀.2.2) : Hn r F E) = 0 := by
      ext <;> simp
    exact hcont.continuousAt.preimage_mem_nhds (by rw [this]; exact hU0)
  have hV2 : ∀ᶠ X in 𝓝 X₀, X.2.1 ∈ Metric.closedBall X₀.2.1 (1 / R') :=
    (continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ (by positivity))
  filter_upwards [hV1, hV2] with X hX1 hX2
  unfold fourU
  congr 1
  funext c
  have hfe : f (X.1, c, X.2.2) = f (X₀.1, c, X₀.2.2) := by
    have := hUf (X₀.1, c, X₀.2.2) _ hX1
    rw [← this]; congr 1; ext <;> simp
  rw [hfe]
  by_cases h0 : f (X₀.1, c, X₀.2.2) = 0
  · rw [h0, zero_mul, zero_mul]
  congr 1
  have hc : ‖c‖ ≤ R := by
    have hmem : c ∈ (fun X : Hn r F E => X.2.1) '' tsupport f :=
      ⟨(X₀.1, c, X₀.2.2), subset_tsupport _ h0, rfl⟩
    simpa using hR hmem
  have hs : ‖star c ⬝ᵥ (X.2.1 - X₀.2.1)‖ ≤ 1 := by
    have hd : ‖X.2.1 - X₀.2.1‖ ≤ 1 / R' := by rw [← dist_eq_norm]; exact hX2
    unfold dotProduct
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, Pi.star_apply, Unram.norm_star (F := F)]
    have h1 : ‖c i‖ ≤ R' := (norm_le_pi_norm c i).trans (hc.trans (le_max_left _ _))
    have h2 : ‖(X.2.1 - X₀.2.1) i‖ ≤ 1 / R' := (norm_le_pi_norm _ i).trans hd
    calc ‖c i‖ * ‖(X.2.1 - X₀.2.1) i‖ ≤ R' * (1 / R') :=
          mul_le_mul h1 h2 (norm_nonneg _) hR'pos.le
      _ = 1 := by field_simp
  have hsplit : star c ⬝ᵥ X.2.1 = star c ⬝ᵥ X₀.2.1 + star c ⬝ᵥ (X.2.1 - X₀.2.1) := by
    rw [dotProduct_sub]; ring
  rw [hsplit, map_add (f := _), AddChar.map_add_eq_mul, htr1 _ hs, mul_one]

end GlobalTheory
end
