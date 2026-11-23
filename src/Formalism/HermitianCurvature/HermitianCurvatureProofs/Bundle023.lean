module

public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AddedBlockKernelSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdicNeighbourhood
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragedKernelSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragedVectorChoices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EqZeroOfIdealCompact
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteClassesPositiveSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle016
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle022
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussIndexIndependentOfChoice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussSumModulusOfLattice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle014
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermSumLattices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HenselRootsBounded
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HessianScalingIntegrals
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralLatticeRefinementIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelScalingBack
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanNormSquaredBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanPositiveSemidefinite
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModulusLocallyConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PadicChangeOfVariables
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubmoduleMultiplication
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoBlockPoint
public import Formalism.RealPlaceAnalysis.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterOrthogonalityDual
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ColumnOperationTripleForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelExplicitFormula
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramKernelHermitian

@[expose] public section

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem det_row_sum {n : ℕ} {ι : Type} (s : Finset ι) (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (c : ι → ℂ)
    (v : ι → Fin n → ℂ) :
    (M.updateRow i (∑ w ∈ s, c w • v w)).det = ∑ w ∈ s, c w * (M.updateRow i (v w)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [Matrix.updateRow_self])
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.det_updateRow_add,
      Matrix.det_updateRow_smul, ih]

theorem det_row_lin {n : ℕ} {ι : Type} [Fintype ι] (X : Fin n → Fin n → ℂ) (i : Fin n) (η : ι → ℂ)
    (v : ι → Fin n → ℂ) (hrow : ∀ l, X i l = ∑ w, η w * v w l) :
    (Matrix.of X).det = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det := by
  have h1 : Matrix.of X = (Matrix.of X).updateRow i (∑ w, η w • v w) := by
    ext a l
    by_cases h : a = i
    · subst h
      simp [Matrix.updateRow_self, hrow, Finset.sum_apply]
    · simp [Matrix.updateRow_ne h]
  have h2 : ∀ w, (Matrix.of fun a l => if a = i then v w l else X a l) =
      (Matrix.of X).updateRow i (v w) := by
    intro w
    ext a l
    by_cases h : a = i
    · subst h
      simp
    · simp [h, Matrix.updateRow_ne h]
  calc (Matrix.of X).det = ((Matrix.of X).updateRow i (∑ w ∈ Finset.univ, η w • v w)).det :=
        congrArg Matrix.det h1
    _ = ∑ w ∈ Finset.univ, η w * ((Matrix.of X).updateRow i (v w)).det := det_row_sum _ _ _ _ _
    _ = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det :=
        Finset.sum_congr rfl (fun w _ => by rw [h2 w])

theorem sum_lin {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} {ι : Type} [Fintype ι]
    (P : (Fin m → Fin N) → Prop) [DecidablePred P] (X : Fin m → Fin N → ℂ) (i : Fin m) (η : ι → ℂ)
    (v : ι → Fin N → ℂ) (hrow : ∀ p, X i p = ∑ w, η w * v w p) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      ∑ w, η w • ∑ c : Fin m → Fin N,
        if P c then (Matrix.of fun a l => (if a = i then v w (c l) else X a (c l))).det • F c else 0 := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hP
  · rw [det_row_lin (fun a l => X a (c l)) i η (fun w l => v w (c l)) (fun l => hrow (c l)),
      Finset.sum_smul]
    exact Finset.sum_congr rfl (fun w _ => mul_smul _ _ _)
  · simp

theorem strictMono_snoc {α : Type} [Preorder α] {m : ℕ} (f : Fin m → α) (hf : StrictMono f) (x : α)
    (hx : ∀ l, f l < x) : StrictMono (Fin.snoc (α := fun _ => α) f x : Fin (m + 1) → α) := by
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (lt_irrefl _)
    | cast a =>
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx a
  | cast b =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last b).le)
    | cast a =>
      simp only [Fin.snoc_castSucc]
      exact hf (Fin.castSucc_lt_castSucc_iff.1 hab)

theorem hpk_zero_alt (k r : ℕ) (p q : Fin (2 * r + k + 1)) (hq : r ≤ q.val ∧ q.val ≤ r + k)
    (hp : ¬ (r ≤ p.val ∧ p.val ≤ r + k)) : Hpk k r q p = 0 := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec_sum (k r : ℕ) (yb : Fin (2 * r + k + 1) → ℂ) (hyb : inWb k r yb) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec p) yb =
      ∑ w : Fin (k + 1), herm (Hpk k r) (bvec (wI k r w)) yb * (if p = wI k r w then 1 else 0) := by
  unfold inWb at hyb
  unfold herm bvec wI
  by_cases hp : r ≤ (p : ℕ) ∧ (p : ℕ) ≤ r + k
  · rw [Finset.sum_eq_single (⟨(p : ℕ) - r, by omega⟩ : Fin (k + 1))]
    · split_ifs with h
      · rw [mul_one, ← h]
      · exact absurd (Fin.ext (by simp only [Fin.val_mk]; omega)) h
    · intro b _ hb
      split_ifs with h
      · exact absurd (Fin.ext (by simp only [Fin.ext_iff, Fin.val_mk] at h ⊢; omega)) hb
      · exact mul_zero _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hL : star yb ⬝ᵥ Hpk k r *ᵥ Pi.single p 1 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k
      · have h0 : (Hpk k r *ᵥ Pi.single p 1) i = 0 := by
          simp [Matrix.mulVec, hpk_zero_alt k r p i hi hp]
        rw [h0, mul_zero]
      · have h0 : yb i = 0 := hyb i (by omega)
        simp [h0]
    rw [hL]
    symm
    apply Finset.sum_eq_zero
    intro w _
    split_ifs with h
    · have hw := w.isLt
      rw [Fin.ext_iff] at h
      simp only [Fin.val_mk] at h
      exact absurd ⟨by omega, by omega⟩ hp
    · exact mul_zero _

theorem hpk_real (k r : ℕ) (p q : Fin (2 * r + k + 1)) : star (Hpk k r p q) = Hpk k r p q := by
  unfold Hpk
  split_ifs <;> simp

theorem hpk_symm (k r : ℕ) (p q : Fin (2 * r + k + 1)) : Hpk k r p q = Hpk k r q p := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_star (k r : ℕ) (p q : Fin (2 * r + k + 1)) : star (Hpk k r p q) = Hpk k r q p := by
  rw [hpk_real, hpk_symm]

theorem herm_swap (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  have hH : (Hpk k r)ᴴ = Hpk k r := by
    ext p q
    rw [conjTranspose_apply, hpk_star]
  rw [star_dotProduct v (Hpk k r *ᵥ w), star_star, star_mulVec, hH, dotProduct_mulVec]

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6

theorem gauss_hessian_index_exists : Formalism.FourierDecayAlt.A6.GaussHess :=
  gauss_hessian_index_of_parts gauss_sum_modulus_of_lattice gauss_index_independent_of_choice
    phase_hessian_determinant modulus_positive_multiplicative volume_scaling_identity

theorem padic_stationary_phase : Formalism.FourierDecayAlt.A6.StationaryPhase :=
  stationaryPhaseOfSteps nonStationary morseLemma integral_field_refinement
    modulus_positive_multiplicative rootsFinite compactOpenChoice orthogonal_lattice_properties
    modulusLocallyConstant oscillatory_integral_invariant volume_scaling_identity rootsSeparated
    smallModules admissible_gauss_sum_small lattice_family_finite

theorem germ_expansion_matrix_function : Formalism.FourierDecayAlt.A6.GermPhi :=
  germExpansionOfTestFunction orbital_integral_change_of_variables padic_stationary_phase
    oscillatory_integral_invariant modulus_positive_multiplicative

theorem germ_expansion_with_head : Formalism.FourierDecayAlt.A6.Germ :=
  germExpansionOfSteps head_reduction_lemma germ_expansion_matrix_function

theorem germ_kernel_expansion : Formalism.FourierDecayAlt.A6.GermKernel :=
  germExpansionKernelOfSteps germ_expansion_with_head kernel_as_coset_sum integral_points_finite
    rootsFinite

theorem germ_identity_bis : Formalism.FourierDecayAlt.A6.GermIdentity :=
  germIdentityOfSteps gauss_hessian_index_exists germ_kernel_expansion gramKernelHermitian
    second_vanishing_off_ring modulus_positive_multiplicative rootsFinite shiftUnit_statement
    shiftSmall_statement rootCutStable rootCorrection square_near_unit phase_difference_estimate
    phase_locally_constant modulusLocallyConstant integral_lattice_refinement_identity
    padic_change_of_variables crossTermsVanish

theorem theta_omega_bound : Formalism.FourierDecayAlt.A6.ThOm :=
  thetaOnDomainOfSteps germ_identity_bis averaged_vector_choices_exist phase_locally_constant
    gramKernelHermitian modulusLocallyConstant compactOpenChoice lattice_family_finite
    shiftUnit_statement smallUnits gram_equality_of_vectors averaged_vector_norm_bound
    cut_posSemidef heads_distinct_determinant_orthogonal head_size_add_block
    modulus_positive_multiplicative kernel_gram_property kernel_block_diagonal_by_modulus
    gramRealisation averageBound parsevalGroup_statement annihilatorCharacters
    orthogonal_lattice_properties characterMean truncated_average_norm_formula thetaAverageLower
    averaged_kernel_periodic_psd averaged_kernel_parseval

theorem lattice_average_induction : Formalism.FourierDecayAlt.A5.ThetaExistsStep :=
  thetaExistsStepOfSteps theta_omega_bound finite_family_truncation_module
    added_block_kernel_support head_size_one_in_GL rootStableExhaustion lattice_family_finite
    posSemidefEntryBound posSemidefClosed boundedSubsequence

theorem lattice_average_lemma_full : Formalism.FourierDecayAlt.A5.LemmaA :=
  lattice_average_lemma_from_parts second_gram_and_vanishing first_kernel_parseval
    first_theta_kernel_equality first_theta_equals_first_kernel lattice_average_induction
    zero_kernel_all_ones added_block_kernel_support added_block_kernel_block_diagonal

end Formalism.FourierDecayAlt.P
end

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section poly

variable {A : Type} [Ring A] [Algebra ℂ A]

def PolyLe (t : ℕ) (f : ℂ → A) : Prop :=
  ∃ C : Fin t → A, ∀ u, f u = ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l

theorem pl_congr {t : ℕ} {f g : ℂ → A} (h : ∀ u, f u = g u) (hf : PolyLe t f) : PolyLe t g := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun u => by rw [← h u]; exact hC u⟩

theorem pl_zero (t : ℕ) : PolyLe t (fun _ => (0 : A)) := ⟨0, fun u => by simp⟩

theorem pl_add {t : ℕ} {f g : ℂ → A} (hf : PolyLe t f) (hg : PolyLe t g) : PolyLe t (fun u => f u + g u) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun u => ?_⟩
  dsimp only
  rw [hC, hD, ← Finset.sum_add_distrib]
  simp only [Pi.add_apply, mul_add]

theorem pl_sum {t : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ → A) (hf : ∀ i ∈ s, PolyLe t (f i)) :
    PolyLe t (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact pl_congr (fun u => by simp) (pl_zero t)
  | insert i s hi ih =>
    exact pl_congr (fun u => by simp [Finset.sum_insert hi])
      (pl_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem pl_lmul {t : ℕ} {f : ℂ → A} (c : A) (hf : PolyLe t f) : PolyLe t (fun u => c * f u) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨fun l => c * C l, fun u => ?_⟩
  dsimp only
  rw [hC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => Algebra.left_comm _ _ _

theorem pl_mono {t : ℕ} {f : ℂ → A} (hf : PolyLe t f) : PolyLe (t + 1) f := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨Fin.snoc (α := fun _ => A) C 0, fun u => ?_⟩
  rw [hC, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem pl_mulu {t : ℕ} {f : ℂ → A} (hf : PolyLe t f) : PolyLe (t + 1) (fun u => f u * algebraMap ℂ A u) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨Fin.cons (α := fun _ => A) 0 C, fun u => ?_⟩
  dsimp only
  rw [hC, Fin.sum_univ_succ, Finset.sum_mul]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, Fin.val_succ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, pow_succ]

theorem pl_mono_const (t : ℕ) (x : A) : PolyLe (t + 1) (fun u => algebraMap ℂ A (u ^ t) * x) := by
  refine ⟨Fin.snoc (α := fun _ => A) 0 x, fun u => ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem prod_poly : ∀ (t : ℕ) (c δ : Fin t → ℂ) (F : Fin t → A),
    PolyLe t (fun u => (List.ofFn fun k => algebraMap ℂ A ((u + c k) * δ k) + F k).prod -
      algebraMap ℂ A (u ^ t * ∏ k, δ k)) := by
  intro t
  induction t with
  | zero =>
    intro c δ F
    exact ⟨Fin.elim0, fun u => by simp⟩
  | succ t ih =>
    intro c δ F
    obtain ⟨C, hC⟩ := ih (fun k => c k.succ) (fun k => δ k.succ) (fun k => F k.succ)
    let Q : ℂ → A := fun u => ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
    have hQpl : PolyLe t Q := ⟨C, fun u => rfl⟩
    have hR : ∀ u, (List.ofFn fun k : Fin t => algebraMap ℂ A ((u + c k.succ) * δ k.succ) + F k.succ).prod =
        algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) + Q u := by
      intro u
      show _ = _ + ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
      have h := hC u
      dsimp only at h
      rw [← h]
      abel
    refine pl_congr (f := fun u => algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) +
        ((algebraMap ℂ A (c 0 * δ 0) + F 0) * Q u + algebraMap ℂ A (u ^ t) *
          ((algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (∏ k : Fin t, δ k.succ)))) ?_
      (pl_add (pl_lmul _ (pl_mulu hQpl)) (pl_add (pl_mono (pl_lmul _ hQpl)) (pl_mono_const t _)))
    intro u
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [hR u]
    have e1 : algebraMap ℂ A (u * δ 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ (t + 1) * (δ 0 * ∏ k : Fin t, δ k.succ)) := by
      rw [← map_mul]
      congr 1
      ring
    have e2 : algebraMap ℂ A (u * δ 0) * Q u = algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) := by
      rw [← Algebra.commutes, ← mul_assoc, ← map_mul, mul_comm (δ 0) u]
    have e3 : (algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ t) * ((algebraMap ℂ A (c 0 * δ 0) + F 0) *
          algebraMap ℂ A (∏ k : Fin t, δ k.succ)) := by
      rw [map_mul (algebraMap ℂ A) (u ^ t), Algebra.left_comm]
    rw [add_mul u (c 0) (δ 0), map_add (f := _), add_assoc,
      mul_add (algebraMap ℂ A (u * δ 0) + (algebraMap ℂ A (c 0 * δ 0) + F 0)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (Q u), e1, e2, e3]
    abel

theorem qminor_poly {n t : ℕ} (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (s0 : ℂ) :
    PolyLe t (fun u => qminor E a b (u + s0) - algebraMap ℂ A (u ^ t *
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0))) := by
  classical
  refine pl_congr (f := fun u => ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
      ((List.ofFn fun k : Fin t => algebraMap ℂ A ((u + (s0 - (k : ℂ))) *
          (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k)).prod -
        algebraMap ℂ A (u ^ t * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0)))) ?_
    (pl_sum _ _ fun σ _ => pl_lmul _ (prod_poly t _ _ _))
  intro u
  have hT : ∀ (σ : Equiv.Perm (Fin t)) (k : Fin t), Tm E (u + s0 - (k : ℂ)) (a (σ k)) (b k) =
      algebraMap ℂ A ((u + (s0 - (k : ℂ))) * (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k) := by
    intro σ k
    unfold Tm
    split_ifs <;> simp [add_sub_assoc]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · unfold qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hT]

  · rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_left_comm (u ^ t) (((Equiv.Perm.sign σ : ℤ) : ℂ)),
      map_mul (algebraMap ℂ A) (((Equiv.Perm.sign σ : ℤ) : ℂ)), map_intCast]

end poly

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end
