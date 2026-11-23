module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PSpecB

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem toMK_inv_eq_conjTranspose {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h : toMK k⁻¹ = star (toMK k) :=
    Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem (show toMK k ∈ Kset ε from k.2).1)
  rw [h, Matrix.star_eq_conjTranspose]

theorem conj_pmat_eq_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    toMK k⁻¹ * pmat z * toMK k = pmat (adK k⁻¹ z) := by
  rw [pmat_adK, toMK_inv_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

theorem rhoP_real_smul {ε : Fin n → Bool} (t : ℝ) (z : PCoord ε → ℂ) : rhoP ((t : ℂ) • z) = |t| * rhoP z := by
  have hS : ∑ ab, ‖((t : ℂ) • z) ab‖ ^ 2 = t ^ 2 * ∑ ab, ‖z ab‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    simp [Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold rhoP
  rw [hs_pmat, hs_pmat, hS, show 2 * (t ^ 2 * ∑ ab, ‖z ab‖ ^ 2) = t ^ 2 * (2 * ∑ ab, ‖z ab‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def plog (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Matrix.isHermitian_conjTranspose_mul_self h).cfc Real.log

def actR {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (z : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => plog (NormedSpace.exp (pmat z) * g) ab.1.1 ab.1.2

theorem pact_cfc_log_exp (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (h : (NormedSpace.exp X).IsHermitian) : h.cfc Real.log = X := by
  have hSA : IsSelfAdjoint X := Matrix.isHermitian_iff_isSelfAdjoint.mp hX
  obtain ⟨W, hWdef⟩ : ∃ W, W = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hW : star W * W = 1 := by
    rw [hWdef]
    exact Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2
  have hWi : W⁻¹ = star W := Matrix.inv_eq_left_inv hW
  have hWu : IsUnit W := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hW)
  have hexp : NormedSpace.exp X = hX.cfc Real.exp := by
    have hd : NormedSpace.exp (RCLike.ofReal ∘ hX.eigenvalues : Fin n → ℂ) =
        (RCLike.ofReal ∘ Real.exp ∘ hX.eigenvalues : Fin n → ℂ) := by
      funext i
      simp [Complex.ofReal_exp, ← Complex.exp_eq_exp_ℂ]
    conv_lhs => rw [hX.spectral_theorem]
    rw [Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star]
    rw [← hWdef, ← hWi, Matrix.exp_conj _ _ hWu, Matrix.exp_diagonal, hd]
  rw [← Matrix.IsHermitian.cfc_eq, hexp, ← Matrix.IsHermitian.cfc_eq,
    ← cfc_comp Real.log Real.exp X hSA
      (Real.continuousOn_log.mono (by rintro _ ⟨x, -, rfl⟩; exact (Real.exp_pos x).ne'))
      Real.continuous_exp.continuousOn]
  have hle : Real.log ∘ Real.exp = id := funext Real.log_exp
  rw [hle]
  exact cfc_id ℝ X hSA

theorem pact_cfc_congr {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) (f : ℝ → ℝ) : hA.cfc f = hB.cfc f := by
  subst h
  rfl

theorem plog_unitary_mul_exp (k X : Matrix (Fin n) (Fin n) ℂ) (hk : kᴴ * k = 1) (hX : X.IsHermitian) :
    plog (k * NormedSpace.exp X) = X := by
  have hE : (NormedSpace.exp X)ᴴ = NormedSpace.exp X := by
    rw [← Matrix.exp_conjTranspose, hX.eq]
  have h2 : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) = NormedSpace.exp (X + X) := by
    rw [Matrix.exp_add_of_commute X X (Commute.refl X), Matrix.conjTranspose_mul, hE,
      Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
  have hB : (NormedSpace.exp (X + X)).IsHermitian := by
    rw [← h2]
    exact Matrix.isHermitian_conjTranspose_mul_self _
  unfold plog
  rw [pact_cfc_congr (Matrix.isHermitian_conjTranspose_mul_self (k * NormedSpace.exp X)) hB h2 Real.log,
    pact_cfc_log_exp (X + X) (hX.add hX) hB, ← two_smul ℂ X, smul_smul]
  norm_num

private theorem toMK_unit_lemma {ε : Fin n → Bool} (k : KG ε) : (toMK k)ᴴ * toMK k = 1 := by
  have hk := k.2
  unfold S7.KG Kset at hk
  unfold S7.toMK
  exact Matrix.mem_unitaryGroup_iff'.mp hk.1

theorem plog_polarM {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : plog (polarM (k, z)) = pmat z :=
  plog_unitary_mul_exp (toMK k) (pmat z) (toMK_unit_lemma k) (pmat_isHermitian z)

theorem pact_pmat_coords {ε : Fin n → Bool} (w : PCoord ε → ℂ) :
    (fun ab : PCoord ε => pmat w ab.1.1 ab.1.2) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, h⟩ := ab
  simp only [pmat]
  rw [dite_eq_left h]

private theorem actR_eq_lemma {ε : Fin n → Bool} {g U : Matrix (Fin n) (Fin n) ℂ} {z w : PCoord ε → ℂ}
    (hU : Uᴴ * U = 1) (h : NormedSpace.exp (pmat z) * g = U * NormedSpace.exp (pmat w)) :
    actR g z = w := by
  unfold actR
  rw [h, plog_unitary_mul_exp U (pmat w) hU (pmat_isHermitian w)]
  exact pact_pmat_coords w

theorem actR_of_eq_polarM {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} {z w : PCoord ε → ℂ} {k : KG ε}
    (h : NormedSpace.exp (pmat z) * g = polarM (k, w)) : actR g z = w := by
  unfold actR
  rw [h, plog_polarM]
  exact pact_pmat_coords w

theorem pact_inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

theorem actR_spec {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    ∃ k : KG ε, NormedSpace.exp (pmat z) * g = polarM (k, actR g z) := by
  obtain ⟨⟨k, w⟩, hkw⟩ := polarM_surj _ (pact_inUJ_mul (exp_pmat_inUJ z) hg)
  refine ⟨k, ?_⟩
  rw [actR_of_eq_polarM hkw.symm]
  exact hkw.symm

theorem actR_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h)
    (z : PCoord ε → ℂ) : actR (g * h) z = actR h (actR g z) := by
  obtain ⟨k1, h1⟩ := actR_spec hg z
  obtain ⟨k2, h2⟩ := actR_spec hh (actR g z)
  simp only [polarM] at h1 h2
  apply actR_eq_lemma (U := toMK k1 * toMK k2)
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (toMK k1)ᴴ, toMK_unit_lemma k1,
      Matrix.one_mul, toMK_unit_lemma k2]
  · rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc (toMK k1) (NormedSpace.exp (pmat (actR g z))) h, h2,
      Matrix.mul_assoc (toMK k1) (toMK k2)]

theorem actR_one {ε : Fin n → Bool} (z : PCoord ε → ℂ) : actR (1 : Matrix (Fin n) (Fin n) ℂ) z = z := by
  apply actR_eq_lemma (U := 1)
  · simp
  · rw [Matrix.mul_one, Matrix.one_mul]

theorem pact_pmat_zero {ε : Fin n → Bool} : pmat (0 : PCoord ε → ℂ) = 0 := by
  ext a b
  simp [pmat]

private theorem toMK_unit_lemma_2 {ε : Fin n → Bool} (k : KG ε) : toMK k * (toMK k)ᴴ = 1 := by
  have hk := k.2
  unfold S7.KG Kset at hk
  unfold S7.toMK
  exact Matrix.mem_unitaryGroup_iff.mp hk.1

theorem actR_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : actR (toMK k) z = adK k⁻¹ z := by
  have hU := toMK_unit_lemma k
  have hU' : toMK k * (toMK k)ᴴ = 1 := toMK_unit_lemma_2 k
  have hinv : toMK k⁻¹ * toMK k = 1 := by
    simp [S7.toMK, S7.toM]
  have hi1 : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_left_inv hU
  have hi2 : (toMK k)⁻¹ = toMK k⁻¹ := Matrix.inv_eq_left_inv hinv
  have hunit : IsUnit (toMK k) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hU)
  apply actR_eq_lemma hU
  have hi3 : (toMK k)⁻¹ᴴ = toMK k := by rw [hi1, Matrix.conjTranspose_conjTranspose]
  rw [pmat_adK, ← hi2, hi3, Matrix.exp_conj' _ _ hunit, hi1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU',
    Matrix.one_mul]

theorem actR_exp_zero {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    actR (NormedSpace.exp (pmat y)) (0 : PCoord ε → ℂ) = y := by
  apply actR_eq_lemma (U := 1)
  · simp
  · rw [pact_pmat_zero, NormedSpace.exp_zero, Matrix.one_mul]

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem wS_nonneg' {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) : 0 ≤ wS z hi S := by
  unfold wS
  positivity

theorem fi_eq_lse {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (t : ℝ) :
    Fi ((t : ℂ) • pmat z) i = Real.log (∑ S, wS z hi S * Real.exp (t * yS z S.1)) := by
  unfold Fi
  rw [lemma3a z hi t]
  congr 1
  have h : (∑ S, ((wS z hi S : ℝ) : ℂ) * Complex.exp ((t * yS z S.1 : ℝ) : ℂ)) =
      ((∑ S, wS z hi S * Real.exp (t * yS z S.1) : ℝ) : ℂ) := by
    push_cast
    simp only [Complex.ofReal_exp, Complex.ofReal_mul]
  rw [h, Complex.ofReal_re]

theorem fi_pmat_eq_fi_one_smul_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) (i : ℕ) :
    Fi (pmat z) i = Fi (((1 : ℝ) : ℂ) • pmat z) i := by
  rw [Complex.ofReal_one, one_smul]

theorem fi_convex {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Fi ((t : ℂ) • pmat z) i) := by
  have h : (fun t : ℝ => Fi ((t : ℂ) • pmat z) i) =
      fun t : ℝ => Real.log (∑ S, wS z hi S * Real.exp (t * yS z S.1)) := by
    funext t
    exact fi_eq_lse z hi t
  rw [h]
  exact lse_convexOn (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi)

theorem fi_zero (i : ℕ) : Fi (0 : Matrix (Fin n) (Fin n) ℂ) i = 0 := by
  unfold Fi Del
  rw [NormedSpace.exp_zero]
  split_ifs with h
  · rw [Matrix.submatrix_one _ (Fin.castLE_injective h)]
    simp
  · simp

theorem fi_nonneg {ε : Fin n → Bool} (z : PCoord ε → ℂ) (i : ℕ) : 0 ≤ Fi (pmat z) i := by
  by_cases hi : i ≤ n
  · rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi]
    apply Real.log_nonneg
    have h := lse_one_le (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    simpa only [one_mul] using h
  · unfold Fi Del
    rw [dite_eq_right hi]
    simp

theorem fi_lower {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) {ep : ℝ}
    (h1 : rhoP z ≤ ep) (h2 : ep ≤ 1) : Vi (pmat z) i / 2 * (1 - ep) ≤ Fi (pmat z) i := by
  have hr : 0 ≤ rhoP z := by
    unfold rhoP
    positivity
  rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi, ← lemma3d z hi]
  have h := lse_lower (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    (hr.trans h1) h2 (fun S => by
      have := abs_sum_pev_le z S.1
      unfold yS
      linarith)
  simpa only [one_mul] using h

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def intMuCD_pM (ε : Fin n → Bool) : KG ε × (PCoord ε → ℂ) → (Fin n → Fin n → ℂ) := fun kz => polarM kz

def intMuCD_P (ε : Fin n → Bool) : Measure (KG ε × (PCoord ε → ℂ)) :=
  (dk ε).prod (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z))

theorem intMuCD_muPolarMat_eq (ε : Fin n → Bool) :
    muPolarMat ε = Measure.map (intMuCD_pM ε) (intMuCD_P ε) := rfl

theorem lintegral_comap_embedding {α : Type*} [MeasurableSpace α] {e : α → (Fin n → Fin n → ℂ)}
    (he : MeasurableEmbedding e) (μ : Measure (Fin n → Fin n → ℂ)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.range e)
    (F : (Fin n → Fin n → ℂ) → ENNReal) :
    ∫⁻ g, F (e g) ∂(Measure.comap e μ) = ∫⁻ x, F x ∂μ := by
  have h1 := he.lintegral_map (μ := Measure.comap e μ) F
  rw [he.map_comap, Measure.restrict_eq_self_of_ae_mem hμ] at h1
  exact h1.symm

theorem intMuCD_measurable_pM (ε : Fin n → Bool) : Measurable (intMuCD_pM ε) := by
  exact Continuous.measurable (f := intMuCD_pM ε) (polarM_continuous ε)

theorem intMuCD_polar_int (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ x, F x ∂(muPolarMat ε) =
      ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hpm := intMuCD_measurable_pM ε
  have hJ : Measurable (fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) :=
    ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  rw [intMuCD_muPolarMat_eq, lintegral_map hF hpm, intMuCD_P]
  refine (lintegral_prod (F ∘ intMuCD_pM ε) (hF.comp hpm).aemeasurable).trans ?_
  refine lintegral_congr (fun k => ?_)
  refine (lintegral_withDensity_eq_lintegral_mul _ hJ (hF.comp (hpm.comp measurable_prodMk_left))).trans ?_
  refine lintegral_congr (fun z => ?_)
  exact mul_comm _ _

theorem intMuCD_ae_range (ε : Fin n → Bool) (S : Set (Fin n → Fin n → ℂ)) (hS : MeasurableSet S)
    (h : ∀ kz : KG ε × (PCoord ε → ℂ), intMuCD_pM ε kz ∈ S) : ∀ᵐ x ∂(muPolarMat ε), x ∈ S := by
  rw [intMuCD_muPolarMat_eq]
  exact (ae_map_iff (p := fun x => x ∈ S) (intMuCD_measurable_pM ε).aemeasurable hS).2 (ae_of_all _ h)

def intMuCD_eM (ε : Fin n → Bool) : UJ ε → (Fin n → Fin n → ℂ) := fun g => toM g

def intMuCD_eU (ε : Fin n → Bool) : Formalism.REAL.UJ ε → (Fin n → Fin n → ℂ) := fun g => Formalism.MainNotions.S.umat g

private theorem exists_UJ_toM_eq_of_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ u : UJ ε, toM u = g := by
  change g ∈ Set.range (fun u : UJ ε => toM u)
  rw [range_toM]
  exact hg

theorem lintegral_muPolar (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ g, F (toM g) ∂(muPolar ε) =
      ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hemb : MeasurableEmbedding (intMuCD_eM ε) := (isClosedEmbedding_toM ε).measurableEmbedding
  have hae : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range (intMuCD_eM ε) :=
    intMuCD_ae_range ε _ hemb.measurableSet_range fun kz => exists_UJ_toM_eq_of_inUJ (polarM_inUJ kz)
  calc ∫⁻ g, F (toM g) ∂(muPolar ε)
        = ∫⁻ g, F (intMuCD_eM ε g) ∂(Measure.comap (intMuCD_eM ε) (muPolarMat ε)) := rfl
    _ = ∫⁻ x, F x ∂(muPolarMat ε) := lintegral_comap_embedding hemb _ hae F
    _ = _ := intMuCD_polar_int ε F hF

theorem lintegral_muCD (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε) =
      ENNReal.ofReal (cPQ ε) * ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hemb : MeasurableEmbedding (intMuCD_eU ε) := (isClosedEmbedding_toM ε).measurableEmbedding
  have hae : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range (intMuCD_eU ε) :=
    intMuCD_ae_range ε _ hemb.measurableSet_range fun kz => exists_UJ_toM_eq_of_inUJ (polarM_inUJ kz)
  calc ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε)
        = ENNReal.ofReal (cPQ ε) *
            ∫⁻ g, F (intMuCD_eU ε g) ∂(Measure.comap (intMuCD_eU ε) (muPolarMat ε)) := by
          rw [muCD, lintegral_smul_measure]
          rfl
    _ = _ := by rw [lintegral_comap_embedding hemb _ hae F, intMuCD_polar_int ε F hF]

end ReciprocityTheory.ChartRestriction.DS
end
end
