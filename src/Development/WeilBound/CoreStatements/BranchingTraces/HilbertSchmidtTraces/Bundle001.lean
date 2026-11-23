module

public import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

private theorem star_dotProduct_Jm_mulVec_comm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) :
    star (star a ⬝ᵥ (Jm ε *ᵥ b)) = star b ⬝ᵥ (Jm ε *ᵥ a) := by
  simp only [Jm, dotProduct, mulVec_diagonal, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem refl_ex {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ) (hz : star z ⬝ᵥ (Jm ε *ᵥ z) = 1) (hy : star y ⬝ᵥ (Jm ε *ᵥ y) = 1)
    (c : ℝ) (hc : c ≤ 0) (hyz : star y ⬝ᵥ (Jm ε *ᵥ z) = c) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, inUJ ε R ∧ R *ᵥ z = y ∧ hs R ≤ 2 * n + 2 * nsq (y - z) ^ 2 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℂ, w = y - z := ⟨_, rfl⟩
  rw [← hw]
  have hzy : star z ⬝ᵥ (Jm ε *ᵥ y) = c := by
    rw [← star_dotProduct_Jm_mulVec_comm, hyz, Complex.star_def, Complex.conj_ofReal]
  have hq : star w ⬝ᵥ (Jm ε *ᵥ w) = 2 - 2 * (c : ℂ) := by
    rw [hw, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hy, hz, hyz, hzy]
    ring
  have hwz : star w ⬝ᵥ (Jm ε *ᵥ z) = c - 1 := by
    rw [hw, star_sub, sub_dotProduct, hyz, hz]
  have hpos : (0 : ℝ) < 2 - 2 * c := by linarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = 2 / (2 - 2 * c) := ⟨_, rfl⟩
  have hk : k * (2 - 2 * c) = 2 := by rw [hkdef, div_mul_cancel₀ _ (ne_of_gt hpos)]
  have hk0 : 0 < k := by rw [hkdef]; exact div_pos (by norm_num) hpos
  have hk1 : k ≤ 1 := by nlinarith
  have hkC : (k : ℂ) * (2 - 2 * (c : ℂ)) = 2 := by exact_mod_cast hk
  have hq' : (star w ᵥ* Jm ε) ⬝ᵥ w = 2 - 2 * (c : ℂ) := by rw [← dotProduct_mulVec, hq]
  have hbj : ∀ j, ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖ ^ 2 = k ^ 2 * ‖w j‖ ^ 2 := by
    intro j
    simp only [Pi.smul_apply, smul_eq_mul, Jm, vecMul_diagonal, norm_mul, Pi.star_apply, norm_star,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0]
    split_ifs <;> simp <;> ring
  have h1 : ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = n := by
    simp [Matrix.one_apply, apply_ite]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2) = k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2 := by
    simp only [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  refine ⟨1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)), ?_, ?_, ?_⟩
  · show (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)))ᴴ * Jm ε * (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε))) = Jm ε
    have hsb : star ((k : ℂ) • (star w ᵥ* Jm ε)) = (k : ℂ) • (Jm ε *ᵥ w) := by
      rw [star_smul, Matrix.star_vecMul, star_star, Jm_conjTranspose, Complex.star_def, Complex.conj_ofReal]
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_vecMulVec, hsb]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul,
      Matrix.mul_vecMulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, hq']
    ext i j
    simp only [Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination ((k : ℂ) * ((Jm ε *ᵥ w) i * (star w ᵥ* Jm ε) j)) * hkC
  · have hkc : (k : ℂ) * ((c : ℂ) - 1) = -1 := by linear_combination (-1 / 2 : ℂ) * hkC
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct,
      ← dotProduct_mulVec, hwz, smul_eq_mul, hkc, hw]
    ext i
    simp
  · calc hs (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)))
        = ∑ i, ∑ j, ‖(1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε))) i j‖ ^ 2 := rfl
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
            + 2 * (‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2))) := by
        gcongr with i _ j _
        rw [Matrix.sub_apply, vecMulVec_apply]
        have h3 := norm_sub_le ((1 : Matrix (Fin n) (Fin n) ℂ) i j) (w i * ((k : ℂ) • (star w ᵥ* Jm ε)) j)
        rw [norm_mul] at h3
        have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        have hp : (‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖) ^ 2 = ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2) := by
          rw [mul_pow, hbj]
        nlinarith [sq_nonneg (‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ - ‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖)]
      _ = 2 * n + 2 * (k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2) := by
        rw [← h1, ← h2]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * n + 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2 := by
        have hk2 : k ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hk2 (sq_nonneg (GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w))]

private theorem nsq_sub_le_two_mul_add {n : ℕ} (a b : Fin n → ℂ) :
    GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (a - b) ≤ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq a + 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq b := by
  unfold GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with i _
  simp only [Pi.sub_apply]
  have h := norm_sub_le (a i) (b i)
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]

private theorem nsq_nonneg_hilbert_schmidt_traces {n : ℕ} (a : Fin n → ℂ) : 0 ≤ GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq a :=
  Finset.sum_nonneg fun i _ => by positivity

theorem boost : ∀ {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ), star z ⬝ᵥ (Jm ε *ᵥ z) = 1 → nsq z = 1 → star y ⬝ᵥ (Jm ε *ᵥ y) = 1 → ∃ g : UJ ε, umat g *ᵥ z = y ∧ hs (umat g) ≤ 16 * ((n : ℝ) + nsq y) ^ 2 := by
  classical
  intro n ε z y hz hnz hy
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hz
    · exact h
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = star y ⬝ᵥ (Jm ε *ᵥ z) := ⟨_, rfl⟩
  obtain ⟨u, hu1, hua⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ star u * a = -(‖a‖ : ℂ) := by
    by_cases h0 : a = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn0 : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hsq : star a * a = (‖a‖ : ℂ) ^ 2 := by rw [Complex.star_def, Complex.conj_mul']
      refine ⟨-(a / (‖a‖ : ℂ)), ?_, ?_⟩
      · rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.mpr h0)]
      · rw [star_neg, star_div₀, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, neg_mul,
          div_mul_eq_mul_div, hsq, sq, mul_div_assoc, div_self hn0, mul_one]
  have hu2 : star u * u = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hu1]
    simp
  have hy' : star (u • y) ⬝ᵥ (Jm ε *ᵥ (u • y)) = 1 := by
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hy, smul_eq_mul,
      smul_eq_mul, mul_one, hu2]
  have hyz' : star (u • y) ⬝ᵥ (Jm ε *ᵥ z) = ((-‖a‖ : ℝ) : ℂ) := by
    rw [star_smul, smul_dotProduct, ← ha, smul_eq_mul, hua]
    push_cast
    ring
  obtain ⟨R, hR, hRz, hRs⟩ := refl_ex ε z (u • y) hz hy' (-‖a‖) (by simp) hyz'
  have hR' : Rᴴ * Jm ε * R = Jm ε := hR
  have hg : (star u • R)ᴴ * Jm ε * (star u • R) = Jm ε := by
    rw [conjTranspose_smul, star_star]
    simp only [Matrix.smul_mul, Matrix.mul_smul, hR', smul_smul]
    rw [hu2, one_smul]
  have hinv : (Jm ε * (star u • R)ᴴ * Jm ε) * (star u • R) = 1 := by
    rw [show Jm ε * (star u • R)ᴴ * Jm ε * (star u • R)
        = Jm ε * ((star u • R)ᴴ * Jm ε * (star u • R)) by simp only [Matrix.mul_assoc], hg, Jm_mul_self]
  refine ⟨⟨⟨star u • R, Jm ε * (star u • R)ᴴ * Jm ε, mul_eq_one_comm.mp hinv, hinv⟩, hg⟩, ?_, ?_⟩
  · show (star u • R) *ᵥ z = y
    rw [Matrix.smul_mulVec, hRz, smul_smul, hu2, one_smul]
  · show hs (star u • R) ≤ 16 * ((n : ℝ) + GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y) ^ 2
    have hsu : hs (star u • R) = hs R := by
      simp [hs, Matrix.smul_apply, norm_mul, norm_star, hu1]
    have hnu : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y) = GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y := by
      simp [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, norm_mul, hu1]
    have hD := nsq_sub_le_two_mul_add (u • y) z
    rw [hnu, hnz] at hD
    have hD0 := nsq_nonneg_hilbert_schmidt_traces (u • y - z)
    have hs0 := nsq_nonneg_hilbert_schmidt_traces y
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y - z) ^ 2 ≤ (2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y + 2 * 1) ^ 2 :=
      pow_le_pow_left₀ hD0 hD 2
    rw [hsu]
    nlinarith

end PositivityTheory.UnitaryDecomposition.X4
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem hs_trace {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : (hs X : ℂ) = trace (Xᴴ * X) := by
  simp only [hs, trace, diag_apply, Matrix.mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem jm_ct {m : ℕ} (ε : Fin m → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1; funext a
  simp only [Pi.star_apply]; split_ifs <;> simp

theorem stab : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → IsNormEmb ι ∧ (∀ h, hs (umat (ι h)) = hs (umat h) + 1) ∧ ∀ g : UJ ε, umat g *ᵥ z = z → ∃ h, ι h = g := by
  intro n r ε ε' ι z ⟨F, hF, FF, Fz, hz⟩
  set Z : Matrix (Fin n) Unit ℂ := replicateCol Unit z with hZ
  have col : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin n) ℂ), M * Z = replicateCol Unit (M *ᵥ z) := fun M => by
    ext i j; simp [hZ, Matrix.mul_apply, mulVec, dotProduct]
  have FZ : Fᴴ * Z = 0 := by rw [col, Fz]; ext; simp
  have ZF : Zᴴ * F = 0 := by simpa using congrArg conjTranspose FZ
  have ZZ : Zᴴ * Z = 1 := by
    ext i j
    have : ((nsq z : ℝ) : ℂ) = 1 := by rw [hz]; simp
    simp only [hZ, Matrix.mul_apply, conjTranspose_apply, replicateCol_apply, Complex.star_def, Complex.conj_mul', Subsingleton.elim i j,
      one_apply_eq]
    rw [← this, GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq]; push_cast; rfl
  have S : F * Fᴴ + Z * Zᴴ = 1 := by
    have e : Fin n ≃ Fin r ⊕ Unit := Fintype.equivOfCardEq (by simp [← hF.codim])
    have h1 : (fromCols F Z)ᴴ * fromCols F Z = 1 := by
      rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, FF, FZ, ZF, ZZ, fromBlocks_one]
    have h2 := (mul_eq_one_comm_of_equiv e.symm).1 h1
    rwa [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows] at h2
  have FJZ : Fᴴ * Jm ε * Z = 0 := by rw [col, hF.perp]; ext; simp
  have ZJF : Zᴴ * Jm ε * F = 0 := by
    have := congrArg conjTranspose FJZ
    simpa [jm_ct, Matrix.mul_assoc] using this
  have ZJZ : Zᴴ * Jm ε * Z = 1 := by
    ext i j
    rw [Matrix.mul_assoc, col, Subsingleton.elim i j, one_apply_eq, ← hF.one]
    simp [hZ, mul_apply, dotProduct]
  have JZ : Jm ε * Z = Z := by
    rw [← Matrix.one_mul (Jm ε * Z), ← S, Matrix.add_mul, Matrix.mul_assoc F, Matrix.mul_assoc Z, ← Matrix.mul_assoc Fᴴ,
      ← Matrix.mul_assoc Zᴴ, FJZ, ZJZ]; simp
  have A : ∀ h, umat (ι h) = F * umat h * Fᴴ + Z * Zᴴ := fun h => by
    rw [← Matrix.mul_one (umat (ι h)), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hF.act, col, hF.fix]
  have hsF : ∀ M : Matrix (Fin r) (Fin r) ℂ, trace ((F * M * Fᴴ)ᴴ * (F * M * Fᴴ)) = trace (Mᴴ * M) := fun M => by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Fᴴ F, FF, Matrix.one_mul, trace_mul_comm]
    simp only [Matrix.mul_assoc, FF, Matrix.mul_one]
  have cA : Continuous fun h => umat (ι h) := by
    simp only [A]
    exact ((continuous_const.matrix_mul Formalism.MainNotions.BridgeCSchur.continuous_umat).matrix_mul continuous_const).add continuous_const
  refine ⟨⟨?_, fun h => ?_⟩, fun h => ?_, fun g hg => ?_⟩
  · refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cA, ?_⟩)
    have : Continuous fun h => umat (ι h⁻¹) := cA.comp continuous_inv
    exact this.congr fun h => by rw [map_inv]; rfl
  · have : umat (ι h) - 1 = F * (umat h - 1) * Fᴴ := by
      rw [A, ← S, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
    exact_mod_cast (by rw [hs_trace, hs_trace, this, hsF] : (hs (umat (ι h) - 1) : ℂ) = hs (umat h - 1))
  · have : (hs (umat (ι h)) : ℂ) = hs (umat h) + 1 := by
      rw [hs_trace, hs_trace, A, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add,
        trace_add, hsF]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Fᴴ Z, FZ, ← Matrix.mul_assoc Zᴴ F, ZF, ← Matrix.mul_assoc Zᴴ Z, ZZ, Matrix.one_mul]
      simp [trace_mul_comm Z, ZZ]
    exact_mod_cast this
  · have gZ : umat g * Z = Z := by rw [col, hg]
    have gJ : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
    have ZgF : Zᴴ * (umat g * F) = 0 := by
      have h1 : Zᴴ = Zᴴ * (umat g)ᴴ * Jm ε := by
        rw [← conjTranspose_mul, gZ, ← jm_ct ε, ← conjTranspose_mul, JZ]
      calc _ = Zᴴ * (umat g)ᴴ * Jm ε * (umat g * F) := by rw [← h1]
        _ = Zᴴ * ((umat g)ᴴ * Jm ε * umat g) * F := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [gJ, ZJF]
    have gF : umat g * F = F * (Fᴴ * (umat g * F)) := by
      conv_lhs => rw [← Matrix.one_mul (umat g * F), ← S, Matrix.add_mul, Matrix.mul_assoc Z, ZgF, Matrix.mul_zero, add_zero,
        Matrix.mul_assoc]
    set h := Fᴴ * (umat g * F) with hh
    have hU : inUJ ε' h := by
      show hᴴ * Jm ε' * h = Jm ε'
      calc hᴴ * Jm ε' * h = (F * h)ᴴ * Jm ε * (F * h) := by
            rw [← hF.gram]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = Fᴴ * ((umat g)ᴴ * Jm ε * umat g) * F := by rw [← gF]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [gJ, hF.gram]
    refine ⟨indefiniteUnitaryMk ε' h hU, Subtype.ext (Units.ext ?_)⟩
    show umat _ = umat g
    rw [A, show umat (indefiniteUnitaryMk ε' h hU) = h from rfl, ← gF]
    conv_rhs => rw [← Matrix.mul_one (umat g), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gZ]

end PositivityTheory.UnitaryDecomposition.X4
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

section

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {σ : Γ → (A →L[ℂ] A)}

theorem uRep_of (h : IsU σ) : URep σ := by
  have hm : ∀ g k x, σ (g * k) x = σ g (σ k x) := fun g k x => by rw [h.mul]; rfl
  refine ⟨hm, fun g x y => ?_, h.norm, h.cont⟩
  have hy : y = σ g (σ g⁻¹ y) := by rw [← hm, mul_inv_cancel, h.one]; rfl
  conv_lhs => rw [hy]
  exact (LinearIsometry.mk (σ g : A →ₗ[ℂ] A) (h.norm g)).inner_map_map x _

variable [MeasurableSpace Γ] {ν : Measure Γ} {d : ℝ}

theorem eq_zero_of_orth (hd : IsFd ν σ d) {w u : A} (hw : w ≠ 0) (hu : ∀ g, ⟪u, σ g w⟫_ℂ = 0) : u = 0 := by
  have h := (hd.2 w u w u).2
  simp only [hu, zero_mul, integral_zero] at h
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  rcases mul_eq_zero.1 ((div_eq_zero_iff.1 h.symm).resolve_right hd0) with h | h
  · exact absurd (inner_self_eq_zero.1 h) hw
  · exact inner_self_eq_zero.1 h

end

end PositivityTheory.UnitaryDecomposition.X4
end
end
