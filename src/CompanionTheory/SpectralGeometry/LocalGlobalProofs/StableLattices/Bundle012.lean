module

public import Formalism.RealPlaceAnalysis.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle001
public import Mathlib.Analysis.Matrix.Spectrum
public import Formalism.RealPlaceAnalysis.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import GroundTheory.AutomorphicForms.Cartan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix ReciprocityTheory.ChartRestriction.DS

open scoped ComplexOrder in
theorem GlobalTheory.T.inverse_gram_eigenvalues_sum_hs (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε)
    (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) :
    (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) := by
  have hmul : S7.toM g * S7.toM g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = 1
    simp
  have hinj : Function.Injective (S7.toM g⁻¹).mulVec := by
    intro x y hxy
    have h := congrArg (S7.toM g).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hmul] using h
  have hpd : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ hinj
  refine ⟨fun i => hpd.eigenvalues_pos i, ?_⟩
  have hre : ∑ i, hT.eigenvalues i = (Matrix.trace ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹)).re := by
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
      (congrArg Complex.re hT.trace_eq_sum_eigenvalues).symm
  have hs_ct (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs Mᴴ = Formalism.REAL.hs M := by
    delta Formalism.REAL.hs
    simp only [Matrix.conjTranspose_apply, norm_star]
    exact Finset.sum_comm
  have hs_j_left (M : Matrix (Fin n) (Fin n) ℂ) :
      Formalism.REAL.hs (Formalism.REAL.Jm ε * M) = Formalism.REAL.hs M := by
    have h : ∀ a, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
    delta Formalism.REAL.hs Formalism.REAL.Jm
    simp only [Matrix.diagonal_mul, norm_mul, h, one_mul]
  have hs_j_right (M : Matrix (Fin n) (Fin n) ℂ) :
      Formalism.REAL.hs (M * Formalism.REAL.Jm ε) = Formalism.REAL.hs M := by
    rw [← hs_ct, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose, hs_j_left, hs_ct]
  have hhs : Formalism.REAL.hs (S7.toM g⁻¹) = Formalism.REAL.hs (S7.toM g) := by
    rw [S7.toM_inv]
    show Formalism.REAL.hs (Formalism.REAL.Jm ε * (S7.toM g)ᴴ * Formalism.REAL.Jm ε) = _
    rw [hs_j_right, hs_j_left, hs_ct]
  rw [hre, ← Formalism.REAL.f1auxiliary_hs_eq, hhs]

theorem GlobalTheory.CompanionTheory.UGeo.specpos_inv_eigenvalues (n : ℕ) (ε : Fin n → Bool)
    (g : S7.UJ ε) (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) :
    (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) :=
  GlobalTheory.T.inverse_gram_eigenvalues_sum_hs n ε g hT
end

section

open Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

namespace GlobalTheory.CompanionTheory.RgExhHecke

theorem capEntry_eq_Tm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (x : ℂ) (a b : Fin n) : capEntry E x a b = Tm E x a b := by
  unfold capEntry Tm
  exact add_comm _ _

theorem qdet_eq_capelliC {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (x : ℂ) : qdet E x = capelliC E x := by
  unfold qdet qminor capelliC cminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [capEntry_eq_Tm, zsmul_eq_mul]

theorem qdetEq : ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (x : ℂ), qdet E x = capelliC E x :=
  fun _ _ _ _ E x => qdet_eq_capelliC E x

end GlobalTheory.CompanionTheory.RgExhHecke
end

section

namespace GlobalTheory.CompanionTheory.Dblock.CartanDVR

open Matrix

theorem cartan_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (ϖ : R), Irreducible ϖ →
    ∀ g : Matrix (Fin n) (Fin n) K, IsUnit g.det →
      ∃ (u v : Matrix (Fin n) (Fin n) R) (a : Fin n → ℤ), IsUnit u.det ∧ IsUnit v.det ∧ Antitone a ∧
        g = u.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) *
          v.map (algebraMap R K) := by
  intro R K _ _ _ _ _ _ n ϖ hϖ g hg
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Fin n × Fin n => g p.1 p.2)
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose A' hA' using hb
  let A : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => A' (i, j)
  have hAg : A.map (algebraMap R K) = algebraMap R K (b : R) • g := by
    ext i j
    simpa [A, Algebra.smul_def] using hA' (i, j)
  have hbK : algebraMap R K (b : R) ≠ 0 := fun h => hb0 (hinj (by simpa using h))
  have hA : A.det ≠ 0 := by
    intro h
    have h1 : (A.map (algebraMap R K)).det = 0 := by
      have := RingHom.map_det (algebraMap R K) A
      rw [h, map_zero] at this
      simpa using this.symm
    rw [hAg, Matrix.det_smul] at h1
    exact (mul_ne_zero (pow_ne_zero _ hbK) hg.ne_zero) h1
  obtain ⟨P, Q, e, he, hPQ⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagonal_pow_mul hϖ A hA
  obtain ⟨c, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖK : algebraMap R K ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by simpa using h))
  have hwK : algebraMap R K (w : R) ≠ 0 := fun h => w.ne_zero (hinj (by simpa using h))
  have hPd : IsUnit (P : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  have hQd : IsUnit (Q : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit
  refine ⟨((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R), Q, fun i => (e i : ℤ) - c, ?_, hQd, ?_, ?_⟩
  · rw [Matrix.det_smul]
    exact ((Units.isUnit _).pow _).mul hPd
  · intro i j hij
    have := he hij
    simp only
    omega
  · have hwinv : algebraMap R K ((w⁻¹ : Rˣ) : R) = (algebraMap R K (w : R))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul]
      simp
    have hdiag : Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ ((e i : ℤ) - c)) =
        ((algebraMap R K ϖ) ^ c)⁻¹ • (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [zpow_sub₀ hϖK, div_eq_mul_inv, mul_comm]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have hmap : A.map (algebraMap R K) = (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) *
        (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) *
        (Q : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      rw [hPQ]
      simp only [Matrix.map_mul]
    have hsm : (((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R)).map (algebraMap R K) =
        (algebraMap R K (w : R))⁻¹ • (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      ext i j
      simp [hwinv]
    rw [hsm, hdiag, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, ← hmap, hAg,
      smul_smul, hw]
    have : (algebraMap R K (w : R))⁻¹ * ((algebraMap R K ϖ) ^ c)⁻¹ *
        algebraMap R K ((w : R) * ϖ ^ c) = 1 := by
      rw [map_mul, map_pow]
      field_simp
    rw [this, one_smul]

end GlobalTheory.CompanionTheory.Dblock.CartanDVR
end
