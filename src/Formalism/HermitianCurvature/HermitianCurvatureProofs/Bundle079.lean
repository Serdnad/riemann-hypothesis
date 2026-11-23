module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle078
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsotropicNormalFormFullStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle023
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle027
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopActAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle028
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.StatementB
import Formalism.RealPlaceAnalysis.Bundle001

@[expose] public section

section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HaarScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem haar_smul {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (c : ℝ≥0) (hc : 0 < c) :
    IsHaarOn U (c • μ) := by
  apply Formalism.FourierDecayAlt.P.BesselScaling.haar_smul <;> assumption

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def scaleG (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) : RealPlaceData k r Wp Wq :=
  { D with μG := c • D.μG, haarG := haar_smul D.haarG c hc }

theorem iteratedDeriv_two_const_mul (c : ℂ) (f : ℝ → ℂ) :
    iteratedDeriv 2 (fun x => c * f x) = fun x => c * iteratedDeriv 2 f x := by
  have h2 : ∀ g : ℝ → ℂ, iteratedDeriv 2 g = deriv (deriv g) := by
    intro g
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h2, deriv_const_mul_field', deriv_const_mul_field']

theorem oneMinusDD_const_mul (c : ℂ) (h : ℝ → ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * h a b) t₁ t₂ = c * oneMinusDD h t₁ t₂ := by
  simp only [oneMinusDD, iteratedDeriv_two_const_mul, ← mul_sub]

variable [FiniteDimensional ℂ Wq]

theorem ph_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) :
    Ph (scaleG D c hc) F F' p = ((c : ℝ) : ℂ) * Ph D F F' p := by
  have hμ : (scaleG D c hc).μG = c • D.μG := rfl
  unfold Ph
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rfl

theorem betaInf_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    betaInf (scaleG D c hc) F F' = ((c : ℝ) : ℂ) * betaInf D F F' := by
  apply Formalism.FourierDecayAlt.P.BesselScaling.betaInf_scale <;> assumption

theorem beta_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    beta (scaleG D c hc) F F' = beta D F F' := rfl

end

end Formalism.FourierDecayAlt.P.HaarScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.HaarScaling

theorem lemma_b_normalised_of_parts : Formalism.FourierDecayAlt.B2.LemmaBNormFromParts := by
  intro hC hJ hD hI k r Wp Wq _ _ _ _ _ _ D A hA hF
  exact hC k r Wp Wq D A hA hF (hJ k r Wp Wq D) (hD k r Wp Wq D) (hI k r Wp Wq D A hA)

theorem lemma_b_any_measure_from_normalised : Formalism.FourierDecayAlt.B2.LemmaBAnyFromNorm := by
  intro hN hB k r Wp Wq _ _ _ _ _ _ D A hA
  obtain ⟨c, ⟨hc, hF⟩, -⟩ := hB k r Wp Wq D
  have hF' : IntFormula (scaleG D c hc) := hF
  obtain ⟨h1, h2, h3, h4⟩ := hN k r Wp Wq (scaleG D c hc) A hA hF'
  refine ⟨c, hc, hF, h1, ?_, ?_, h4⟩
  · intro F F' hF1 hF2
    rw [← beta_scale D c hc F F', h2 F F' hF1 hF2, betaInf_scale]
  · intro UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4 hIC
    exact h3 UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4
      (fun p hp T hT i j hij hj => (hIC p hp T hT i j hij hj).smul_measure_nnreal)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.HaarScaling

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end Formalism.FourierDecayAlt.P.HaarScaling
end
end

section

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

section nf

variable {k r : ℕ}

theorem zb_last_row (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) (a b : ℕ) (ha : a ≠ i0)
    (ha' : a + 1 < i0 + s) (hb : b = i0) : C3.Zb i0 s hh t a b = 0 := by
  subst hb
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem zb_col_last (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) (a : ℕ) (ha : a ≠ i0)
    (ha' : a + 1 < i0 + s) : C3.Zb i0 s hh t a (i0 + s - 1) = 0 := by
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem corner_matrix_last_entry (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) :
    C3.Zb i0 s hh t i0 (i0 + s - 1) = t := by
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem corner_matrix_first_line_zero (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) (b : ℕ) (hb : b + 1 < i0 + s) :
    C3.Zb i0 s hh t i0 b = 0 := by
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem herm_bvec_right (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec p) = WeylGroupFacts.sgn k r p * v (WeylGroupFacts.tau k r p) := by
  have hs : star (Pi.single p (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single p 1 := by
    ext q
    by_cases h : q = p
    · subst h
      simp
    · simp [Pi.single_apply, h]
  unfold herm bvec
  rw [hs, single_dotProduct, one_mul, SignAntidiagonal.mulVec_hpk]

theorem nf_top (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hT' : herm (Hpk k r) z' z' ≠ 0)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : γ ∈ UH (Hpk k r)) (i0 s : ℕ) (hs : 2 ≤ s)
    (hj : i0 + s = r + 1) (hh : Matrix (Fin i0) (Fin i0) ℂ) (hdet : hh.det ≠ 0) (t : ℂ) (ht : t ≠ 0)
    (hZ : ∀ a b : Fin (r + 1), Zhat k r z z' γ a b = C3.Zb i0 s hh t a.val b.val) :
    ∃ n0 ∈ C3.N0set k r z', ∃ yb : Fin (2 * r + k + 1) → ℂ, inWb k r yb ∧ herm (Hpk k r) z' yb = t ∧
      (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val ≠ i0 →
        PBG.xi0 (γ * n0) a p = if p.val < r ∧ p.val ≠ i0 then C3.Zb i0 s hh t a.val p.val else 0) ∧
      (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val = i0 → PBG.xi0 (γ * n0) a p = herm (Hpk k r) (bvec p) yb) := by
  obtain ⟨s'', rfl⟩ : ∃ s'', s = s'' + 2 := ⟨s - 2, by omega⟩
  obtain rfl : r = i0 + s'' + 1 := by omega
  have hγi : γ⁻¹ ∈ UH (Hpk k (i0 + s'' + 1)) := WeylGroupFacts.uh_inv hγ
  have hγu := WeylGroupFacts.isUnit_of_uh hγ
  set y : Fin (i0 + s'' + 1) → Fin (2 * (i0 + s'' + 1) + k + 1) → ℂ := fun a => γ⁻¹ *ᵥ bvec (eI k _ a) with hy
  set i : Fin (i0 + s'' + 1) := ⟨i0, by omega⟩ with hi

  have hyS : ∀ (a b : Fin (i0 + s'' + 1)), y a (esI k _ b) = star (C3.Zb i0 (s'' + 2) hh t a.val b.val) := by
    intro a b
    simp only [hy]
    rw [(xi_Y_zhat_identity k _ z z' γ a b hγ).2, hZ]
    rfl
  have hfz' : fvec k (i0 + s'' + 1) z' (Fin.last _) = z' := by unfold fvec; rw [dite_eq_right (by simp)]
  have hfa : ∀ a : Fin (i0 + s'' + 1), fvec k _ z a.castSucc = bvec (eI k _ a) := by
    intro a; unfold fvec; rw [dite_eq_left (by have := a.isLt; simp; omega)]; rfl
  have hyz : ∀ a : Fin (i0 + s'' + 1), herm (Hpk k _) z' (y a) = C3.Zb i0 (s'' + 2) hh t a.val (i0 + s'' + 1) := by
    intro a
    have h1 : herm (Hpk k _) z' (y a) = herm (Hpk k _) (γ *ᵥ z') (γ *ᵥ y a) := (herm_unitary γ hγ _ _).symm
    have h2 : γ *ᵥ y a = bvec (eI k _ a) := by
      rw [hy]; simp only
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hγu, Matrix.one_mulVec]
    rw [h1, h2]
    have := hZ a.castSucc (Fin.last _)
    simp only [Zhat, hfz', hfa] at this
    rw [this]
    simp
  obtain ⟨n0, hn0, y', hy'⟩ := isotropicNormalFormFull_statement k (i0 + s'') z' i y t hz' hT' ht
    (by
      intro a ha
      rw [hyS]
      have : C3.Zb i0 (s'' + 2) hh t a.val i0 = 0 :=
        zb_last_row i0 _ hh t (by omega) a.val i0 (fun h => ha (Fin.ext h)) (by omega) rfl
      show star (C3.Zb i0 (s'' + 2) hh t a.val i0) = 0
      rw [this, star_zero])
    (by
      intro p hp
      have hb : 2 * (i0 + s'' + 1) + k - p.val < i0 + s'' + 1 := by omega
      have hpe : p = esI k _ ⟨2 * (i0 + s'' + 1) + k - p.val, hb⟩ := by ext; simp [esI]; omega
      rw [hpe, hyS]
      have : C3.Zb i0 (s'' + 2) hh t i0 (2 * (i0 + s'' + 1) + k - p.val) = 0 :=
        corner_matrix_first_line_zero i0 _ hh t (by omega) _ (by omega)
      simp [hi, this])
    (by
      have hP := third_polynomial_expansion i0 s'' hh t
      have hS := (sign_permutation_identity s'').2
      have hsg : C3.sgnW s'' ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hS; exact (by norm_num : (0 : ℂ) ≠ -1) hS
      have hne : (Matrix.of fun a b : Fin (i0 + s'') => C3.Zb i0 (s'' + 2) hh t
          ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
          ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val).det ≠ 0 := by
        rw [hP]; exact mul_ne_zero (mul_ne_zero hdet (pow_ne_zero _ ht)) hsg
      have e : (Matrix.of fun a b : Fin (i0 + s'') => y (i.succAbove a) (esI k (i0 + s'' + 1) (i.succAbove b))) =
          (Matrix.of fun a b : Fin (i0 + s'') => C3.Zb i0 (s'' + 2) hh t
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val).map (starRingEnd ℂ) := by
        ext a b; simp [hyS, hi]
      rw [e]
      change ((starRingEnd ℂ).mapMatrix _).det ≠ 0
      rw [← RingHom.map_det]
      exact (map_ne_zero _).2 hne)
    (by
      intro a ha
      rw [hyz]
      have := zb_col_last i0 (s'' + 2) hh t (by omega) a.val (fun h => ha (Fin.ext h)) (by omega)
      rwa [show i0 + (s'' + 2) - 1 = i0 + s'' + 1 by omega] at this)
    (by
      rw [hyz]
      have := corner_matrix_last_entry i0 (s'' + 2) hh t (by omega)
      rwa [show i0 + (s'' + 2) - 1 = i0 + s'' + 1 by omega] at this)
    (by
      intro a a'
      rw [hy]; simp only
      rw [herm_unitary _ hγi, herm_bvec_bvec]
      have := a.isLt
      have := a'.isLt
      unfold Hpk
      rw [if_neg (fun h => by simp only [eI] at h; omega), if_neg (fun h => by simp only [eI] at h; omega),
        if_neg (fun h => by simp only [eI] at h; omega)])

  have hn0u : n0 ∈ UH (Hpk k (i0 + s'' + 1)) := hn0.1
  have hxi : ∀ (a : Fin (i0 + s'' + 1)) (p : Fin (2 * (i0 + s'' + 1) + k + 1)),
      PBG.xi0 (γ * n0) a p = herm (Hpk k _) (bvec p) (y' a) := by
    intro a p
    unfold PBG.xi0
    have h2 : bvec (eI k _ a) = γ *ᵥ y a := by
      rw [hy]; simp only
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hγu, Matrix.one_mulVec]
    rw [h2, ← Matrix.mulVec_mulVec, herm_unitary γ hγ, ← (hy' a).1, herm_unitary n0 hn0u]
  refine ⟨n0, hn0, y' i, ((hy' i).2.2 rfl).1, ((hy' i).2.2 rfl).2, ?_, ?_⟩
  · intro a p ha
    have hai : a ≠ i := fun h => ha (by rw [h])
    obtain ⟨hz0, hsame⟩ := (hy' a).2.1 hai
    rw [hxi, herm_swap, herm_bvec_right]
    by_cases hp : p.val < i0 + s'' + 1
    ·
      have htau : WeylGroupFacts.tau k _ p = esI k _ ⟨p.val, hp⟩ := by
        ext; rw [tau_val, if_pos (Or.inl hp)]; simp [esI]
      have hsg : WeylGroupFacts.sgn k _ p = 1 := sgn_one _ (by omega)
      rw [htau, hsg, one_mul, hsame _ (by simp [esI]; omega), hyS, star_star]
      by_cases hpi : p.val = i0
      · rw [if_neg (by omega)]
        exact zb_last_row i0 _ hh t (by omega) a.val p.val ha (by omega) hpi
      · rw [if_pos ⟨hp, hpi⟩]
    · rw [if_neg (by omega)]
      have hle : (WeylGroupFacts.tau k _ p).val ≤ i0 + s'' + 1 + k := by
        rw [tau_val]; split_ifs <;> omega
      rw [hz0 _ hle]
      simp
  · intro a p ha
    have hai : a = i := Fin.ext ha
    subst hai
    rw [hxi]

end nf

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.TwoByOneBlock

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma bigCell_mulVec_jV (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    bigCell k r c μ *ᵥ jV k r u = jV k r (μ *ᵥ u) := by
  rw [← emb_mulVec_jV (r := r) μ u]
  ext i
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hj1 : ¬ j.val < r := by omega
    have e : bigCell k r c μ i j = Formalism.FourierDecayAlt.B2.embWb k r μ i j := by
      simp only [bigCell, Formalism.FourierDecayAlt.B2.embWb, dif_neg hj1, dif_pos hj.2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dif_pos hi, dif_pos ⟨hi, hj⟩]
      · rw [dif_neg hi, dif_neg (fun h => hi h.1)]
        rw [if_neg]
        rintro ⟨rfl, h2⟩
        exact h2 hj
    rw [e]
  · have h0 : jV k r u j = 0 := by simp only [jV, dif_neg hj]
    rw [h0, mul_zero, mul_zero]

lemma herm_bigCell (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  conv_lhs => rw [← jV_wbPart hz', ← jV_wbPart hz]
  rw [bigCell_mulVec_jV, herm_jV]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gqDom (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    gq D q ∈ Om k r D.z D.z' := by
  obtain ⟨hc, hζ⟩ := hq
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  refine ⟨big_cell_mem_holds k r q.1 _ hc hsec.1, ?_, ?_⟩
  · intro l hl
    have h := hmin.1 ⟨l.val, by omega⟩
    have hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l := Fin.ext rfl
    show Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) l ≠ 0
    rw [← hl', h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  · have hz := hmin.2.2 hc
    rw [herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    show 0 < Gf k r D.z D.z' (gq D q)
    unfold Gf gq
    rw [hlast, ← hP, Complex.normSq_mul]
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

theorem _root_.Formalism.FourierDecayAlt.P.big_cell_domain : GqDom := fun _ _ _ _ _ _ _ _ D _ hq => gqDom D hq

end Formalism.FourierDecayAlt.P.BigCellHermitian
end
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem top_action_on_gauge_holds : GTRTopAct := TopAct.gTRTopAct_of_cut quadratic_top_algebra_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

theorem Formalism.FourierDecayAlt.P.derivative_cost_bound : Formalism.FourierDecayAlt.U.DerivativeCost := by
  have hS : Formalism.FourierDecayAlt.U.SliceMem := Formalism.FourierDecayAlt.P.slice_membership
  have h21 : Formalism.FourierDecayAlt.U.SliceCoordinateSizes :=
    Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_hypotheses hS Formalism.FourierDecayAlt.P.block3_apply_embedding Formalism.FourierDecayAlt.P.aux_statement_17
      Formalism.FourierDecayAlt.P.hat_z_on_slice
  exact operator_word_cost hS Formalism.FourierDecayAlt.P.radical_parametrisation Formalism.FourierDecayAlt.P.slice_right_coordinates
    Formalism.FourierDecayAlt.P.slice_left_coordinates Formalism.FourierDecayAlt.P.slice_z_coordinates Formalism.FourierDecayAlt.P.directions_in_parabolic h21
end

section

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.ListSumInequalities

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma list_sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (h : β → M) :
    ((L.flatMap f).map h).sum = (L.map fun a => ((f a).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma norm_list_sum_le {α : Type*} (L : List α) (f : α → E) :
    ‖(L.map f).sum‖ ≤ (L.map fun a => ‖f a‖).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma list_sum_le {α : Type*} (L : List α) (f f' : α → ℝ) (h : ∀ a ∈ L, f a ≤ f' a) :
    (L.map f).sum ≤ (L.map f').sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma list_sum_nonneg {α : Type*} (L : List α) (f : α → ℝ) (h : ∀ a ∈ L, 0 ≤ f a) : 0 ≤ (L.map f).sum := by
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact h a ha)

end Formalism.FourierDecayAlt.P.ListSumInequalities

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end
