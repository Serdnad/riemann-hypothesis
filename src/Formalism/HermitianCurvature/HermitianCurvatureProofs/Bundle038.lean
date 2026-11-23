module

public import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.HermitianCurvature.Bundle006
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.OperatorsCommuteTranslations

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

def TypeComm : Prop :=
  ∀ (P : M.Par) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)) (z e : Fin (2 * P.r + P.k + 1) → ℂ) (TP : Top.TypeProj P π z e),
    IsCRepOn (UWset P.k P.r z) π → ContinuousOn π (UWset P.k P.r z) →
    (∀ h ∈ UWset P.k P.r z, ∀ v, ‖π h v‖ = ‖v‖) →
    1 ≤ P.k → inWb P.k P.r z → 0 < Tz P.k P.r z → inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 →
    herm (Hpk P.k P.r) e e = 1 →
    ∀ g ∈ UWset P.k P.r z, ∀ l : ℂ, g *ᵥ e = l • e → ∀ ρ, (TP.E ρ).comp (π g) = (π g).comp (TP.E ρ)

def HouseMeas : Prop :=
  ∀ (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ), inWb k r z → (herm (Hpk k r) z z).re < 0 →
    inWb k r e → herm (Hpk k r) e z = 0 → herm (Hpk k r) e e = 1 →
    ∃ h : (Fin (2 * r + k + 1) → ℂ) → B.Mat k r, Measurable h ∧ (∀ u, h u ∈ UWset k r z) ∧
      ∀ u, inWb k r u → herm (Hpk k r) u z = 0 → u ≠ 0 → ∃ l : ℂ, h u *ᵥ u = l • e

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
end

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x5

variable {k r : ℕ}

lemma herm_sum_smul {n : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (x : ι → ℂ)
    (v : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ c, x c • v c) w = ∑ c, x c * herm H (v c) w := by
  simp only [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

lemma hzz_real (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
  have h := ggHerm_swap (Hpk k r) (GBasic.Hpk_herm k r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    simp only [Complex.ofReal_im]; linarith

lemma hzz_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  rw [hzz_real]; exact_mod_cast (neg_ne_zero.mpr hz.ne')

lemma herm_f_es {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    herm (Hpk k r) (fvec k r z c) (bvec (esI k r a)) = if c.val = a.val then 1 else 0 := by
  rw [bvec, ggHerm_bvec_right]
  have hlt : r + k < (esI k r a).val := by simp [esI]; omega
  rw [gn_Hpk_mulVec, dite_eq_left (Or.inr hlt)]
  have e : (⟨2 * r + k - (esI k r a).val, by omega⟩ : Fin (2 * r + k + 1)) = ⟨a.val, by omega⟩ := by
    apply Fin.ext; simp [esI]; omega
  rw [e, fvec_apply_lt z hz c _ (by simp)]

lemma herm_e_alt {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Fin (2 * r + k + 1))
    (hx : x.val < r ∨ r + k < x.val) : herm (Hpk k r) (bvec x) z = 0 := by
  rw [ggHerm_swap (Hpk k r) (GBasic.Hpk_herm k r), bvec, ggHerm_bvec_right, ggHpk_mulVec_Wb k r z hz,
    hz x hx, mul_zero, star_zero]

lemma hermitian_form_flag_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z c) z = if c.val = r then herm (Hpk k r) z z else 0 := by
  unfold fvec
  split_ifs with h1 h2 h2
  · omega
  · exact herm_e_alt hz _ (Or.inl (by simp [eI, h1]))
  · rfl
  · omega

lemma uMap_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (s : B.Mat k r)
    (U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (h : ∀ b, s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c) :
    C2.uMap k r z s = U := by
  ext a b
  unfold C2.uMap
  rw [h b]
  split_ifs with ha
  · rw [herm_sum_smul]
    simp only [herm_f_es hz.1]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; rw [if_neg (fun e => hc (Fin.ext e)), mul_zero]
    · simp
  · rw [herm_sum_smul]
    simp only [hermitian_form_flag_vector hz.1]
    rw [Finset.sum_eq_single a]
    · rw [if_pos (by have := a.isLt; omega)]
      field_simp [hzz_ne hz.2]
    · intro c _ hc
      rw [if_neg, mul_zero]
      intro e; apply hc; apply Fin.ext; have := a.isLt; omega
    · simp

lemma colEq {z : Fin (2 * r + k + 1) → ℂ} {s : B.Mat k r} {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (h : s * Fm k r z = Fm k r z * U) (b : Fin (r + 1)) :
    s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c := by
  funext i
  have := congrFun (congrFun h i) b
  simp only [Matrix.mul_apply, Fm, Matrix.of_apply] at this
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)

end C2x5

open C2x5

theorem unipotent_map_frame : C2.UMapFrame := by
  intro k r z hz
  refine ⟨fun s hs => ?_, fun h hh => ?_⟩
  · obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    have hu := uMap_eq hz s U (colEq hsF)
    refine ⟨by rw [hu]; exact colEq hsF, by rw [hu]; exact ⟨fun i j h => hU1 i j h, hU2⟩, fun t ht => ?_⟩
    obtain ⟨Ut, _, _, htF⟩ := S_F hz.1 ht
    have hut := uMap_eq hz t Ut (colEq htF)
    have hst : s * t * Fm k r z = Fm k r z * (U * Ut) := by
      rw [Matrix.mul_assoc, htF, ← Matrix.mul_assoc, hsF, Matrix.mul_assoc]
    rw [uMap_eq hz (s * t) (U * Ut) (colEq hst), hu, hut]
  · have h1 : h * Fm k r z = Fm k r z * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
      rw [UW_F hh, Matrix.mul_one]
    exact uMap_eq hz h 1 (colEq h1)

theorem zhat_equivalence : C2.ZhatEquiv := by
  intro k r z z' hz hz' s hs s' hs' g
  obtain ⟨U, _, _, hsF⟩ := S_F hz.1 hs
  obtain ⟨U', _, _, hs'F⟩ := S_F hz'.1 hs'
  rw [uMap_eq hz s U (colEq hsF), uMap_eq hz' s' U' (colEq hs'F), Zhat_eq, Zhat_eq]
  have hsU : sᴴ * Hpk k r * s = Hpk k r := Sset_UH hs
  have hu : IsUnit s.det := WeylGroupFacts.isUnit_of_uh hsU
  have hHs : Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
    calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hsU]
      _ = sᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  calc (Fm k r z)ᴴ * Hpk k r * (s⁻¹ * g * s') * Fm k r z'
      = (Fm k r z)ᴴ * (Hpk k r * s⁻¹) * g * (s' * Fm k r z') := by simp only [Matrix.mul_assoc]
    _ = (Fm k r z)ᴴ * (sᴴ * Hpk k r) * g * (Fm k r z' * U') := by rw [hHs, hs'F]
    _ = (s * Fm k r z)ᴴ * Hpk k r * g * Fm k r z' * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Fm k r z * U)ᴴ * Hpk k r * g * Fm k r z' * U' := by rw [hsF]
    _ = Uᴴ * ((Fm k r z)ᴴ * Hpk k r * g * Fm k r z') * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P
end

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

section N1

variable {k r : ℕ}

theorem tau_val (p : Fin (2 * r + k + 1)) :
    (tau k r p).val = if p.val < r ∨ r + k < p.val then 2 * r + k - p.val else p.val := rfl

theorem sgn_one (p : Fin (2 * r + k + 1)) (h : p.val ≠ r + k) : WeylGroupFacts.sgn k r p = 1 := by
  unfold WeylGroupFacts.sgn; rw [if_neg h]

theorem mulVec_hpk (v : Fin (2 * r + k + 1) → ℂ) (l : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) l = WeylGroupFacts.sgn k r l * v (tau k r l) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (tau k r l)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm; rw [hpk_row, if_neg hm, zero_mul]
  · simp

theorem herm_expand (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ l, star (w l) * (WeylGroupFacts.sgn k r l * v (tau k r l)) := by
  unfold herm; simp only [dotProduct, mulVec_hpk, Pi.star_apply]





end N1

section MajorantSquareBound

variable {k r : ℕ}

end MajorantSquareBound

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem coef_eq {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) {z Y z' : Mx k r}
    (hz : z ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hY : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : z' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (w : H) :
    ⟪σ z w, σ Y (σ z' w)⟫_ℂ = ⟪w, σ (z⁻¹ * Y * z') w⟫_ℂ := by
  have hzi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hz
  have hiso := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hds).2 z hz
  have hM : z⁻¹ * Y * z' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hzi.1 hY) hz'
  have h1 : σ Y (σ z' w) = σ z (σ (z⁻¹ * Y * z') w) := by
    have e1 : σ (Y * z') = (σ Y).comp (σ z') := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds hY hz'
    have e2 : σ (z * (z⁻¹ * Y * z')) = (σ z).comp (σ (z⁻¹ * Y * z')) :=
      Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds hz hM
    have e3 : z * (z⁻¹ * Y * z') = Y * z' := by
      rw [← mul_assoc, ← mul_assoc, hzi.2.1, one_mul]
    rw [e3] at e2
    have h2 := congrArg (fun T => T w) (e1.symm.trans e2)
    simpa using h2
  rw [h1]
  exact (⟨(σ z).toLinearMap, hiso⟩ : H →ₗᵢ[ℂ] H).inner_map_map w _

theorem gN_sandwich (hNI : NormInv) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ}
    (hb : 0 ≤ b) :
    B.gN (x⁻¹ * A * y) ^ (-b) ≤ (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by
  have hN := hNI k r
  have hxi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hx
  have hyi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hy
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hxi.1 hA) hy
  have hm1 := (hN.2 _ hM).2
  have ha1 := (hN.2 _ hA).2
  have hx1 := (hN.2 _ hx).2
  have hy1 := (hN.2 _ hy).2
  have hyinv := (hN.2 _ hy).1
  have hAeq : x * (x⁻¹ * A * y) * y⁻¹ = A := by
    rw [show x * (x⁻¹ * A * y) * y⁻¹ = (x * x⁻¹) * A * (y * y⁻¹) by simp only [mul_assoc],
      hxi.2.1, hyi.2.1, one_mul, mul_one]
  have hle : B.gN A ≤ (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by
    calc B.gN A = B.gN (x * (x⁻¹ * A * y) * y⁻¹) := by rw [hAeq]
      _ ≤ B.gN (x * (x⁻¹ * A * y)) * B.gN y⁻¹ := hN.1 _ _
      _ ≤ B.gN x * B.gN (x⁻¹ * A * y) * B.gN y⁻¹ :=
          mul_le_mul_of_nonneg_right (hN.1 _ _) (by rw [hyinv]; linarith)
      _ = (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by rw [hyinv]; ring
  have hp : 0 < B.gN x * B.gN y := mul_pos (by linarith) (by linarith)
  have hmb : 0 < B.gN (x⁻¹ * A * y) ^ b := Real.rpow_pos_of_pos (by linarith) b
  have hab : 0 < B.gN A ^ b := Real.rpow_pos_of_pos (by linarith) b
  have key : B.gN A ^ b ≤ (B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b := by
    rw [← Real.mul_rpow hp.le (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hle hb
  rw [Real.rpow_neg (show (0:ℝ) ≤ B.gN (x⁻¹ * A * y) by linarith),
    Real.rpow_neg (show (0:ℝ) ≤ B.gN A by linarith)]
  calc (B.gN (x⁻¹ * A * y) ^ b)⁻¹
        = (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * B.gN A ^ b * (B.gN A ^ b)⁻¹ := by
          exact (mul_inv_cancel_right₀ hab.ne' _).symm
    _ ≤ (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * ((B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b) *
          (B.gN A ^ b)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (inv_nonneg.2 hmb.le))
          (inv_nonneg.2 hab.le)
    _ = (B.gN x * B.gN y) ^ b * (B.gN A ^ b)⁻¹ := by
        rw [mul_comm ((B.gN x * B.gN y) ^ b) (B.gN (x⁻¹ * A * y) ^ b), inv_mul_cancel_left₀ hmb.ne']

end Formalism.FourierDecayAlt.P.S3dx4
end
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SandwichRhoAction

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma deriv_comp_of_leftInv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (M : F →L[ℝ] E) (hML : ∀ x, M (L x) = x) (φ : ℝ → E) (t : ℝ) :
    deriv (fun s => L (φ s)) t = L (deriv φ t) := by
  by_cases h : DifferentiableAt ℝ φ t
  · exact (L.hasFDerivAt.comp_hasDerivAt t h.hasDerivAt).deriv
  · have h' : ¬ DifferentiableAt ℝ (fun s => L (φ s)) t := by
      intro hd
      apply h
      have hφ : (fun s => M (L (φ s))) = φ := funext fun s => hML (φ s)
      rw [← hφ]
      exact M.differentiableAt.comp t hd
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h', map_zero]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sandw (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  (((ContinuousLinearMap.compL ℂ Wq Wp Wp P).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip Q)).restrictScalars ℝ)

lemma sandw_apply (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) (A : Wq →L[ℂ] Wp) : sandw P Q A = P.comp (A.comp Q) := rfl

lemma rho_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) (φ : Mat k r → (Wq →L[ℂ] Wp)) (x : Mat k r) :
    rho D p φ x = sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) (φ (sgs p x)) := rfl

lemma sandw_leftInv (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (A : Wq →L[ℂ] Wp) :
    sandw (D.π (Matrix.of p.1.1)⁻¹) (D.π' (Matrix.of p.2.1))
      (sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) A) = A := by
  have h1 := hp.1
  have h3 := hp.2.2.1
  have u1 := WeylGroupFacts.isUnit_of_uh h1.1
  have u3 := WeylGroupFacts.isUnit_of_uh h3.1
  have e1 : (D.π (Matrix.of p.1.1)⁻¹).comp (D.π (Matrix.of p.1.1)) = 1 := by
    rw [← D.π_rep.2 _ (WeylGroupFacts.uw_inv h1) _ h1, Matrix.nonsing_inv_mul _ u1, D.π_rep.1]
  have e3 : (D.π' (Matrix.of p.2.1)⁻¹).comp (D.π' (Matrix.of p.2.1)) = 1 := by
    rw [← D.π'_rep.2 _ (WeylGroupFacts.uw_inv h3) _ h3, Matrix.nonsing_inv_mul _ u3, D.π'_rep.1]
  have re : ∀ (P1 P2 : Wp →L[ℂ] Wp) (Q1 Q2 : Wq →L[ℂ] Wq) (B : Wq →L[ℂ] Wp),
      P1.comp ((P2.comp (B.comp Q2)).comp Q1) = (P1.comp P2).comp (B.comp (Q2.comp Q1)) := by
    intros; ext; rfl
  simp only [sandw_apply]
  rw [re, e1, e3]
  ext; rfl

lemma sgs_eq' (p : SS k r) (x : Mat k r) : sgs p x = (sL p)⁻¹ * x * sR p := by
  unfold sgs sL sR
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

lemma isUnit_sL (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : IsUnit (sL p).det :=
  WeylGroupFacts.isUnit_of_uh (WeylGroupFacts.uh_mul hp.2.1.1 hp.1.1)

lemma isUnit_sR (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : IsUnit (sR p).det :=
  WeylGroupFacts.isUnit_of_uh (WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1)

lemma sgs_curveR (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X g : Mat k r) (t : ℝ) :
    sgs p (g * NormedSpace.exp ((t : ℂ) • X)) = sgs p g * NormedSpace.exp ((t : ℂ) • AdR p X) := by
  have hu : IsUnit (sR p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sR D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdR
  have hc : ((t : ℂ) • ((sR p)⁻¹ * X * sR p)) = (sR p)⁻¹ * ((t : ℂ) • X) * sR p := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sR D hp)]

lemma sgs_curveL (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X g : Mat k r) (t : ℝ) :
    sgs p (NormedSpace.exp (-((t : ℂ) • X)) * g) = NormedSpace.exp (-((t : ℂ) • AdL p X)) * sgs p g := by
  have hu : IsUnit (sL p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sL D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdL
  have hc : -((t : ℂ) • ((sL p)⁻¹ * X * sL p)) = (sL p)⁻¹ * (-((t : ℂ) • X)) * sL p := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sL D hp)]

lemma rdV_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : RdV X (rho D p φ) g = rho D p (RdV (AdR p X) φ) g := by
  unfold RdV
  simp only [rho_eq, sgs_curveR D hp]
  exact deriv_comp_of_leftInv _ _ (sandw_leftInv D hp) _ 0

lemma ldV_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : LdV X (rho D p φ) g = rho D p (LdV (AdL p X) φ) g := by
  unfold LdV
  simp only [rho_eq, sgs_curveL D hp]
  exact deriv_comp_of_leftInv _ _ (sandw_leftInv D hp) _ 0

lemma rw_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    ∀ (v : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)), Rw v (rho D p φ) = rho D p (Rw (v.map (AdR p)) φ)
  | [], _ => rfl
  | X :: v, φ => by
    funext g
    show RdV X (Rw v (rho D p φ)) g = rho D p (RdV (AdR p X) (Rw (v.map (AdR p)) φ)) g
    rw [rw_rho D hp v φ, rdV_rho D hp]

lemma lw_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    ∀ (u : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)),
      u.foldr LdV (rho D p φ) = rho D p ((u.map (AdL p)).foldr LdV φ)
  | [], _ => rfl
  | X :: u, φ => by
    funext g
    show LdV X (u.foldr LdV (rho D p φ)) g = rho D p (LdV (AdL p X) ((u.map (AdL p)).foldr LdV φ)) g
    rw [lw_rho D hp u φ, ldV_rho D hp]

theorem dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (u v : List (Mat k r))
    (f : Mat k r → (Wq →L[ℂ] Wp)) : dLR u v (rho D p f) = rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) f) := by
  show u.foldr LdV (Rw v (rho D p f)) = rho D p ((u.map (AdL p)).foldr LdV (Rw (v.map (AdR p)) f))
  rw [rw_rho D hp v f, lw_rho D hp u]

theorem _root_.Formalism.FourierDecayAlt.P.rewrite_rho_action : RwRho := by
  intro k r Wp Wq _ _ _ _ D m f p hp _ u v _ _ _ g _
  exact congrFun (dLR_rho D hp u v f) g

end Formalism.FourierDecayAlt.P.SandwichRhoAction
end
end
