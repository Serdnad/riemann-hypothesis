module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051

@[expose] public section

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace HermitianXiVector

open C2x5 FlagSpanVanishing

variable {k r : ℕ}

lemma herm_add_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b w : Fin n → ℂ) :
    herm H (a + b) w = herm H a w + herm H b w := by
  simp only [herm, mulVec_add, dotProduct_add]

lemma herm_smul_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (a w : Fin n → ℂ) :
    herm H (s • a) w = s * herm H a w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma herm_add_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v a b : Fin n → ℂ) :
    herm H v (a + b) = herm H v a + herm H v b := by
  simp only [herm, star_add, add_dotProduct]

lemma herm_smul_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (v a : Fin n → ℂ) :
    herm H v (s • a) = conj s * herm H v a := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
  try rfl

lemma herm_neg_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a w : Fin n → ℂ) :
    herm H (-a) w = -herm H a w := by
  simp only [herm, mulVec_neg, dotProduct_neg]

lemma herm_X_left (v u : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0)
    (hu : ∀ i : Fin (2 * r + k + 1), r + k < i.val → u i = 0) : herm (Hpk k r) v u = 0 := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : r + k < i.val
  · rw [hu i hi, star_zero, zero_mul]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    by_cases hj : r ≤ j.val
    · rw [hv j hj, mul_zero]
    · rw [show Hpk k r i j = 0 by
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega), zero_mul]

lemma herm_X_right (v u : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0)
    (hu : ∀ i : Fin (2 * r + k + 1), r + k < i.val → u i = 0) : herm (Hpk k r) u v = 0 := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : r ≤ i.val
  · rw [hv i hi, star_zero, zero_mul]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    by_cases hj : r + k < j.val
    · rw [hu j hj, mul_zero]
    · rw [show Hpk k r i j = 0 by
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega), zero_mul]

lemma xiV_X (ξ : Fin r → ℂ) : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → C2.xiV k r ξ i = 0 := by
  intro i hi
  unfold C2.xiV
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

lemma xiV_apply_last_block_zero (ξ : Fin r → ℂ) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → C2.xiV k r ξ i = 0 := by
  intro i hi
  unfold C2.xiV
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

lemma vmv_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (a b y : Fin n → ℂ) :
    vecMulVec a (star (H *ᵥ b)) *ᵥ y = herm H y b • a := by
  have hH' : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    rwa [conjTranspose_apply] at this
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, herm, Pi.star_apply, star_sum, star_mul', hH', Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

private lemma hpk_conjTranspose_self (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | (simp; done) | (exfalso; omega)

lemma nEich_apply (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    C2.nEich k r z ξ *ᵥ y = y + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • (-(herm (Hpk k r) y z) • C2.xiV k r ξ +
      herm (Hpk k r) y (C2.xiV k r ξ) • z + ((1 / 2 : ℂ) * herm (Hpk k r) y (C2.xiV k r ξ)) • C2.xiV k r ξ) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := hpk_conjTranspose_self k r
  first
  | simp only [C2.nEich, add_mulVec, one_mulVec, smul_mulVec, neg_mulVec, vmv_apply _ hH, neg_smul, smul_smul]
  | simp only [C2.nEich, add_mulVec, one_mulVec, Matrix.smul_mulVec_assoc, neg_mulVec, vmv_apply _ hH, neg_smul, smul_smul]

end HermitianXiVector

namespace HermitianXiVector

open C2x5 FlagSpanVanishing

variable {k r : ℕ}

lemma herm_neg_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v a : Fin n → ℂ) :
    herm H v (-a) = -herm H v a := by
  simp only [herm, star_neg, neg_dotProduct]

lemma herm_basis {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    herm H (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single i 1) = (Aᴴ * H * A) i j := by
  have e1 : herm H (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single i 1) =
      herm (Aᴴ * H * A) (Pi.single j 1) (Pi.single i 1) := by
    simp only [herm, star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]
  rw [e1]
  simp [herm, dotProduct, mulVec, Pi.single_apply]

lemma uh_of_herm {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ y y', herm H (A *ᵥ y) (A *ᵥ y') = herm H y y') : A ∈ UH H := by
  show Aᴴ * H * A = H
  ext i j
  have h1 := h (Pi.single j 1) (Pi.single i 1)
  rw [herm_basis] at h1
  rw [h1]
  simp [herm, dotProduct, mulVec, Pi.single_apply]

lemma nEich_herm {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) (y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (C2.nEich k r z ξ *ᵥ y) (C2.nEich k r z ξ *ᵥ y') = herm (Hpk k r) y y' := by
  have hH := GBasic.Hpk_herm k r
  have hxx : herm (Hpk k r) (C2.xiV k r ξ) (C2.xiV k r ξ) = 0 :=
    herm_X_left _ _ (xiV_X ξ) (xiV_apply_last_block_zero ξ)
  have hxz : herm (Hpk k r) (C2.xiV k r ξ) z = 0 :=
    herm_X_left _ z (xiV_X ξ) (fun i hi => hz.1 i (Or.inr hi))
  have hzx : herm (Hpk k r) z (C2.xiV k r ξ) = 0 :=
    herm_X_right _ z (xiV_X ξ) (fun i hi => hz.1 i (Or.inr hi))
  have hzz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by rw [hzz_real]; push_cast; ring
  have hxy : herm (Hpk k r) (C2.xiV k r ξ) y' = conj (herm (Hpk k r) y' (C2.xiV k r ξ)) := ggHerm_swap _ hH _ _
  have hzy : herm (Hpk k r) z y' = conj (herm (Hpk k r) y' z) := ggHerm_swap _ hH _ _
  have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz.2.ne'
  have hcc : conj ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := by
    rw [map_div₀, map_one, Complex.conj_ofReal]
  rw [nEich_apply, nEich_apply]
  simp only [herm_add_l, herm_add_r, herm_smul_l, herm_smul_r, herm_neg_l, herm_neg_r, hxx, hxz, hzx, hzz,
    hxy, hzy, hcc, map_neg, map_mul, map_div₀, map_one, map_ofNat]
  set c : ℂ := (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) with hc
  have hcT : c * ((Tz k r z : ℝ) : ℂ) = 1 := by rw [hc]; field_simp
  linear_combination (-(c * herm (Hpk k r) y (C2.xiV k r ξ) * conj (herm (Hpk k r) y' (C2.xiV k r ξ)))) * hcT

lemma nEich_col {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) :
    WeylGroupFacts.col k r (C2.nEich k r z ξ) := by
  intro i j hj hij
  have e : (C2.nEich k r z ξ *ᵥ bvec j) i = C2.nEich k r z ξ i j := by rw [mulVec_bvec]
  rw [← e, nEich_apply]
  have hjx : herm (Hpk k r) (bvec j) (C2.xiV k r ξ) = 0 :=
    herm_X_right (C2.xiV k r ξ) (bvec j) (xiV_X ξ) (fun p hp => by
      simp only [bvec, Pi.single_apply]; rw [if_neg (fun e => by rw [e] at hp; omega)])
  rw [hjx]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, Pi.neg_apply, zero_mul, mul_zero,
    add_zero]
  by_cases hir : r ≤ i.val
  · rw [xiV_X ξ i hir]; simp
  · have hjr : j.val < r := by omega
    have hjz : herm (Hpk k r) (Pi.single j 1) z = 0 :=
      herm_X_left (Pi.single j 1) z (fun p hp => by
        simp only [Pi.single_apply]; rw [if_neg (fun e => by rw [e] at hp; omega)])
        (fun p hp => hz.1 p (Or.inr hp))
    rw [hjz]; simp

lemma nEich_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) :
    C2.nEich k r z ξ ∈ Nset k r := by
  rw [WeylGroupFacts.nset_iff]
  exact ⟨uh_of_herm _ _ (nEich_herm hz ξ), nEich_col hz ξ⟩

end HermitianXiVector

end Formalism.FourierDecayAlt.P
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

private theorem lintegral_comp_eq_of_map_eq {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure α} {f : α → α}
    (hμ : μ.map f = μ) {G : α → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (f x) ∂μ = ∫⁻ x, G x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · conv_rhs => rw [← hμ]
    rw [lintegral_map' hG.aemeasurable hf]
  · by_cases h0 : μ = 0
    · simp [h0]
    · haveI : Nonempty α := Measure.nonempty_of_not_aemeasurable hf
      have hd : μ = Measure.dirac (Classical.ofNonempty : α) :=
        hμ.symm.trans (Measure.map_of_not_aemeasurable_of_ne_zero hf h0)
      rw [hd] at hf
      exact (hf aemeasurable_dirac).elim

theorem lint_lmul {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.lmulM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.lmulM a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem param_left {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    [SigmaFinite μW] [SigmaFinite μN] (hz : Formalism.QuantumDeterminants.inWb k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r)
    {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) =
      ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := by
  have hm1 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm2 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm3 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (h0 * Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1

  have step1 : (fun x => ∫⁻ y, F (fun i j => (h0 * n0 * (Matrix.of x * Matrix.of y)) i j) ∂μN) =ᵐ[μW]
      fun x => ∫⁻ y, F (fun i j => (h0 * Matrix.of x * Matrix.of y) i j) ∂μN := by
    filter_upwards [hae] with x hx
    obtain ⟨hxi, hx1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hx
    have hm : (Matrix.of x)⁻¹ * n0 * Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r := by
      have h1 := (Formalism.QuantumDeterminants.uWNormal k r z hz _ hxi n0 hn0).1
      rwa [Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse hx1)] at h1
    have hG : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (h0 * Matrix.of x * Matrix.of w) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * Matrix.of x * Matrix.of w) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have e1 : ∀ y : Formalism.QuantumDeterminants.Mt k r, h0 * n0 * (Matrix.of x * Matrix.of y) =
        h0 * Matrix.of x * Matrix.of (Formalism.QuantumDeterminants.lmulM ((Matrix.of x)⁻¹ * n0 * Matrix.of x) y) := by
      intro y
      show _ = h0 * Matrix.of x * ((Matrix.of x)⁻¹ * n0 * Matrix.of x * Matrix.of y)
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Matrix.of x) (Matrix.of x)⁻¹, hx1, Matrix.one_mul]
    simp_rw [e1]
    exact lint_lmul (hN.2.2.2 _ hm) hG
  rw [MeasureTheory.lintegral_prod _ hm1.aemeasurable, MeasureTheory.lintegral_prod _ hm2.aemeasurable,
    MeasureTheory.lintegral_congr_ae step1,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (h0 * Matrix.of x * Matrix.of y) i j))
      hm3.aemeasurable,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * Matrix.of y) i j))
      hm2.aemeasurable]

  refine MeasureTheory.lintegral_congr fun y => ?_
  have hG : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r => F (fun i j => (Matrix.of w * Matrix.of y) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of w * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have e2 : ∀ x : Formalism.QuantumDeterminants.Mt k r, h0 * Matrix.of x * Matrix.of y =
      Matrix.of (Formalism.QuantumDeterminants.lmulM h0 x) * Matrix.of y := fun x => rfl
  simp_rw [e2]
  exact lint_lmul (hW.2.2.2 h0 hh0) hG

theorem lint_rmul {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (B.rmulF a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (B.rmulF a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem lint_conj {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.conjM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.conjM a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem param_right {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    [SigmaFinite μW] [SigmaFinite μN] (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r)
    {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j) ∂(μW.prod μN) =
      ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := by
  obtain ⟨hi, h1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hh0
  have hinv : h0⁻¹⁻¹ = h0 := Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse h1)
  have hconj : μN.map (Formalism.QuantumDeterminants.conjM h0⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN _ hi
  have hm1 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm2 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm3 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * h0 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * h0 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)

  have inner : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ∫⁻ y, F (fun i j => (Matrix.of x * Matrix.of y * (h0 * n0)) i j) ∂μN =
        ∫⁻ y, F (fun i j => (Matrix.of x * h0 * Matrix.of y) i j) ∂μN := by
    intro x
    have hG1 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (Matrix.of x * h0 * Matrix.of w * n0) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of x * h0 * Matrix.of w * n0) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have hG2 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (Matrix.of x * h0 * Matrix.of w) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of x * h0 * Matrix.of w) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have e1 : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * Matrix.of y * (h0 * n0) =
        Matrix.of x * h0 * Matrix.of (Formalism.QuantumDeterminants.conjM h0⁻¹ y) * n0 := by
      intro y
      show _ = Matrix.of x * h0 * (h0⁻¹ * Matrix.of y * h0⁻¹⁻¹) * n0
      rw [hinv]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc h0 h0⁻¹, h1, Matrix.one_mul]
    have e2 : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * h0 * Matrix.of y * n0 =
        Matrix.of x * h0 * Matrix.of (B.rmulF n0 y) := by
      intro y
      show _ = Matrix.of x * h0 * (Matrix.of y * n0)
      simp only [Matrix.mul_assoc]
    simp_rw [e1]
    rw [lint_conj hconj hG1]
    simp_rw [e2]
    exact lint_rmul (hN.right n0 hn0) hG2
  rw [MeasureTheory.lintegral_prod _ hm1.aemeasurable, MeasureTheory.lintegral_prod _ hm2.aemeasurable]
  simp_rw [inner]
  rw [MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * h0 * Matrix.of y) i j))
      hm3.aemeasurable,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * Matrix.of y) i j))
      hm2.aemeasurable]

  refine MeasureTheory.lintegral_congr fun y => ?_
  have hG3 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r => F (fun i j => (Matrix.of w * Matrix.of y) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of w * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have e3 : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * h0 * Matrix.of y =
      Matrix.of (B.rmulF h0 x) * Matrix.of y := fun x => rfl
  simp_rw [e3]
  exact lint_rmul (hW.right h0 hh0) hG3

end Formalism.FourierDecayAlt.P.S3dx4
end
end

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x7

theorem fixed_frame_property : C2.FixFrame := by
  intro k r z hz
  ext g
  constructor
  · rintro ⟨hgV, hfix⟩
    have hS : g ∈ Sset k r z := by
      rw [← standard_flag_property k r z hz]
      exact ⟨hgV, fun a => by simp [hfix a]⟩
    refine ⟨hS, uMap_eq hz g 1 fun b => ?_⟩
    simp [Matrix.one_apply, hfix b]
  · rintro ⟨hS, hU⟩
    have hS' := hS
    rw [← standard_flag_property k r z hz] at hS'
    refine ⟨hS'.1, fun a => ?_⟩
    rw [((unipotent_map_frame k r z hz).1 g hS).1 a, hU]
    simp [Matrix.one_apply]

end Formalism.FourierDecayAlt.P
end

section

theorem Formalism.FourierDecayAlt.P.xi_Y_zhat_identity : Formalism.FourierDecayAlt.C3.XiYZhat :=
  covector_entries
end
