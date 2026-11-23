module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFockLSqLe
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.FockJet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TaylorCoefficientForms

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransport

variable {D : D7}

def sg (b : Bool) : ℝ := if b then 1 else -1

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

def cf (b b' : Bool) (c : ℂ) : ℂ := (c.re : ℂ) + ((sg b * sg b' * c.im : ℝ) : ℂ) * Complex.I

theorem cf_cf (b b' : Bool) (c : ℂ) : cf b b' (cf b b' c) = c := by
  have h : sg b * sg b' * (sg b * sg b') = 1 := by
    rw [mul_mul_mul_comm, sg_mul_self, sg_mul_self, one_mul]
  apply Complex.ext <;> simp [cf, h, ← mul_assoc]

theorem continuous_cf (b b' : Bool) : Continuous (cf b b') := by
  unfold cf; fun_prop

theorem jm_mul_single_mul_jm {m n : ℕ} (εB : Fin m → Bool) (εA : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm εB * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm εA =
      Matrix.single i j (((sg (εB i) * sg (εA j) : ℝ)) : ℂ) := by
  ext a b
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, sg]
  by_cases ha : i = a <;> by_cases hb : j = b <;> subst_vars <;> simp_all <;> split_ifs <;> simp

variable {S T : HSp D}

theorem det_fr_unit {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) : IsUnit (A.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)

theorem unitMap_fr (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    unitMap (A.onb τ) (B.onb τ) i j = (B.fr τ)⁻¹ * Matrix.single i j (1 : ℂ) * A.fr τ := by
  simp only [unitMap, GlobalTheory.ChainFr.Fr.onb, Matrix.nonsing_inv_nonsing_inv _ (det_fr_unit A τ)]

theorem cplxO_unitMap_fr (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (i : Fin T.rank)
    (j : Fin S.rank) :
    cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j) =
      (B.fr τ)⁻¹ * Matrix.single i j ((((sg (B.ε τ i) * sg (A.ε τ j) : ℝ)) : ℂ) * Complex.I) * A.fr τ := by
  rw [unitMap_fr]
  have e : B.cart τ * ((B.fr τ)⁻¹ * Matrix.single i j (1 : ℂ) * A.fr τ) * A.cart τ =
      (B.fr τ)⁻¹ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
    simp only [GlobalTheory.ChainFr.Fr.cart, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit B τ),
      Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit A τ)]
  rw [cplxO, e, jm_mul_single_mul_jm, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_comm]

theorem fockMat_eq (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (z : Fin T.rank → Fin S.rank → ℂ) :
    fockMat A B τ z = (B.fr τ)⁻¹ * Matrix.of (fun i j => cf (B.ε τ i) (A.ε τ j) (z i j)) * A.fr τ := by
  have ht : ∀ i j, (((z i j).re : ℂ) • unitMap (A.onb τ) (B.onb τ) i j +
      ((z i j).im : ℂ) • cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j)) =
      (B.fr τ)⁻¹ * Matrix.single i j (cf (B.ε τ i) (A.ε τ j) (z i j)) * A.fr τ := by
    intro i j
    rw [cplxO_unitMap_fr, unitMap_fr, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul,
      ← Matrix.add_mul, ← Matrix.mul_add, Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 3
    simp only [cf, smul_eq_mul, mul_one, Complex.ofReal_mul]
    ring
  rw [fockMat]
  simp only [ht]
  simp only [← Matrix.sum_mul, ← Matrix.mul_sum]
  congr 2
  conv_rhs => rw [Matrix.matrix_eq_sum_single (Matrix.of _)]
  simp only [Matrix.of_apply]

def fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X : Matrix (Fin T.rank) (Fin S.rank) ℂ) : Fin T.rank → Fin S.rank → ℂ :=
  fun i j => cf (B.ε τ i) (A.ε τ j) ((B.fr τ * X * (A.fr τ)⁻¹) i j)

theorem fockInvMat_fockMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (z : Fin T.rank → Fin S.rank → ℂ) : fockInvMat A B τ (fockMat A B τ z) = z := by
  funext i j
  rw [fockInvMat, fockMat_eq]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit B τ),
    Matrix.mul_nonsing_inv _ (det_fr_unit A τ), Matrix.mul_one, Matrix.of_apply, cf_cf]

theorem fockMat_fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X : Matrix (Fin T.rank) (Fin S.rank) ℂ) : fockMat A B τ (fockInvMat A B τ X) = X := by
  rw [fockMat_eq]
  have e : (Matrix.of fun i j => cf (B.ε τ i) (A.ε τ j) (fockInvMat A B τ X i j)) = B.fr τ * X * (A.fr τ)⁻¹ := by
    ext i j; simp only [Matrix.of_apply, fockInvMat, cf_cf]
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_fr_unit A τ), Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ (det_fr_unit B τ)]

theorem continuous_fockMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) :
    Continuous (fockMat A B τ) := by
  unfold fockMat; fun_prop

theorem continuous_fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) :
    Continuous (fockInvMat A B τ) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_cf _ _).comp
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)

def fockInv (θ : InfFam D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (w : WO S T) :
    VCx D.what₂.Tau S.rank T.rank :=
  fun τ => fockInvMat A B τ (GlobalTheory.FockCompare.piW θ T S w τ)

theorem fockInv_fockPt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    fockInv θ A B (fockPt σ A B z) = z := by
  funext τ
  have e : GlobalTheory.FockCompare.piW θ T S (fockPt σ A B z) τ = fockMat A B τ (z τ) := congrFun (h.pi_iota T S _) τ
  show fockInvMat A B τ (GlobalTheory.FockCompare.piW θ T S (fockPt σ A B z) τ) = z τ
  rw [e, fockInvMat_fockMat]

theorem fockPt_fockInv {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) {w : WO S T} (hw : w.map (finPart D) = 0) :
    fockPt σ A B (fockInv θ A B w) = w := by
  have e : (fun τ => fockMat A B τ (fockInv θ A B w τ)) = GlobalTheory.FockCompare.piW θ T S w :=
    funext fun τ => fockMat_fockInvMat A B τ _
  rw [fockPt, e]
  exact h.iota_pi hw

theorem fockPt_transport : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ →
    ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), Continuous (fockPt σ A B) ∧
      (∀ w : WO S T, w.map (finPart D) = 0 → ∃ z, fockPt σ A B z = w) ∧
      ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g → ∃ (m : Measure (WO S T)) (α : WO S T → ℂ),
        SFinite m ∧ Integrable α m ∧ ∀ H : WO S T → ℂ, ∫ w, α w * H w ∂m = ∫ z, g z * H (fockPt σ A B z) := by
  intro D θ σ h S T A B
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : T2Space (WO S T) := (GlobalTheory.MixModel.lattice_Mx D T.rank S.rank).2.2.2.1
  have hc : Continuous (fockPt σ A B) :=
    (h.continuous_iota T S).comp (continuous_pi fun τ => (continuous_fockMat A B τ).comp (continuous_apply τ))
  have hic : Continuous (fockInv θ A B) := continuous_pi fun τ =>
    (continuous_fockInvMat A B τ).comp ((continuous_apply τ).comp (GlobalTheory.FockCompare.continuous_pi' h.inf T S))
  have hl : Function.LeftInverse (fockInv θ A B) (fockPt σ A B) := fun z => fockInv_fockPt h A B z
  have hr : Set.range (fockPt σ A B) = {w | fockPt σ A B (fockInv θ A B w) = w} := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg (fockPt σ A B) (hl z)
    · intro hw
      exact ⟨_, hw⟩
  have hme : MeasurableEmbedding (fockPt σ A B) :=
    MeasurableEmbedding.of_measurable_inverse hc.measurable
      (by rw [hr]; exact (isClosed_eq (hc.comp hic) continuous_id).measurableSet) hic.measurable hl
  refine ⟨hc, fun w hw => ⟨_, fockPt_fockInv h A B hw⟩, fun g hg => ?_⟩
  haveI : SigmaFinite (volume : Measure (Fin S.rank → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin T.rank → Fin S.rank → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (VCx D.what₂.Tau S.rank T.rank)) := inferInstance
  refine ⟨Measure.map (fockPt σ A B) volume, g ∘ fockInv θ A B, MeasureTheory.Measure.instSFiniteMap _ _, ?_, fun H => ?_⟩
  · rw [hme.integrable_map_iff]
    have e : (g ∘ fockInv θ A B) ∘ fockPt σ A B = g := funext fun z => congrArg g (hl z)
    rw [e]; exact hg
  · rw [hme.integral_map]
    simp only [Function.comp_apply, hl _]

end GlobalTheory.FockTransport
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

def fmR {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    GlobalTheory.FockCompare.RW T S :=
  fun τ => fockMat A B τ (z τ)

def omF {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) : ℝ :=
  GlobalTheory.OrientedHeis.omO S T (fmR A B z) (fmR A B e)

def gD {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z e : VCx ι a b) : ℝ :=
  2 * ∑ τ, ∑ i, ∑ j, c τ * (z τ i j * conj (e τ i j)).re

def lamF {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  (1 / 2 : ℂ) * (-((Real.pi : ℂ) * I) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ)
    - (Real.pi : ℂ) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ)
    - (1 / 2 : ℂ) * (gD (fw D) z (Formalism.L2.Ker.coordX l) : ℂ)
    + (I / 2) * (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ))

def crOp {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (Φ : VCx D.what₂.Tau S.rank T.rank → ℂ) (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  lamF A B l z * Φ z + (1 / 2 : ℂ) *
    (fderiv ℝ Φ z (Formalism.L2.Ker.coordX l) - I * fderiv ℝ Φ z (I • Formalism.L2.Ker.coordX l))

end GlobalTheory.FockTransl.Jet

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

theorem integrable_vcx_prod {ι : Type} [Fintype ι] {a b : ℕ} (g : ι → Fin b → Fin a → ℂ → ℂ)
    (hg : ∀ τ i j, Integrable (g τ i j)) :
    Integrable fun z : VCx ι a b => ∏ τ, ∏ i, ∏ j, g τ i j (z τ i j) := by
  have h1 : ∀ τ i, Integrable (fun w : Fin a → ℂ => ∏ j, g τ i j (w j)) := fun τ i =>
    Integrable.fintype_prod (f := fun j (w : ℂ) => g τ i j w) (hg τ i)
  have h2 : ∀ τ, Integrable (fun w : Fin b → Fin a → ℂ => ∏ i, ∏ j, g τ i j (w i j)) := fun τ =>
    Integrable.fintype_prod (f := fun i (w : Fin a → ℂ) => ∏ j, g τ i j (w j)) (h1 τ)
  exact Integrable.fintype_prod (f := fun τ (w : Fin b → Fin a → ℂ) => ∏ i, ∏ j, g τ i j (w i j)) h2

theorem exp_gq_eq_prod {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z : VCx ι a b) :
    (Real.exp (-gq c z / 2) : ℂ) = ∏ τ, ∏ i, ∏ j, (Real.exp (-(c τ * ‖z τ i j‖ ^ 2) / 2) : ℂ) := by
  have h : -gq c z / 2 = ∑ τ, ∑ i, ∑ j, (-(c τ * ‖z τ i j‖ ^ 2) / 2) := by
    simp [gq, Finset.sum_div, Finset.sum_neg_distrib, neg_div]
  rw [h]
  simp only [Real.exp_sum]
  push_cast
  rfl

theorem integrable_conj_pow_mul_gauss (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable fun w : ℂ => conj w ^ n * (Real.exp (-(c * ‖w‖ ^ 2) / 2) : ℂ) := by
  have h := GlobalTheory.integrable_norm_pow_mul_exp_neg_mul_norm_sq (E := ℂ) n (b := c / 2) (by positivity)
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
  rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply le_of_eq
  congr 2
  ring

theorem integrable_exp_bargmann_mul_gauss (u : ℂ) {c : ℝ} (hc : 0 < c) :
    Integrable fun w : ℂ => Complex.exp ((c : ℂ) * u * conj w) * (Real.exp (-(c * ‖w‖ ^ 2) / 2) : ℂ) := by
  have h := (GlobalTheory.integrable_exp_neg_mul_norm_sq (E := ℂ) (b := c / 4) (by positivity)).const_mul
    (Real.exp (c * ‖u‖ ^ 2))
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : ((c : ℂ) * u * conj w).re ≤ c * (‖u‖ * ‖w‖) := by
    calc _ ≤ ‖(c : ℂ) * u * conj w‖ := Complex.re_le_norm _
      _ = c * (‖u‖ * ‖w‖) := by
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hc.le]
        ring
  have h2 : ‖u‖ * ‖w‖ ≤ ‖u‖ ^ 2 + ‖w‖ ^ 2 / 4 := by nlinarith [sq_nonneg (‖u‖ - ‖w‖ / 2)]
  have h3 := mul_le_mul_of_nonneg_left h2 hc.le
  nlinarith

theorem integrable_conjMono_bargmann_gauss : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) →
    (∀ m : DVar ι a b →₀ ℕ, Integrable fun z => conjMono m z * (Real.exp (-gq c z / 2) : ℂ)) ∧
      ∀ z₀ : VCx ι a b, Integrable fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) := by
  intro ι _ a b c hc
  constructor
  · intro m
    have h := integrable_vcx_prod (fun τ i j w => conj w ^ m (τ, i, j) * (Real.exp (-(c τ * ‖w‖ ^ 2) / 2) : ℂ))
      (fun τ i j => integrable_conj_pow_mul_gauss _ (hc τ))
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [conjMono, exp_gq_eq_prod, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Fintype.prod_prod_type, Finset.prod_mul_distrib]
  · intro z₀
    have h := integrable_vcx_prod (fun τ i j w => Complex.exp ((c τ : ℂ) * z₀ τ i j * conj w) *
      (Real.exp (-(c τ * ‖w‖ ^ 2) / 2) : ℂ)) (fun τ i j => integrable_exp_bargmann_mul_gauss _ (hc τ))
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [bk, exp_gq_eq_prod]
    simp only [Complex.exp_sum, Finset.prod_mul_distrib]

end GlobalTheory.FockTransl

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockMoment

variable {ι : Type} [Fintype ι] {a b : ℕ}

def unitPt (r : ι → ℝ) (u : DVar ι a b → ℂ) : VCx ι a b := fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α)

def scalePt (r : ι → ℝ) (z : VCx ι a b) : DVar ι a b → ℂ := fun x => (r x.1 : ℂ) * z x.1 x.2.1 x.2.2

def scaleEquiv (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) : VCx ι a b ≃ᵐ (DVar ι a b → ℂ) where
  toFun := scalePt r
  invFun := unitPt r
  left_inv z := by
    funext τ β α
    have : (r τ : ℂ) ≠ 0 := by exact_mod_cast (hr τ).ne'
    simp [unitPt, scalePt, this]
  right_inv u := by
    funext x
    have : (r x.1 : ℂ) ≠ 0 := by exact_mod_cast (hr x.1).ne'
    simp [unitPt, scalePt, this]
  measurable_toFun := (show Continuous (scalePt (a := a) (b := b) r) by unfold scalePt; fun_prop).measurable
  measurable_invFun := (show Continuous (unitPt (a := a) (b := b) r) by unfold unitPt; fun_prop).measurable

theorem scaleEquiv_apply (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (z : VCx ι a b) :
    scaleEquiv r hr z = scalePt r z := rfl

theorem unitPt_scalePt (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (z : VCx ι a b) :
    unitPt r (scalePt r z) = z := (scaleEquiv r hr).symm_apply_apply z

theorem volume_eq_smul_map (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) :
    (volume : Measure (DVar ι a b → ℂ)) =
      ENNReal.ofReal (∏ x : DVar ι a b, r x.1 ^ 2) • (volume : Measure (VCx ι a b)).map (scaleEquiv r hr) := by
  rw [volume_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.map_apply (scaleEquiv r hr).measurable (MeasurableSet.univ_pi hs), smul_eq_mul]
  have e : (scaleEquiv r hr) ⁻¹' Set.univ.pi s = Set.univ.pi fun τ => Set.univ.pi fun β => Set.univ.pi fun α =>
      (fun w : ℂ => r τ • w) ⁻¹' s (τ, β, α) := by
    ext z
    simp [scaleEquiv_apply, scalePt, Set.mem_univ_pi, Prod.forall, Complex.real_smul]
  rw [e, volume_pi, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [ENNReal.ofReal_prod_of_nonneg (fun x _ => sq_nonneg _)]
  simp_rw [Fintype.prod_prod_type]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun α _ => ?_
  rw [Measure.addHaar_preimage_smul _ (hr τ).ne', Complex.finrank_real_complex, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg _), abs_of_pos (by have := hr τ; positivity), mul_inv_cancel₀ (by have := hr τ; positivity),
    ENNReal.ofReal_one, one_mul]

theorem integral_unitPt (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (h : VCx ι a b → ℂ) :
    ∫ u : DVar ι a b → ℂ, h (unitPt r u) = ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) * ∫ z, h z := by
  rw [volume_eq_smul_map r hr, integral_smul_measure, integral_map_equiv]
  have hP : 0 ≤ ∏ x : DVar ι a b, r x.1 ^ 2 := Finset.prod_nonneg fun _ _ => sq_nonneg _
  rw [ENNReal.toReal_ofReal hP, Complex.real_smul]
  simp only [scaleEquiv_apply, unitPt_scalePt r hr]

end GlobalTheory.FockMoment

namespace GlobalTheory.FockMoment

open Formalism.DimensionVariation (nsq mono cj mfact)

theorem gaussMoment : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z) : ℂ) * G z = ((∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) : ℂ) * ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) * derivAt0 G m := by
  intro ι _ a b c hc G hG ⟨M, hM⟩ m
  classical
  set r : ι → ℝ := fun τ => Real.sqrt (c τ) with hr_def
  have hr : ∀ τ, 0 < r τ := fun τ => Real.sqrt_pos.2 (hc τ)
  have hr2 : ∀ τ, r τ ^ 2 = c τ := fun τ => Real.sq_sqrt (hc τ).le
  have hrC : ∀ τ, (r τ : ℂ) ≠ 0 := fun τ => by exact_mod_cast (hr τ).ne'
  set F : (DVar ι a b → ℂ) → ℂ := fun u => G fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α) with hF_def
  have hFd : Differentiable ℂ F := hG.comp (by fun_prop)
  have hgq : ∀ u : DVar ι a b → ℂ, gq c (unitPt r u) = nsq u := by
    intro u
    simp only [gq, unitPt, nsq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, hr2, ← mul_assoc,
      mul_inv_cancel₀ (hc τ).ne', one_mul]
  have hmono : ∀ u : DVar ι a b → ℂ, conjMono m (unitPt r u) =
      (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * mono (Formalism.DimensionVariation.cj u) m := by
    intro u
    rw [conjMono, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [unitPt, Formalism.DimensionVariation.cj, mul_pow, Complex.conj_ofReal]
  have hgrow : ∀ u : DVar ι a b → ℂ, ‖F u‖ ≤ M * Real.exp (nsq u / 2) := fun u => by
    rw [← hgq u]; exact hM _
  have hfj := (Formalism.DimensionVariation.gaussianCoeffIntegral (DVar ι a b) F (GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F) M hFd.continuous
    (GlobalTheory.JetFrameCompare.hasSum_taylorCoeff hFd) hgrow m).2
  have htj := GlobalTheory.JetBlock.taylor_jetC hG r hr (fun _ => 1) m
  simp only [Formalism.L2.Ker.jetC, one_pow, one_mul] at htj
  rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Finset.prod_const_one, one_mul] at htj
  have hcov := integral_unitPt r hr (fun z => conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)
  have hint : ∫ u : DVar ι a b → ℂ, conjMono m (unitPt r u) * (Real.exp (-gq c (unitPt r u)) : ℂ) * G (unitPt r u) =
      (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * ∫ u, F u * mono (Formalism.DimensionVariation.cj u) m * (Real.exp (-(nsq u)) : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    funext u
    have hFu : F u = G (unitPt r u) := rfl
    rw [hmono, hgq, hFu]
    ring
  rw [hint, hfj] at hcov
  have htj' : GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) * ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x = derivAt0 G m := htj
  have hPpos : 0 < ∏ x : DVar ι a b, r x.1 ^ 2 := Finset.prod_pos fun x _ => by have := hr x.1; positivity
  have hP : (∏ x : DVar ι a b, r x.1 ^ 2) = ∏ x : DVar ι a b, c x.1 := Finset.prod_congr rfl fun x _ => hr2 x.1
  have hpi : (∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) =
      Real.pi ^ Fintype.card (DVar ι a b) * (∏ x : DVar ι a b, r x.1 ^ 2)⁻¹ := by
    rw [hP]
    simp only [Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod]
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, div_eq_mul_inv, mul_comm b a,
      mul_comm (a * b) (Fintype.card ι)]
  have hmp : ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) = (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) ^ 2 := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    push_cast
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← hr2 x.1]
    push_cast
    ring
  have hPC : ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hRR : (∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x) * (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ => by rw [← mul_pow, mul_inv_cancel₀ (hrC x.1), one_pow]
  have hPinv := mul_inv_cancel₀ hPC
  rw [hpi, hmp, ← htj']
  apply mul_left_cancel₀ hPC
  rw [← hcov, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  set P := ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) with hP_def
  set R := ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x with hR_def
  set Ri := ∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x with hRi_def
  set TM := GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) with hTM
  set K := (Real.pi : ℂ) ^ Fintype.card (DVar ι a b) with hK
  linear_combination (-(K * TM * Ri)) * hRR + (-(K * TM * Ri ^ 2 * R)) * hPinv
end FockMoment
end GlobalTheory
end
end
