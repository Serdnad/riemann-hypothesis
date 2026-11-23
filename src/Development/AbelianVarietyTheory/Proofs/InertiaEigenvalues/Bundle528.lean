module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittApproxFrobeniusPerfection
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

noncomputable section
open MvPolynomial

namespace GlobalTheory.FockSubstComm

variable {D : D7} {m n : ℕ}

def rowMat (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  if (i : ℕ) < p τ then ((g τ)⁻¹).val else ((g τ).val)ᵀ

theorem fockSubst_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (v : FVar D m n) :
    fockSubst p g (X v) = ∑ b, C (rowMat p g v.1 v.2.1 v.2.2 b) * X (v.1, v.2.1, b) := by
  rw [fockSubst, aeval_X, rowMat]
  split_ifs <;> simp

open Classical in
theorem pderiv_fockSubst_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (b : Fin n)
    (u : FVar D m n) :
    pderiv (τ, i, b) (fockSubst p g (X u)) = if u.1 = τ ∧ u.2.1 = i then C (rowMat p g τ i u.2.2 b) else 0 := by
  rw [fockSubst_X]

  simp only [map_sum, Derivation.leibniz, pderiv_C, smul_zero, add_zero, pderiv_X, smul_eq_mul]
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [Finset.sum_eq_single b]
    · simp [Pi.single_apply]
    · intro c _ hc; simp [Pi.single_apply, Prod.ext_iff, hc]
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    have : (u.1, u.2.1, c) ≠ (τ, i, b) := by
      intro e; simp [Prod.ext_iff] at e; exact h ⟨e.1, e.2.1⟩
    simp [Pi.single_apply, this]

theorem chain_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n)
    (C' : Matrix (Fin n) (Fin n) ℂ) (hC : rowMat p g τ i * C' = 1) (u : FVar D m n) :
    fockSubst p g (pderiv (τ, i, c) (X u)) = ∑ b, C' b c • pderiv (τ, i, b) (fockSubst p g (X u)) := by
  classical
  simp only [pderiv_fockSubst_X]
  rw [pderiv_X]
  by_cases h : u.1 = τ ∧ u.2.1 = i
  · simp only [if_pos h]
    have e : (∑ b, C' b c • C (rowMat p g τ i u.2.2 b) : PolF D m n) = C ((rowMat p g τ i * C') u.2.2 c) := by

      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_eq_C_mul, ← map_mul, mul_comm]
    rw [e, hC]
    obtain ⟨u1, u2, u3⟩ := u
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1; subst h2
    by_cases h3 : u3 = c
    · subst h3; simp
    · have : ((u1, u2, u3) : FVar D m n) ≠ (u1, u2, c) := by simp [h3]
      simp [Pi.single_apply, this, Matrix.one_apply, h3]
  · simp only [if_neg h, smul_zero, Finset.sum_const_zero]
    have : u ≠ (τ, i, c) := by
      rintro rfl; exact h ⟨rfl, rfl⟩
    simp [Pi.single_apply, this]

theorem chain (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n)
    (C' : Matrix (Fin n) (Fin n) ℂ) (hC : rowMat p g τ i * C' = 1) (P : PolF D m n) :
    fockSubst p g (pderiv (τ, i, c) P) = ∑ b, C' b c • pderiv (τ, i, b) (fockSubst p g P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [pderiv_C]
  | add P Q hP hQ =>
    simp only [map_add (f := _), hP, hQ, smul_add, Finset.sum_add_distrib]
  | mul_X P u ih =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib]
    rw [ih, chain_X p g τ i c C' hC u, Finset.mul_sum, Finset.mul_sum]
    simp only [mul_smul_comm]

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem rai_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n) :
    (fockSubst p g).toLinearMap * raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i c =
      ∑ b, ((g τ)⁻¹).val c b • (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i b *
        (fockSubst p g).toLinearMap) := by
  refine LinearMap.ext fun P => ?_
  by_cases h : (i : ℕ) < p τ
  · simp only [raiO, sgn, h, decide_true, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [fockSubst_X, Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rowMat, h, smul_eq_C_mul, mul_assoc]
  · have hC : rowMat p g τ i * (((g τ)⁻¹).val)ᵀ = 1 := by
      rw [rowMat, if_neg h, ← Matrix.transpose_mul]
      simp
    simp only [raiO, sgn, h, decide_false, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.neg_apply, map_neg, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Derivation.coeFn_coe, Bool.false_eq_true, if_false]
    rw [chain p g τ i c _ hC, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [smul_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem low_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (l : Fin m) (c : Fin n) :
    (fockSubst p g).toLinearMap * lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l c =
      ∑ b, (g τ).val b c • (lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l b *
        (fockSubst p g).toLinearMap) := by
  refine LinearMap.ext fun P => ?_
  by_cases h : (l : ℕ) < p τ
  · have hC : rowMat p g τ l * (g τ).val = 1 := by
      rw [rowMat, if_pos h]
      simp
    simp only [lowO, sgn, h, decide_true, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe]
    rw [chain p g τ l c _ hC]
  · simp only [lowO, sgn, h, decide_false, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Bool.false_eq_true, if_false]
    rw [fockSubst_X, Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rowMat, h, smul_eq_C_mul, mul_assoc]

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem pair_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i l : Fin m) :
    Commute (fockSubst p g).toLinearMap
      (∑ j, raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i j *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l j) := by
  set σ := (fockSubst p g).toLinearMap
  set R := raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i
  set L := lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l
  have hR : ∀ c, σ * R c = ∑ b, ((g τ)⁻¹).val c b • (R b * σ) := rai_comm p g τ i
  have hL : ∀ c, σ * L c = ∑ b, (g τ).val b c • (L b * σ) := low_comm p g τ l
  have hGG : ∀ c b, ∑ j, (g τ).val c j * ((g τ)⁻¹).val j b = (1 : Matrix (Fin n) (Fin n) ℂ) c b := by
    intro c b
    rw [← Matrix.mul_apply]
    simp
  unfold Commute SemiconjBy
  calc σ * ∑ j, R j * L j
      = ∑ j, ∑ b, ∑ c, (((g τ)⁻¹).val j b * (g τ).val c j) • (R b * L c * σ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, hR, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [smul_mul_assoc, mul_assoc, hL, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [mul_smul_comm, smul_smul, ← mul_assoc]
    _ = ∑ b, ∑ c, (∑ j, (g τ).val c j * ((g τ)⁻¹).val j b) • (R b * L c * σ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = (∑ j, R j * L j) * σ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hGG, Matrix.one_apply, ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq']
        simp


open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem fockSubst_fockT (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau)
    (Y : Matrix (Fin m) (Fin m) ℂ) (P : PolF D m n) :
    fockSubst p g (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y P) =
      fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y (fockSubst p g P) := by
  have hc : Commute (fockSubst p g).toLinearMap
      (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y) := by
    unfold fockT
    refine Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun l _ => Commute.smul_right ?_ _
    rw [Finset.sum_add_distrib]
    refine Commute.add_right (pair_comm p g τ i l) (Commute.sum_right _ _ _ fun j _ => ?_)
    split_ifs
    · exact Commute.smul_right (Commute.one_right _) _
    · exact Commute.zero_right _
  have := LinearMap.congr_fun hc.eq P
  simpa only [Module.End.mul_apply, AlgHom.toLinearMap_apply] using this

end GlobalTheory.FockSubstComm
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open scoped ContDiff

namespace GlobalTheory.DiscSMO

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a c N : ℕ} {n : Fin c → ℕ}
  {π π' : ∀ i, CuspSub E (n i)}


def prodForm (φ : ∀ i, (π i).V) : (∀ i, GA E (n i)) → ℂ := fun m => ∏ i, (φ i).1.1 (m i)

structure IsTensorOf (T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V) (Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)) : Prop where
  comm : ∀ i o φ, T i ((π i).op o φ) = (π' i).op o (T i φ)
  prod : ∀ φ, Θ (prodForm φ) = prodForm fun i => T i (φ i)

namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}

end IsTensorOf

variable {h : ∑ i, n i = N}




namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}

end IsTensorOf

theorem mem_Sm_of_one {f : GA E a → ℂ} (hf : ∀ g, ContDiffAt ℝ ∞ (chart f g) (oneL E a)) : f ∈ Sm E a := by
  rintro g x ⟨y, hy⟩
  obtain rfl : x = toL y.val := hy.symm
  have e : chart f g = chart f (g * infGL E a y) ∘ lmul (toL (y⁻¹).val) := by
    rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : lmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.inv_mul
  rw [e]
  refine (ContDiffAt.comp _ ?_ (lmul (toL (y⁻¹).val)).contDiff.contDiffAt).contDiffWithinAt
  rw [e1]
  exact hf _

theorem contDiffAt_chart_mul {f : GA E a → ℂ} {g : GA E a} {y : GL (Fin a) (Cinf E)}
    (hf : ContDiffAt ℝ ∞ (chart (fun x => f (x * infGL E a y)) g) (oneL E a)) :
    ContDiffAt ℝ ∞ (chart f (g * infGL E a y)) (oneL E a) := by
  have e : chart f g = chart (fun x => f (x * infGL E a y)) g ∘ rmul (toL (y⁻¹).val) := by
    rw [← chart_rt_inf]
    simp only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have e1 : rmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.mul_inv
  have e2 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  rw [chart_mul, e]
  refine ContDiffAt.comp _ ?_ (lmul (toL y.val)).contDiff.contDiffAt
  rw [e2]
  refine ContDiffAt.comp _ ?_ (rmul (toL (y⁻¹).val)).contDiff.contDiffAt
  rw [e1]
  exact hf


namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}


end IsTensorOf


end GlobalTheory.DiscSMO

end
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.ColConvGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_toL_mul_le (M P : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (M * P)‖ ≤ (a : ℝ) * ‖toL M‖ * ‖toL P‖ := by
  have hM : ∀ i k, ‖M i k‖ ≤ ‖toL M‖ := fun i k =>
    (norm_le_pi_norm (toL M i) k).trans (norm_le_pi_norm (toL M) i)
  have hP : ∀ i k, ‖P i k‖ ≤ ‖toL P‖ := fun i k =>
    (norm_le_pi_norm (toL P i) k).trans (norm_le_pi_norm (toL P) i)
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i =>
    pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  change ‖(M * P) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ k, M i k * P k j‖ ≤ ∑ k, ‖M i k * P k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin a, ‖toL M‖ * ‖toL P‖ := Finset.sum_le_sum fun k _ =>
        (norm_mul_le _ _).trans (mul_le_mul (hM i k) (hP k j) (norm_nonneg _) (norm_nonneg _))
    _ = (a : ℝ) * ‖toL M‖ * ‖toL P‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

theorem height_mul_le (y u : GL (Fin a) (Cinf E)) :
    height (y * u) ≤ ((a : ℝ) + 1) * height y * height u := by
  have h1 := norm_toL_mul_le y.val u.val
  have h2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
  have e1 : (y * u).val = y.val * u.val := rfl
  have e2 : ((y * u)⁻¹).val = (u⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (toL u.val)
  have n4 := norm_nonneg (toL (u⁻¹).val)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  unfold height
  rw [e1, e2]
  nlinarith [mul_nonneg n1 n3, mul_nonneg n2 n4, mul_nonneg n1 n4, mul_nonneg n2 n3,
    mul_nonneg ha (mul_nonneg n1 n3), mul_nonneg ha (mul_nonneg n2 n4), mul_nonneg ha n1, mul_nonneg ha n2,
    mul_nonneg ha n3, mul_nonneg ha n4, mul_nonneg ha (mul_nonneg n1 n4), mul_nonneg ha (mul_nonneg n2 n3)]

end GlobalTheory.MSpanDecay.ColConvGrowth

namespace GlobalTheory.MSpanDecay

end GlobalTheory.MSpanDecay
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedSec

theorem eq_of_pow_eq_self {R K : Type} [CommRing R] [Field K] [CharZero K] (θ : R →+* K)
    (hθ : ∀ y, θ y ≠ 0 → IsUnit y) {n : ℕ} (hn : 2 ≤ n) {u v : R} (hu : u ^ n = u) (hv : v ^ n = v)
    (h : θ u = θ v) : u = v := by
  set S := ∑ i ∈ Finset.range n, u ^ i * v ^ (n - 1 - i) with hS
  have h1 : S * (u - v) = u - v := by rw [hS, geom_sum₂_mul, hu, hv]
  have hc : θ u ^ n = θ u := by rw [← map_pow, hu]
  have e : θ S = n * θ u ^ (n - 1) := by

    rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => θ u ^ (n - 1)) (fun i hi => by
    have := Finset.mem_range.1 hi
    rw [map_mul, map_pow, map_pow, ← h, ← pow_add]
    congr 1
    omega)]
    simp
  have h2 : θ (S - 1) ≠ 0 := by
    rw [map_sub, map_one, e]
    by_cases h0 : θ u = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h3 : θ u ^ (n - 1) = 1 := by
        refine mul_right_cancel₀ h0 ?_
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, hc]
      rw [h3, mul_one, sub_ne_zero]
      exact_mod_cast (show n ≠ 1 by omega)
  have h4 : (S - 1) * (u - v) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact sub_eq_zero.1 ((hθ _ h2).mul_right_eq_zero.1 h4)

theorem exists_om_of_pow_eq_self (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : 2 ≤ n) (c : ℂ_[l]) (hc : c ^ n = c) :
    ∃ x : Om l, algebraMap (Om l) ℂ_[l] x = c := by
  have hs : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)).Splits := IsAlgClosed.splits _
  have h0 : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)) ≠ 0 := fun h => by
    have := congrArg (fun p : Polynomial (Om l) => p.coeff n) h
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, show (1 : ℕ) ≠ n by omega] at this
  obtain ⟨x, hx⟩ := hs.mem_range_of_isRoot h0 (i := algebraMap (Om l) ℂ_[l]) (x := c) (by simp [hc])
  exact ⟨x, hx⟩

private theorem padicInt_hom_apply_eq {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R]
    (hR : IsHausdorff (Ideal.span {(l : R)}) R) (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hR _ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f c - g c, ?_⟩
  have hf := congrArg f hc
  have hg := congrArg g hc
  simp only [map_mul, map_pow, map_natCast, map_sub] at hf hg
  linear_combination hf - hg

theorem exists_sec (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) :
    ∃ x : Om l, ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] x ∧
      C.o x = aDp l (wA l a w) := by
  have hspan : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    have hq : 2 ≤ l ^ a := one_lt_pow_l l a
    have hw : (WittVector.teichmuller l z) ^ (l ^ a) = WittVector.teichmuller l z := by
      rw [← map_pow, Fq.pow_card]
    set A := wA l a (WittVector.teichmuller l z) with hAdef
    have hA : A ^ (l ^ a) = A := by rw [hAdef, ← map_pow, hw]
    have hc : ((Per.θ l A : OC l) : ℂ_[l]) ^ (l ^ a) = ((Per.θ l A : OC l) : ℂ_[l]) := by
      rw [← SubmonoidClass.coe_pow, ← map_pow, hA]
    obtain ⟨x, hx⟩ := exists_om_of_pow_eq_self l hq _ hc
    have hxq : x ^ (l ^ a) = x := (algebraMap (Om l) ℂ_[l]).injective (by rw [map_pow, hx, hc])
    refine ⟨x, hx.symm, eq_of_pow_eq_self (Per.θD l) (thetaD_props l).2.2.1 hq
      (by rw [← map_pow, hxq]) (by rw [← map_pow, hA]) ?_⟩
    rw [C.o_sec.th, (thetaD_props l).2.2.2.1]
    exact hx
  | zero => exact ⟨0, by simp, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨x, hx1, hx2⟩ := hy
    obtain ⟨x', hx1', hx2'⟩ := hy'
    refine ⟨x + x', ?_, ?_⟩
    · rw [map_add (f := _), map_add (f := _), map_add (f := _), Subring.coe_add, hx1, hx1']
    · rw [map_add (f := _), map_add (f := _), map_add (f := _), hx2, hx2']
  | smul r y _ hy =>
    obtain ⟨x, hx1, hx2⟩ := hy
    have e : wA l a (r • y) = algebraMap ℤ_[l] (Ainf l) r * wA l a y := by
      rw [map_smul, Algebra.smul_def]
    refine ⟨algebraMap ℚ_[l] (Om l) (r : ℚ_[l]) * x, ?_, ?_⟩
    · rw [e, map_mul, Subring.coe_mul, hx1, map_mul]
      congr 1
      exact GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) r
    · rw [e, map_mul, map_mul, hx2, C.o_sec.z r]
      have hA : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l) := inferInstance
      rw [padicInt_hom_apply_eq hA.toIsHausdorff (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) r]

theorem o_eq_aDp_wA : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (x : Om l),
    ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = (x : ℂ_[l]) → C.o x = aDp l (wA l a w) := by
  intro l _ a _ C w x hx
  obtain ⟨y, hy1, hy2⟩ := exists_sec l a C w
  have hxy : x = y := (algebraMap (Om l) ℂ_[l]).injective (hx.symm.trans hy1)
  rw [hxy, hy2]

end GlobalTheory.SeedSec
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.galoisFixedTensorWitt_approx_frobeniusPerfection : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ y ∈ fixSub AI LL (Hinf K : Set (GQ l)), ∀ m : ℕ, ∃ (n : ℕ) (y0 : RW LL) (e : W.EE) (r : RW LL), (φRW LL)^[n] y0 = E.tie.ioE e + (l : RW LL) * r ∧ NearPi AI LL s m (y - y0) := by
  first | exact @GlobalTheory.DecomplDense.fixSub_approx_perfection | exact GlobalTheory.DecomplDense.fixSub_approx_perfection | (intros; apply GlobalTheory.DecomplDense.fixSub_approx_perfection <;> assumption)
end
