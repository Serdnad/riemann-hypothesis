module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSStatements
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.OpNormLeOneOfIso
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.Bundle001

@[expose] public section

section

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Meas

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

theorem ae_UH_of_haar {μG : Measure (Mt k r)} (h : IsHaarOn (UH (Hpk k r)) μG) :
    ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by
  rw [ae_iff]
  exact h.2.2.1

private theorem isClosed_UH' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    IsClosed (UH A) := by
  have hc : Continuous fun g : Matrix n n ℂ => gᴴ * A * g :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const

theorem measurableSet_UH' : MeasurableSet {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := by
  exact ((isClosed_UH' (Hpk k r)).preimage (continuous_id : Continuous fun y : Mt k r => y)).measurableSet

theorem coef_contOn {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) (w v : H) :
    ContinuousOn (fun y : Mt k r => ⟪v, σ (Matrix.of y) w⟫_ℂ) {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := by
  have hσ := (ds_rep hds).2.2.2 w
  have hof : Continuous fun y : Mt k r => (Matrix.of y : Mx k r) := continuous_id
  exact continuousOn_const.inner (hσ.comp hof.continuousOn fun y hy => hy)

theorem coef_aesm {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {μG : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG) (w v : H) :
    AEStronglyMeasurable (fun y : Mt k r => ⟪v, σ (Matrix.of y) w⟫_ℂ) μG := by
  have h1 := (coef_contOn hds w v).aestronglyMeasurable (measurableSet_UH' (k := k) (r := r)) (μ := μG)
  rwa [Measure.restrict_eq_self_of_ae_mem (s := {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)})
    (ae_UH_of_haar hG)] at h1

def Tset (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × (Mt k r × Mt k r)) :=
  {q | Matrix.of q.1 ∈ UH (Hpk k r) ∧ (Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r)}

private theorem isClosed_UWset' (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have h1 : ∀ u : Fin (2 * r + k + 1) → ℂ, Continuous fun g : Mx k r => g *ᵥ u :=
    fun u => continuous_id.matrix_mulVec continuous_const
  simp only [UWset, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_UH' _).inter ((isClosed_iInter fun a =>
    (isClosed_eq (h1 _) continuous_const).inter (isClosed_eq (h1 _) continuous_const)).inter
      (isClosed_eq (h1 _) continuous_const))

private theorem isClosed_Nset_bessel_line (k r : ℕ) : IsClosed (Nset k r) := by
  simp only [Nset, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_UH' _).inter ((isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem _ _) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem _ _) continuous_const))

theorem measurableSet_Tset (z : Fin (2 * r + k + 1) → ℂ) : MeasurableSet (Tset (k := k) (r := r) z) := by
  have c1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mx k r) := continuous_fst
  have c2 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mx k r) :=
    continuous_fst.comp continuous_snd
  have c3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mx k r) :=
    continuous_snd.comp continuous_snd
  exact (((isClosed_UH' (Hpk k r)).preimage c1).inter
    (((isClosed_UWset' (k := k) (r := r) z).preimage c2).inter ((isClosed_Nset_bessel_line k r).preimage c3))).measurableSet

theorem joint_ae {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    [SFinite μG] (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ Tset z := by
  have h1 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ UH (Hpk k r) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_UH_of_haar hG)
  have h2 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae hM1
  filter_upwards [h1, h2] with q hq1 hq2
  exact ⟨hq1, hq2⟩

theorem matrix_coefficient_continuousOn {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} (hGr : Cv.GrpF k r z) (w v : H) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => ⟪v, σ (sM q.2 * Matrix.of q.1) w⟫_ℂ) (Tset z) := by
  have hσ := (ds_rep hds).2.2.2 w
  have a1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mx k r) :=
    continuous_fst.comp continuous_snd
  have a2 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mx k r) :=
    continuous_snd.comp continuous_snd
  have a3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mx k r) := continuous_fst
  have hc : Continuous fun q : Mt k r × (Mt k r × Mt k r) => sM q.2 * Matrix.of q.1 := by
    unfold sM
    exact (a1.matrix_mul a2).matrix_mul a3
  refine continuousOn_const.inner (hσ.comp hc.continuousOn ?_)
  intro q hq
  obtain ⟨h1, h2, h3⟩ := hq
  exact hGr.1 _ (hGr.1 _ h2.1 _ h3.1) _ h1

theorem matrix_coefficient_ae_strongly_measurable {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} (hGr : Cv.GrpF k r z)
    {μW μN μG : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite μG] (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) (w v : H) :
    AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) => ⟪v, σ (sM q.2 * Matrix.of q.1) w⟫_ℂ)
      (μG.prod (μW.prod μN)) := by
  have h := (matrix_coefficient_continuousOn hds hGr w v).aestronglyMeasurable (measurableSet_Tset z) (μ := μG.prod (μW.prod μN))
  rwa [Measure.restrict_eq_self_of_ae_mem (joint_ae hG hM1)] at h

theorem sfinite_haar {μG : Measure (Mt k r)} (h : IsHaarOn (UH (Hpk k r)) μG) : SFinite μG := by
  have := h.1
  infer_instance

end Meas

end PI.WBL.FSW
end
end

section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem psi_mul_star (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) :
    psi k r z c g * star (psi k r z c g) = 1 := by
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero
  simp <;> ring

theorem beF_tEq (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c)
    (h m : Mx k r) (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) (w v : H) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    beF z c π σ (σ (h * m) w) v p =
      (psi k r z c m • π h).comp (beF z c π σ w v (tEq h m p)) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG
  obtain ⟨hs1, hsm, hsn⟩ := hσ
  obtain ⟨hp1, hpm, hpn⟩ := hπ
  obtain ⟨ψ1, ψ2, ψ3, ψ4⟩ := hψ
  obtain ⟨hP1, hP2⟩ := hp
  have hhU : h ∈ UH (Hpk k r) := hh.1
  have hmU : m ∈ UH (Hpk k r) := hm.1
  have hP1U : Matrix.of p.1 ∈ UH (Hpk k r) := hP1.1
  have hP2U : Matrix.of p.2 ∈ UH (Hpk k r) := hP2.1
  have hinv : h * h⁻¹ = 1 := (g2 h hhU).1
  have e1 : Matrix.of (tEq h m p).1 = Matrix.of p.1 * h := rfl
  have e2 : Matrix.of (tEq h m p).2 = h⁻¹ * Matrix.of p.2 * h * m := rfl
  have hQ : Matrix.of p.1 * h * (h⁻¹ * Matrix.of p.2 * h * m) =
      Matrix.of p.1 * Matrix.of p.2 * (h * m) := by
    calc _ = Matrix.of p.1 * (h * h⁻¹) * Matrix.of p.2 * (h * m) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hinv, Matrix.mul_one]
  have hσw : σ (Matrix.of p.1 * Matrix.of p.2) (σ (h * m) w) =
      σ (Matrix.of p.1 * Matrix.of p.2 * (h * m)) w := by
    rw [hsm _ (g1 _ hP1U _ hP2U) _ (g1 _ hhU _ hmU)]
    rfl
  have hn : h⁻¹ * Matrix.of p.2 * h ∈ Nset k r := g5 h hh _ hP2
  have hψQ : psi k r z c (h⁻¹ * Matrix.of p.2 * h * m) = psi k r z c (Matrix.of p.2) * psi k r z c m := by
    rw [ψ1 _ hn _ hm, ψ2 h hh _ hP2]
  have hπQ : (π h).comp (π (Matrix.of p.1 * h)⁻¹) = π (Matrix.of p.1)⁻¹ := by
    have hu : h⁻¹ * (Matrix.of p.1)⁻¹ ∈ UWset k r z := g7 _ (g3 h hh) _ (g3 _ hP1)
    rw [Matrix.mul_inv_rev, ← hpm h hh _ hu, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hms := psi_mul_star z c m
  unfold beF
  rw [e1, e2, hQ, hσw, hψQ, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, hπQ, smul_smul]
  congr 1
  rw [star_mul]
  first
  | linear_combination (-(⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * (h * m)) w⟫_ℂ *
      star (psi k r z c (Matrix.of p.2)))) * hms
  | linear_combination (⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * (h * m)) w⟫_ℂ *
      star (psi k r z c (Matrix.of p.2))) * hms

def adjR (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] :
    (Wp →L[ℂ] Wp) →ₗᵢ[ℝ] (Wp →L[ℂ] Wp) where
  toFun T := ContinuousLinearMap.adjoint T
  map_add' S T := map_add _ S T
  map_smul' a T := by
    show ContinuousLinearMap.adjoint (a • T) = a • ContinuousLinearMap.adjoint T
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a T,
      RCLike.real_smul_eq_coe_smul (K := ℂ) a (ContinuousLinearMap.adjoint T),
      LinearIsometryEquiv.map_smulₛₗ]
    simp
  norm_map' T := ContinuousLinearMap.adjoint.norm_map T

theorem beF_tInv (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c)
    (w v : H) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    beF z c π σ v w (tInv p) = ContinuousLinearMap.adjoint (beF z c π σ w v p) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG
  obtain ⟨hs1, hsm, hsn⟩ := hσ
  obtain ⟨hp1, hpm, hpn⟩ := hπ
  obtain ⟨ψ1, ψ2, ψ3, ψ4⟩ := hψ
  obtain ⟨hP1, hP2⟩ := hp
  have hP1U : Matrix.of p.1 ∈ UH (Hpk k r) := hP1.1
  have hP2U : Matrix.of p.2 ∈ UH (Hpk k r) := hP2.1
  have hAU : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := g1 _ hP1U _ hP2U
  have e1 : Matrix.of (tInv p).1 = (Matrix.of p.1)⁻¹ := rfl
  have e2 : Matrix.of (tInv p).2 = Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ := rfl
  have hQ : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
      (Matrix.of p.1 * Matrix.of p.2)⁻¹ := by
    rw [Matrix.mul_inv_rev]
    calc _ = ((Matrix.of p.1)⁻¹ * Matrix.of p.1) * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [(g2 _ hP1U).2.1, Matrix.one_mul]
  have hψQ : psi k r z c (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
      star (psi k r z c (Matrix.of p.2)) := by
    rw [ψ3 _ hP1 _ (g4 _ hP2), ψ4 _ hP2]
  have hσadj : ⟪w, σ (Matrix.of p.1 * Matrix.of p.2)⁻¹ v⟫_ℂ = ⟪σ (Matrix.of p.1 * Matrix.of p.2) w, v⟫_ℂ := by
    set A := Matrix.of p.1 * Matrix.of p.2 with hAdef
    have hAi := g2 A hAU
    let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ A : H →ₗ[ℂ] H), norm_map' := hsn A hAU }
    have hv : σ A (σ A⁻¹ v) = v := by
      rw [← ContinuousLinearMap.comp_apply, ← hsm A hAU _ hAi.2.2, hAi.1, hs1, ContinuousLinearMap.one_apply]
    calc ⟪w, σ A⁻¹ v⟫_ℂ = ⟪L w, L (σ A⁻¹ v)⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪σ A w, σ A (σ A⁻¹ v)⟫_ℂ := rfl
      _ = ⟪σ A w, v⟫_ℂ := by rw [hv]
  have hπadj : ContinuousLinearMap.adjoint (π (Matrix.of p.1)⁻¹) = π ((Matrix.of p.1)⁻¹)⁻¹ := by
    set A := (Matrix.of p.1)⁻¹ with hAdef
    have hA : A ∈ UWset k r z := g3 _ hP1
    have hAi : A⁻¹ ∈ UWset k r z := g3 _ hA
    have h1 : A * A⁻¹ = 1 := (g2 A hA.1).1
    let L : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π A : Wp →ₗ[ℂ] Wp), norm_map' := hpn A hA }
    have hx : ∀ x : Wp, π A (π A⁻¹ x) = x := by
      intro x
      rw [← ContinuousLinearMap.comp_apply, ← hpm A hA _ hAi, h1, hp1, ContinuousLinearMap.one_apply]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    calc ⟪π A⁻¹ x, y⟫_ℂ = ⟪L (π A⁻¹ x), L y⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪π A (π A⁻¹ x), π A y⟫_ℂ := rfl
      _ = ⟪x, π A y⟫_ℂ := by rw [hx]
  unfold beF
  rw [e1, e2, hQ, hψQ, star_star, hσadj, LinearIsometryEquiv.map_smulₛₗ, hπadj]
  congr 1
  simp only [map_mul, inner_conj_symm, Complex.star_def, Complex.conj_conj]

end PI.WBL.Cv
end
end

section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

def GrpAll : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), GrpF k r z

def SigAll : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ → SigU σ

def PiAll : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)),
    inWb k r z → 0 < Tz k r z → IsHCTypeW k r z u π → PiU z π

def PsiAll : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), inWb k r z → PsiF k r z c

instance sfinite_muN {k r : ℕ} (L : LocBessel k r) : SFinite L.μN := by
  unfold LocBessel.μN haarLie
  infer_instance

end PI.WBL.Cv
end
end
