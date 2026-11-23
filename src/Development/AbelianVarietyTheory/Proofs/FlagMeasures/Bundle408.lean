module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle402
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle310
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle399
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePiPointsAtInfinitePlacesCMTypeImage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle312
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle404
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle403
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHeightBasePairEqModuleProduct
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselMap_multipleIsometry_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), 1000 ≤ Cl → (∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → 0 < θ) → (∀ w, 0 < Tr D w) → BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  first | exact @GlobalTheory.BesselSchurGap.bessel_schur | exact GlobalTheory.BesselSchurGap.bessel_schur | (intros; apply GlobalTheory.BesselSchurGap.bessel_schur <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.LoopVol

open Formalism.L2.SG.HidaSetting

theorem hJ_sum_right' {n m : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) (g : Fin m → ℂ)
    (y : Fin m → Fin n → ℂ) : hJ ε x (∑ i, g i • y i) = ∑ i, g i * hJ ε x (y i) := by
  unfold hJ
  simp only [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem ratCoord_eq_matOn : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ))) (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ)) M → ∀ q : GlobalTheory.LoopV.roots (ptMat w), GlobalTheory.LoopVol.ratCoord X u' w γ s y τ q = M q.1.1 q.1.2 := by
  intro D X u' w γ s y τ M hM q
  unfold GlobalTheory.LoopVol.ratCoord
  rw [hM q.1.2, hJ_sum_right', Fin.sum_univ_castSucc]
  have hfe : ∀ i : Fin D.R.rS, hJ (X.B.I.ε (X.pl.symm τ)) (rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
      (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) (Fin.castSucc i)) = if i = ⟨q.1.1.1, root_fst_lt w q⟩ then 1 else 0 := by
    intro i
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Fin.snoc_castSucc, Complex.ofReal_one, one_pow, inv_one, one_smul]
    exact (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X _ _ _).trans
      (by rw [Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X]; split_ifs <;> simp)
  have hfz : hJ (X.B.I.ε (X.pl.symm τ)) (rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
      (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) (Fin.last _)) = 0 := by
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Fin.snoc_last, Complex.ofReal_one, one_pow, inv_one, one_smul]
    exact (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X _ _ _).trans (by rw [(X.zu_orth u' _).2]; simp)
  simp only [hfe, hfz, mul_ite, mul_one, mul_zero, add_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1

end GlobalTheory.LoopVol
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.measurePi_pointsAtInfinitePlacesCMType_image : ∀ (D : D7) (S : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)), Measure.pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (Gm D '' S) = Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) S := by
  first | exact @GlobalTheory.CovDom.measure_Gm_image | exact GlobalTheory.CovDom.measure_Gm_image | (intros; apply GlobalTheory.CovDom.measure_Gm_image <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

open scoped Classical

namespace GlobalTheory.FrameStab

open Formalism.L2.SG.RealObj

variable {n m r : ℕ}

def colMat (f : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin m) ℂ := Matrix.of fun i a => f a i

theorem isMatOn_iff (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin m → Fin n → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.LoopAct.IsMatOn g f M ↔ g * colMat f = colMat f * M := by
  constructor
  · intro h
    ext i b
    have := congrFun (h b) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply, this, mul_comm]
  · intro h b
    ext i
    have := congrFun (congrFun h i) b
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply] at this
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, this, mul_comm]

theorem zhat_eq (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.L2.SG.RealObj.Zhat ε f f' G = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  ext a b
  simp only [Formalism.L2.SG.RealObj.Zhat, Formalism.L2.SG.HidaSetting.hJ, Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat,
    Matrix.of_apply, Matrix.conjTranspose_apply, Pi.star_apply]

theorem conjTranspose_mul_zhat_mul {ε : Fin n → Bool} {f f' : Fin (r + 1) → Fin n → ℂ}
    {Y G Gi : Matrix (Fin n) (Fin n) ℂ} {P M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hY : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε) (hG : G * Gi = 1)
    (hP : GlobalTheory.LoopAct.IsMatOn Y f P) (hM : GlobalTheory.LoopAct.IsMatOn (Gi * Y * G) f' M) :
    Pᴴ * (Formalism.L2.SG.RealObj.Zhat ε f f' G * M) = Formalism.L2.SG.RealObj.Zhat ε f f' G := by
  rw [isMatOn_iff] at hP hM
  rw [zhat_eq]
  calc Pᴴ * ((colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' * M)
      = (colMat f * P)ᴴ * Formalism.REAL.Jm ε * G * (colMat f' * M) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Y * colMat f)ᴴ * Formalism.REAL.Jm ε * G * (Gi * Y * G * colMat f') := by rw [hP, hM]
    _ = (colMat f)ᴴ * (Yᴴ * Formalism.REAL.Jm ε * ((G * Gi) * Y)) * G * colMat f' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
        rw [hG, Matrix.one_mul, hY]

theorem isLoUni_conjTranspose {N : ℕ} {P : Matrix (Fin N) (Fin N) ℂ} (h : Formalism.MainNotions.S.IsUpUni P) :
    Formalism.MainNotions.S.IsLoUni Pᴴ := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.conjTranspose_apply, (h j i).1 hij, star_zero]
  · rw [Matrix.conjTranspose_apply, (h j i).2 hij.symm, star_one]

theorem mem_stabU_of_conjTranspose_mul {N : ℕ} {Z P M : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det)
    (hP : Formalism.MainNotions.S.IsUpUni P) (hM : Formalism.MainNotions.S.IsUpUni M) (h : Pᴴ * (Z * M) = Z) :
    M ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨hM, ?_⟩
  have e : Pᴴ * (Z * M * Z⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_nonsing_inv _ hZ]
  rw [← Matrix.inv_eq_right_inv e]
  exact (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (isLoUni_conjTranspose hP)).1

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

variable {n r : ℕ}

theorem exists_coeff_of_mem_spanLt {e : Fin r → Fin n → ℂ} {k : ℕ} {x : Fin n → ℂ}
    (hx : x ∈ Formalism.L2.SG.HidaSetting.spanLt e k) :
    ∃ c : Fin r → ℂ, (∀ b : Fin r, ¬ b.1 < k → c b = 0) ∧ x = ∑ b, c b • e b := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hx
  refine ⟨l, fun b hb => ?_, ?_⟩
  · exact (Finsupp.mem_supported' ℂ l).1 hl b hb
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _

theorem exists_isUpUni_isMatOn {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.L2.SG.HidaSetting.InS e z Y) :
    ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, Formalism.MainNotions.S.IsUpUni P ∧
      GlobalTheory.LoopAct.IsMatOn Y (Formalism.L2.SG.RealObj.fam e z) P := by
  choose ca hca0 hcae using fun a : Fin r => exists_coeff_of_mem_spanLt (h.1 a)
  obtain ⟨cz, -, hcz⟩ := exists_coeff_of_mem_spanLt h.2
  let Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := fun i j =>
    Fin.lastCases (motive := fun _ => ℂ) 0
      (fun c : Fin r => Fin.lastCases (motive := fun _ => ℂ) (cz c) (fun a : Fin r => ca a c) j) i
  have hQl : ∀ j, Q (Fin.last r) j = 0 := fun j => by simp [Q]
  have hQcl : ∀ c, Q (Fin.castSucc c) (Fin.last r) = cz c := fun c => by simp [Q]
  have hQcc : ∀ c a, Q (Fin.castSucc c) (Fin.castSucc a) = ca a c := fun c a => by simp [Q]
  refine ⟨1 + Q, fun i j => ?_, fun b => ?_⟩
  · refine Fin.lastCases ?_ (fun c => ?_) i
    · refine ⟨fun hj => ?_, fun hj => ?_⟩
      · rw [Matrix.add_apply, hQl, Matrix.one_apply_ne (ne_of_lt hj).symm, add_zero]
      · rw [Matrix.add_apply, hQl, hj, Matrix.one_apply_eq, add_zero]
    · refine Fin.lastCases ?_ (fun a => ?_) j
      · exact ⟨fun hj => absurd hj (not_lt.2 (Fin.castSucc_lt_last c).le),
          fun hj => absurd hj (Fin.castSucc_lt_last c).ne⟩
      · refine ⟨fun hj => ?_, fun hj => ?_⟩
        · rw [Matrix.add_apply, hQcc, Matrix.one_apply_ne (ne_of_lt hj).symm, zero_add]
          exact hca0 a c (not_lt.2 (Fin.castSucc_lt_castSucc_iff.1 hj).le)
        · rw [Matrix.add_apply, hQcc, hj, Matrix.one_apply_eq, Fin.castSucc_inj.1 hj]
          rw [hca0 a a (lt_irrefl _), add_zero]
  · rw [Fin.sum_univ_castSucc]
    simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last, Matrix.add_apply, add_smul,
      Finset.sum_add_distrib, hQl, zero_smul, add_zero]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simp only [Fin.snoc_last, hQcl, Matrix.one_apply_eq, one_smul,
        Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne, zero_smul, Finset.sum_const_zero, zero_add]
      rw [← hcz, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    · simp only [Fin.snoc_castSucc, hQcc, Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne', zero_smul,
        add_zero]
      have e1 : ∑ x : Fin r, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.castSucc x) (Fin.castSucc a) • e x
          = e a := by
        simp only [Matrix.one_apply, Fin.castSucc_inj, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [e1, ← hcae a, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

theorem frameMat_mem_stabU : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ y : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), y ∈ Formalism.L2.SG.RealObj.StInf X u u' γ → IsUpUni M → GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * y * γ) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) M → IsUnit (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v).det → M ∈ GlobalTheory.LoopV.stabU (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v) := by
  intro D X u u' γ y v M hy hMu hM hZ
  obtain ⟨P, hPu, hP⟩ := exists_isUpUni_isMatOn ((hy.1 v).1)
  have hf : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam
      (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  rw [← hf] at hP
  have hY : (uMat (y v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (y v) = Formalism.REAL.Jm (X.B.I.ε v) := (y v).2
  have hG : uMat (γ v) * uMat (γ⁻¹ v) = 1 := by
    show uMat ((γ * γ⁻¹) v) = 1
    rw [mul_inv_cancel]
    rfl
  exact mem_stabU_of_conjTranspose_mul hZ hPu hMu (conjTranspose_mul_zhat_mul hY hG hP hM)

end GlobalTheory.FrameStab

end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.LoopAct

open scoped Classical

theorem exists_coeff_of_mem_span_image {r n : ℕ} (e : Fin r → Fin n → ℂ) (s : Set (Fin r)) (x : Fin n → ℂ)
    (hx : x ∈ Submodule.span ℂ (e '' s)) : ∃ c : Fin r → ℂ, (∀ b, b ∉ s → c b = 0) ∧ x = ∑ b, c b • e b := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  refine ⟨l, fun b hb => ?_, ?_⟩
  · by_contra h
    exact hb (hl (Finsupp.mem_support_iff.mpr h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro b
    exact zero_smul ℂ (e b)

theorem exists_upUni_of_inS {r n : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : Formalism.L2.SG.HidaSetting.InS e z g) :
    ∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUpUni M ∧
      IsMatOn g (Fin.snoc (α := fun _ => Fin n → ℂ) e z) M := by
  set f : Fin (r + 1) → Fin n → ℂ := Fin.snoc (α := fun _ => Fin n → ℂ) e z with hf

  have hcol : ∀ b : Fin (r + 1), (g - 1) *ᵥ f b ∈ Submodule.span ℂ (e '' {c : Fin r | c.1 < b.1}) := by
    intro b
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simpa [hf, Formalism.L2.SG.HidaSetting.spanLt] using hg.2
    · simpa [hf, Formalism.L2.SG.HidaSetting.spanLt] using hg.1 a
  choose D hD0 hDs using fun b => exists_coeff_of_mem_span_image e _ _ (hcol b)
  refine ⟨fun c b => (if c = b then 1 else 0) + (if h : c.1 < r then D b ⟨c.1, h⟩ else 0), ?_, ?_⟩
  · intro i j
    constructor
    · intro hji
      have hne : i ≠ j := fun h => (lt_irrefl j) (h ▸ hji)
      simp only [hne, if_false, zero_add]
      split_ifs with h
      · apply hD0
        simp only [Set.mem_setOf_eq, not_lt]
        exact le_of_lt hji
      · rfl
    · rintro rfl
      simp only [if_true]
      split_ifs with h
      · rw [hD0 i ⟨i.1, h⟩ (by simp)]
        ring
      · ring
  · intro b
    have hg1 : g *ᵥ f b = (g - 1) *ᵥ f b + f b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    rw [hg1, hDs b]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [add_comm, Fin.sum_univ_castSucc]
    simp [hf]

theorem sinfU_frame_upUni : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : X.B.I.Ginf), y ∈ X.SinfU u → ∀ v : NumberField.InfinitePlace X.B.I.F, ∃ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, IsUpUni M ∧ GlobalTheory.LoopAct.IsMatOn (uMat (y v)) (Formalism.L2.SG.RealObj.frm X u 1 v) M := by
  intro D X u y hy v
  obtain ⟨M, hM, hMat⟩ := exists_upUni_of_inS _ _ _ (hy v)
  refine ⟨M, hM, ?_⟩
  have hfr : Formalism.L2.SG.RealObj.frm X u 1 v = Fin.snoc (α := fun _ => Fin X.B.I.n → ℂ)
      (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Formalism.L2.SG.RealObj.fam]
  rw [hfr]
  exact hMat

end GlobalTheory.LoopAct

end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.ZxMul

theorem zx_mul : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (g γ h : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (C B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat (g⁻¹ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) C → GlobalTheory.LoopAct.IsMatOn (uMat (h v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) B → Formalism.L2.SG.RealObj.ZX X u u' 1 (g * γ * h) v = Cᴴ * Formalism.L2.SG.RealObj.ZX X u u' 1 γ v * B := by
  intro D X u u' g γ h v C B hC hB
  have hU : (uMat (g⁻¹ v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (g⁻¹ v) = Formalism.REAL.Jm (X.B.I.ε v) := (g⁻¹ v).2
  have e : uMat ((g * γ * h) v) = uMat (g v) * uMat (γ v) * uMat (h v) := rfl
  have hL : ∀ a, uMat (g⁻¹ v) *ᵥ Formalism.L2.SG.RealObj.frm X u 1 v a =
      ∑ c, Cᵀ a c • Formalism.L2.SG.RealObj.frm X u 1 v c := fun a => by
    rw [hC a]; rfl
  have hM : ∀ b, uMat (h v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b =
      ∑ d, Bᵀ b d • Formalism.L2.SG.RealObj.frm X u' 1 v d := fun b => by
    rw [hB b]; rfl
  unfold Formalism.L2.SG.RealObj.ZX
  rw [e, GlobalTheory.GxConj.zhat_conj _ _ _ _ _ _ _
    (GlobalTheory.GxConj.hJ_adj _ _ _ hU (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (g v))) _ _ hL hM,
    Matrix.transpose_transpose]
  rfl

end GlobalTheory.ZxMul
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nongeneric_row_statements_of_family_statements : FamNG → (FamilyWeightSumUnfoldingIdentity → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) ∧ (WeightsFam → Formalism.L2.SG.FamDefs.WeightsNG) ∧ (FamilyGroupSumFactorsWeightAmplitude → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) ∧ (ExistFam → Formalism.L2.SG.FamDefs.ExistNG) := by
  first | exact @GlobalTheory.SnFamNG.leaves_of_fam | exact GlobalTheory.SnFamNG.leaves_of_fam | (intros; apply GlobalTheory.SnFamNG.leaves_of_fam <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.nonzeroFlagProbabilityBound_of_volumeRatioInduction : VolumeStep → NonzeroFlagBound := by
  first | exact @GlobalTheory.NonzeroFlag.nonzeroFlagBound | exact GlobalTheory.NonzeroFlag.nonzeroFlagBound | (intros; apply GlobalTheory.NonzeroFlag.nonzeroFlagBound <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleCoset_terms_same_innerLattices : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).1 = (G.datOf (c.lat ρ t₀.lam) p).1 ∧ (G.datOf (c.lat (ρ * n) t.lam) p).2.1 = (G.datOf (c.lat ρ t₀.lam) p).2.1 := by
  first | exact @GlobalTheory.HL.datOf_dcoset | exact GlobalTheory.HL.datOf_dcoset | (intros; apply GlobalTheory.HL.datOf_dcoset <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleCoset_term_eq_iff_stabiliserOrbit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t t' : TauC Y u u') n m n' m', t.lam = t₀.lam → t.lam' = t₀.lam' → t'.lam = t₀.lam → t'.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → n' ∈ NRat (lf D (X.Fu u)) ∧ m' ∈ NRat (lf D (X.Fu u')) ∧ t'.lin = n'⁻¹ * t₀.lin * m' → (t = t' ↔ G.LRel (c.lat (ρ * n) t.lam) (c.lat (ρ * n') t'.lam)) := by
  first | exact @GlobalTheory.HL.TermOrbit.term_eq_iff_lRel | exact GlobalTheory.HL.TermOrbit.term_eq_iff_lRel | (intros; apply GlobalTheory.HL.TermOrbit.term_eq_iff_lRel <;> assumption)
end

section


theorem _root_.GlobalTheory.T.product_modules_type_uniformisers_eq_power : Formalism.L2.SG.NGHTie.HTTheta := by
  first | exact @GlobalTheory.HTThetaLeaf.main | exact GlobalTheory.HTThetaLeaf.main | (intros; apply GlobalTheory.HTThetaLeaf.main <;> assumption)
end

section


theorem _root_.GlobalTheory.T.local_height_base_pair_eq_module_product : Formalism.L2.SG.NGHTie.HTPlace := by
  first | exact @GlobalTheory.HTPlaceLeaf.htPlace | exact GlobalTheory.HTPlaceLeaf.htPlace | (intros; apply GlobalTheory.HTPlaceLeaf.htPlace <;> assumption)
end
