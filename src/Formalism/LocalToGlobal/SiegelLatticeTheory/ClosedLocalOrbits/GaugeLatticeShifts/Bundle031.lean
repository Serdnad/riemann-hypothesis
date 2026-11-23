module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameWZeroExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle005
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeftInverseThreeBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
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

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

section Cons

variable {n r : ℕ} (ε : Fin n → Bool)

def lamOf (sc : ℝ) (c : Fin (r + 1) → ℂ) (b : Fin r) : ℂ :=
  c (Fin.castSucc b) / (((sc : ℂ) ^ (r - b.1))⁻¹ * ((sc : ℂ) ^ (r - b.1))⁻¹)

def alOf (T : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := -c (Fin.last r) / T

def beOf (T T' : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := ((Real.sqrt (‖c (Fin.last r)‖ ^ 2 / T - T') : ℝ) : ℂ)

theorem zhat_of_images (e f : Fin r → Fin n → ℂ) (z z' w : Fin n → ℂ) (T sc : ℝ) (β : ℂ)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) (hez : ∀ a, hJ ε (e a) z = 0)
    (hzf : ∀ b, hJ ε z (f b) = 0) (hew : ∀ a, hJ ε (e a) w = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : hJ ε z w = 0) (hT : T ≠ 0) (hsc : 0 < sc) (c : Fin (r + 1) → ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (hMe : ∀ b, M *ᵥ e b = lamOf sc c b • f b) (hMz : M *ᵥ z' = alOf T c • z + β • w) :
    Zhat ε (famSc sc e z) (famSc sc e z') M = Matrix.diagonal c := by
  have hsc0 : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hne : ∀ b : Fin r, Fin.last r ≠ Fin.castSucc b := fun b h => Fin.castSucc_ne_last b h.symm
  ext a b
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul, hMz,
      hJ_add_r, hJ_smul_r, hzz, hzw, mul_zero, add_zero, Matrix.diagonal_apply_eq, alOf]
    field_simp
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Nat.sub_self, pow_zero, inv_one,
      one_smul, mulVec_smul, hMe, hJ_smul_r, hzf, mul_zero, Matrix.diagonal_apply_ne _ (hne b)]
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Nat.sub_self, pow_zero, inv_one,
      one_smul, hMz, hJ_smul_l, hJ_add_r, hJ_smul_r, hez, hew, mul_zero, add_zero,
      Matrix.diagonal_apply_ne _ (hne a).symm]
  · simp only [Zhat, famSc, fam, Fin.snoc_castSucc, Fin.val_castSucc, mulVec_smul, hMe, hJ_smul_l, hJ_smul_r, hef,
      Matrix.diagonal_apply, Fin.castSucc_inj, lamOf]
    split_ifs with h
    · subst h
      simp only [map_inv₀, map_pow, Complex.conj_ofReal]
      field_simp
    · simp

theorem step_isIsom (a b : Fin n → ℂ) (hab : hJ ε a a = hJ ε b b) :
    IsIsom ε (tv ε (a - b) (hJ ε (a - b) a)⁻¹) := by
  apply tv_isIsom
  set w := hJ ε (a - b) a with hw
  have haa : conj (hJ ε a a) = hJ ε a a := hJ_self_conj ε a
  have huu : hJ ε (a - b) (a - b) = w + conj w := by
    simp only [hw, hJ_sub_left, hJ_sub_right, map_sub, haa, ← hJ_conj ε a b]
    rw [← hab]
    ring
  rw [huu]
  by_cases h0 : w = 0
  · simp [h0]
  · have h1 : conj w ≠ 0 := (map_ne_zero _).2 h0
    rw [map_inv₀]
    field_simp
    ring

theorem step_apply (a b : Fin n → ℂ) (h0 : hJ ε (a - b) a ≠ 0) : tv ε (a - b) (hJ ε (a - b) a)⁻¹ *ᵥ a = b := by
  rw [tv_apply, inv_mul_cancel₀ h0, one_smul, sub_sub_cancel]

theorem entry_eq (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : A i j = (A *ᵥ Pi.single j 1) i := by
  simp [mulVec, dotProduct, Pi.single_apply]

variable {α : Type*} [MeasurableSpace α]

theorem meas_hJ (x y : α → Fin n → ℂ) (hx : ∀ l, Measurable fun c => x c l) (hy : ∀ l, Measurable fun c => y c l) :
    Measurable fun c => hJ ε (x c) (y c) := by
  unfold hJ
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  refine (Complex.continuous_conj.measurable.comp (hx l)).mul ?_
  exact Finset.measurable_sum _ fun m _ => measurable_const.mul (hy m)

theorem meas_mul (A B : α → Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, Measurable fun c => A c i j)
    (hB : ∀ i j, Measurable fun c => B c i j) : ∀ i j, Measurable fun c => (A c * B c) i j := fun i j => by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hB k j)

theorem meas_tvm {ι : Type} [Fintype ι] [DecidableEq ι] (u : α → ι → Fin n → ℂ) (ξ : α → ι → ℂ)
    (hu : ∀ b l, Measurable fun c => u c b l) (hξ : ∀ b, Measurable fun c => ξ c b) :
    ∀ i j, Measurable fun c => tvm ε (u c) (ξ c) i j := fun i j => by
  simp only [entry_eq _ i j, tvm_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine measurable_const.sub (Finset.measurable_sum _ fun b _ => ?_)
  exact ((hξ b).mul (meas_hJ ε (fun c => u c b) (fun _ => Pi.single j 1) (hu b) fun _ => measurable_const)).mul
    (hu b i)

theorem meas_tv (u : α → Fin n → ℂ) (ξ : α → ℂ) (hu : ∀ l, Measurable fun c => u c l) (hξ : Measurable ξ) :
    ∀ i j, Measurable fun c => tv ε (u c) (ξ c) i j := fun i j => by
  simp only [entry_eq _ i j, tv_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact measurable_const.sub ((hξ.mul (meas_hJ ε u (fun _ => Pi.single j 1) hu fun _ => measurable_const)).mul (hu i))

end Cons

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Matrix

namespace Formalism.L2.SG.RealObj.RealFramesCharacters

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem fam_rv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a = rv X.B.I v (X.crd ((X.Fu u).fvec a)) := by
  induction a using Fin.lastCases with
  | last => simp only [fam, Fin.snoc_last, FlagG.fvec, X.flagZVector u]; rfl
  | cast b => simp only [fam, Fin.snoc_castSucc, FlagG.fvec, X.Fu_e u]; rfl

theorem rv_sum (v : InfinitePlace X.B.I.F) {ι : Type} (t : Finset ι) (c : ι → X.B.I.E) (y : ι → Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (∑ i ∈ t, c i • y i) = ∑ i ∈ t, X.B.I.φ v (c i) • rv X.B.I v (y i) := by
  unfold rv
  have h : (fun j => X.B.I.φ v ((∑ i ∈ t, c i • y i) j)) =
      ∑ i ∈ t, X.B.I.φ v (c i) • (fun j => X.B.I.φ v (y i j)) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, smul_eq_mul, map_mul]
  rw [h, Matrix.mulVec_sum]
  congr 1
  funext i
  rw [Matrix.mulVec_smul]

theorem real_frame (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hRL : Formalism.L2.SG.TermOp.RatLink X x n) (un : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hun : ∀ b, n ((X.Fu u).fvec b) = ∑ c, un c b • (X.Fu u).fvec c) (v : InfinitePlace X.B.I.F)
    (a : Fin (D.R.rS + 1)) :
    uMat (x.1 v) *ᵥ fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a =
      ∑ c, X.B.I.φ v (X.ιE.symm (un c a)) • fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) c := by
  obtain ⟨M, -, hv, -, hcrd⟩ := hRL
  simp only [fam_rv]
  rw [hv v, Formalism.L2.SG.Pf.rv_mulVec, ← hcrd, hun, Formalism.L2.SG.NormCut.crd_sum']
  simp only [Formalism.L2.SG.NormCut.crd_smul']
  rw [rv_sum]

theorem psiInf_rat (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hRL : Formalism.L2.SG.TermOp.RatLink X x n) (un : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hun : ∀ b, n ((X.Fu u).fvec b) = ∑ c, un c b • (X.Fu u).fvec c) :
    X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf X.B.g (Formalism.L2.SG.PairVal.sgUp un) := by
  refine FormRegularity.psi_of_frame X u x.1 (fun v => (un.map (fun t => X.B.I.φ v (X.ιE.symm t)))ᵀ)
    (fun v a => by simpa [Matrix.transpose_apply, Matrix.map_apply] using real_frame X u hRL un hun v a) _ fun v => ?_

  simp only [Matrix.transpose_apply, Matrix.map_apply, FormRegularity.sgUp_eq, map_sum, star_sum, ← Finset.sum_add_distrib]

end Formalism.L2.SG.RealObj.RealFramesCharacters
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Matrix

namespace Formalism.L2.SG.RealObj.RealPointRepresentatives

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames Formalism.L2.SG.RealObj.FormRegularity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem exists_ptRep (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1))
    (L U : Formalism.L2.SG.PairVal.MatR D) (hLo : IsLoUni L) (hUp : IsUpUni U)
    (hZ : ∀ v, ZhatO (ZX X u u' 1 γ v) = (L * ptMat w * U).map (fun x => X.B.I.φ v (X.ιE.symm x))) :
    ∃ γw, IsPtRep X u u' w γw := by
  let ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ := fun v => (X.B.I.φ v).comp X.ιE.symm.toRingHom
  let P : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v => (L.map (ψ v)).map star
  let P' : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
    fun v => (sgn D.R.rS * U.map (ψ v) * sgn D.R.rS)ᵀ
  have hzz : ∀ (w' : D.what₂.Word) v, hJ (X.B.I.ε v) (rv X.B.I v (X.zR w')) (rv X.B.I v (X.zR w')) ≠ 0 := by
    intro w' v
    rw [(HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.1]
    exact neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.2)
  have hs : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v),
      InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s) ∧
      ∀ a, uMat s *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) a =
        ∑ c, P v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) c := fun v =>
    ThreeBlockFrameInverses.NRealize_holds X.B.I.n D.R.rS (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.1
      (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.2.1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.2.2.2.1 (hzz u v) (P v)
      (isLoUni_star (isLoUni_map _ hLo))
  have hs' : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v),
      InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat s) ∧
      ∀ a, uMat s *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) a =
        ∑ c, P' v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) c := fun v =>
    ThreeBlockFrameInverses.NRealize_holds X.B.I.n D.R.rS (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u')) (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.1
      (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.2.1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.2.2.2.1 (hzz u' v) (P' v)
      (isLoUni_sgnT (isUpUni_map _ hUp))
  choose s hsN hsP using hs
  choose s' hs'N hs'P using hs'
  have hsN' : s ∈ X.NinfU u := fun v => hsN v
  have hs'N' : s' ∈ X.NinfU u' := fun v => hs'N v
  have hsS : s ∈ X.SinfU u := fun v => (hsN v).1
  have hs'S : s' ∈ X.SinfU u' := fun v => (hs'N v).1

  have hPt : IsPtRep X u u' w (s * γ * s'⁻¹) := by
    intro v
    have hg : s⁻¹ * (s * γ * s'⁻¹) * s' = γ := by group
    have h4 := HermitianSumRootCoordinateFrames.ZhatNAct_holds _ _ (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
      (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (s v)) (uMat (s⁻¹ v)) (uMat (s' v))
      (uMat ((s * γ * s'⁻¹) v)) (P v) (P' v) (InfCut.uMat_inv_mul' (s v)) (hJ_map _ (s v).2) (hsP v) (hs'P v)
    have hγv : uMat (s⁻¹ v) * uMat ((s * γ * s'⁻¹) v) * uMat (s' v) = uMat (γ v) := by
      calc uMat (s⁻¹ v) * uMat ((s * γ * s'⁻¹) v) * uMat (s' v)
          = uMat ((s⁻¹ * (s * γ * s'⁻¹) * s') v) := by
            simp only [uMat, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]
        _ = uMat (γ v) := by rw [hg]
    rw [hγv, ← zx_eq, ← zx_eq] at h4
    have h5 : ZhatO (ZX X u u' 1 γ v) = (L * ptMat w * U).map (ψ v) := hZ v
    rw [Matrix.map_mul, Matrix.map_mul, zhatO_eq, h4] at h5
    have hPs : (P v).map star = L.map (ψ v) := by
      ext i j
      simp only [P, Matrix.map_apply, star_star]
    have hPt' : (P' v)ᵀ = sgn D.R.rS * U.map (ψ v) * sgn D.R.rS := Matrix.transpose_transpose _
    rw [hPs, hPt'] at h5
    have h6 : L.map (ψ v) * ZhatO (ZX X u u' 1 (s * γ * s'⁻¹) v) * U.map (ψ v) =
        L.map (ψ v) * ptC X v w * U.map (ψ v) := by
      refine Eq.trans ?_ h5
      rw [zhatO_eq]
      simp only [Matrix.mul_assoc, sgn_sq, Matrix.mul_one]
    exact cancel (by rw [det_lo (isLoUni_map _ hLo)]; exact one_ne_zero)
      (by rw [det_up (isUpUni_map _ hUp)]; exact one_ne_zero) h6
  exact ⟨_, hPt⟩

end Formalism.L2.SG.RealObj.RealPointRepresentatives
end
end

section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.EnergyIntOm

variable {D : D7} (X : HidaSetting D)

def dsc (lam : ℂ) (sc : ℝ) (a : Fin (D.R.rS + 1)) : ℂ := (lam * (sc : ℂ)) ^ (D.R.rS - a.val)

theorem dsc_ne {lam : ℂ} (hl : lam ≠ 0) {sc : ℝ} (hsc : sc ≠ 0) (a : Fin (D.R.rS + 1)) : dsc (D := D) lam sc a ≠ 0 := by
  unfold dsc
  exact pow_ne_zero _ (mul_ne_zero hl (by exact_mod_cast hsc))

theorem dsc_last (lam : ℂ) (sc : ℝ) : dsc (D := D) lam sc (Fin.last D.R.rS) = 1 := by
  unfold dsc
  simp

theorem q_fvec {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : sc ≠ 0) (u : D.what₂.Word) (a : Fin (D.R.rS + 1)) :
    Q *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) a = dsc (D := D) lam sc a • frm X u sc v a := by
  obtain ⟨-, h2, -, h4⟩ := hQ
  have hsc' : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc
  induction a using Fin.lastCases with
  | last =>
    have hl : ¬ (Fin.last D.R.rS).val < D.R.rS := by simp
    unfold Formalism.QuantumDeterminants.fvec
    rw [dite_eq_right hl, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, dsc_last, one_smul]
    unfold frm famSc fam
    simp [Fin.snoc_last]
  | cast b =>
    have hb : (Fin.castSucc b).val < D.R.rS := b.isLt
    unfold Formalism.QuantumDeterminants.fvec Formalism.QuantumDeterminants.bvec
    rw [dite_eq_left hb]
    have hbb : (⟨(Fin.castSucc b).val, hb⟩ : Fin D.R.rS) = b := Fin.ext rfl
    rw [hbb, (h4 b b rfl).1]
    unfold dsc frm famSc fam
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc]
    rw [smul_smul, mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hsc'), mul_one]

theorem zhat_tr {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : sc ≠ 0) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) (trG Q Qi (γ v)) a b =
      star (dsc (D := D) lam sc a) * dsc (D := D) lam sc b * ZX X u u' sc γ v a b := by
  obtain ⟨-, h2, h3, -⟩ := id hQ
  have ea := q_fvec X hQ hsc u a
  have eb := q_fvec X hQ hsc u' b
  unfold ZX Formalism.QuantumDeterminants.Zhat trG
  unfold Formalism.L2.SG.RealObj.Zhat
  beta_reduce
  unfold Formalism.QuantumDeterminants.herm Formalism.L2.SG.HidaSetting.hJ
  rw [← h3]
  have hm : Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q * (Qi * uMat (γ v) * Q) =
      Qᴴ * (Formalism.REAL.Jm (X.B.I.ε v) * (uMat (γ v) * Q)) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ea,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, star_smul, smul_eq_mul]
  ring

theorem dmin_diag (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
    (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) (d : Fin (D.R.rS + 1) → ℂ)
    (h : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' g = Matrix.diagonal d) (l : Fin (D.R.rS + 2)) :
    Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' g l = ∏ i : Fin l.val, d (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) := by
  unfold Formalism.QuantumDeterminants.Dmin
  rw [h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  rfl

theorem mem_om {v : InfinitePlace X.B.I.F} {lam : ℂ} (hl : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : 0 < sc) (u u' : D.what₂.Word) (c : Cinf X) (hc : c ∈ Good X u u') (γ : X.B.I.Ginf)
    (hγ : HasDiag X u u' sc c γ) :
    trG Q Qi (γ v) ∈ Formalism.FourierDecayAlt.JF.Om D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) := by
  have hsc0 : sc ≠ 0 := hsc.ne'
  have hc' : ∀ w, (∀ l, c w l ≠ 0) ∧ 0 < Gv (Tw u) (Tw u') (Matrix.diagonal (c w)) := hc
  have hγ' : ∀ w, ZX X u u' sc γ w = Matrix.diagonal (c w) := hγ
  obtain ⟨dd, hdd⟩ : ∃ dd : Fin (D.R.rS + 1) → ℂ,
      dd = fun a => star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a * c v a := ⟨_, rfl⟩
  have hdiag : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
      (trG Q Qi (γ v)) = Matrix.diagonal dd := by
    ext a b
    rw [zhat_tr X hQ hsc0 u u' γ a b, hγ' v, hdd]
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hab]
  have hdsc : ∀ a, star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a ≠ 0 := fun a =>
    mul_ne_zero (star_ne_zero.mpr (dsc_ne (D := D) hl hsc0 a)) (dsc_ne (D := D) hl hsc0 a)
  have hd0 : ∀ a, dd a ≠ 0 := by
    intro a
    rw [hdd]
    exact mul_ne_zero (hdsc a) ((hc' v).1 a)
  have hDmin := fun l => dmin_diag (D := D) _ _ _ _ hdiag l
  have hTz : ∀ w : D.what₂.Word, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR w)) = Tw w := by
    intro w
    have hQz : Q *ᵥ (Qi *ᵥ rv X.B.I v (X.zR w)) = rv X.B.I v (X.zR w) := by
      rw [Matrix.mulVec_mulVec, hQ.2.1, Matrix.one_mulVec]
    have hJ := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v w
    unfold Formalism.L2.SG.HidaSetting.hJ at hJ
    unfold Formalism.QuantumDeterminants.Tz Formalism.QuantumDeterminants.herm
    rw [← hQ.2.2.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Formalism.L2.SG.Pf.LTL.star_dot_conjT, hQz, hJ]
    simp
  unfold Formalism.FourierDecayAlt.JF.Om
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem Q Qi _ hQ.2.1 hQ.2.2.1 (γ v), ?_⟩
  rw [Formalism.FourierDecayAlt.Q.OmPlus, Set.mem_ofPred_eq]
  refine ⟨fun l _ => ?_, ?_⟩
  · rw [hDmin l]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
  · have hlast : Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
        (trG Q Qi (γ v)) (Fin.last (D.R.rS + 1)) =
        (∏ i : Fin D.R.rS, dd (Fin.castSucc i)) * dd (Fin.last D.R.rS) := by
      rw [hDmin]
      have h : ∏ i : Fin (D.R.rS + 1), dd i =
          (∏ i : Fin D.R.rS, dd (Fin.castSucc i)) * dd (Fin.last D.R.rS) := Fin.prod_univ_castSucc _
      exact h
    have hr : Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
        (trG Q Qi (γ v)) ⟨D.R.rS, by omega⟩ = ∏ i : Fin D.R.rS, dd (Fin.castSucc i) := by
      rw [hDmin]
      rfl
    have hsplit : ∏ i : Fin D.R.rS, dd (Fin.castSucc i) =
        (∏ i : Fin D.R.rS, star (dsc (D := D) lam sc (Fin.castSucc i)) * dsc (D := D) lam sc (Fin.castSucc i)) *
          ∏ i : Fin D.R.rS, c v (Fin.castSucc i) := by
      rw [hdd, ← Finset.prod_mul_distrib]
    have hlastd : dd (Fin.last D.R.rS) = c v (Fin.last D.R.rS) := by
      rw [hdd]
      simp [dsc_last]
    have hG := (hc' v).2
    unfold Gv at hG
    rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.dl_diag_last, Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.dl_diag_r,
      Complex.sq_norm, Complex.sq_norm] at hG
    have hE : 0 < Complex.normSq
        (∏ i : Fin D.R.rS, star (dsc (D := D) lam sc (Fin.castSucc i)) * dsc (D := D) lam sc (Fin.castSucc i)) :=
      Complex.normSq_pos.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hdsc _)
    unfold Formalism.QuantumDeterminants.Gf
    rw [hlast, hr, hTz u, hTz u', hsplit, hlastd]
    simp only [Complex.normSq_mul] at hG ⊢
    nlinarith [mul_pos hE hG]

end Formalism.L2.SG.RealObj.EnergyIntOm
end
end
