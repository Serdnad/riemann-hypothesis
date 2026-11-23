module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartLaw
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSH
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.Pv.HaarSubS

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.WFL

theorem isFolner_Sinf_gen {n r k : ℕ} (hn : n = 2 * r + k + 1) {ι : Type} [Fintype ι] {εv : ι → Fin n → Bool}
    (ev fv : ι → Fin r → Fin n → ℂ) (wv : ι → Fin k → Fin n → ℂ) (zv : ι → Fin n → ℂ) (T : ι → ℝ)
    (hT : ∀ v, 0 < T v)
    (hee : ∀ v a b, hJ (εv v) (ev v a) (ev v b) = 0) (hff : ∀ v a b, hJ (εv v) (fv v a) (fv v b) = 0)
    (hef : ∀ v a b, hJ (εv v) (ev v a) (fv v b) = if a = b then 1 else 0)
    (hez : ∀ v a, hJ (εv v) (ev v a) (z0v (T v) (zv v)) = 0)
    (hfz : ∀ v a, hJ (εv v) (fv v a) (z0v (T v) (zv v)) = 0)
    (hzz : ∀ v, hJ (εv v) (z0v (T v) (zv v)) (z0v (T v) (zv v)) = -1)
    (hww : ∀ v a b, hJ (εv v) (wv v a) (wv v b) = if a = b then 1 else 0)
    (hew : ∀ v c a, hJ (εv v) (ev v c) (wv v a) = 0) (hfw : ∀ v c a, hJ (εv v) (fv v c) (wv v a) = 0)
    (hzw : ∀ v a, hJ (εv v) (z0v (T v) (zv v)) (wv v a) = 0)
    (μS : Measure (∀ v, Formalism.REAL.UJ (εv v)))
    (hμ : IsHaarSub {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS) :
    IsFolner {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS := by
  subst hn
  exact Formalism.L2.S.Pv.FolnerJ.isFolner_Sinf ev fv wv zv T hT
    (fun v => ⟨hee v, hff v, hef v, hez v, hfz v, hzz v, hww v, hew v, hfw v, hzw v⟩) μS hμ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermitian_scaled_right {n : ℕ} (ε : Fin n → Bool) (T : ℝ) (x z : Fin n → ℂ) :
    hJ ε x (z0v T z) = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * hJ ε x z := by
  unfold z0v hJ
  simp [Matrix.mulVec_smul, dotProduct_smul]

theorem hermitian_scaled_left {n : ℕ} (ε : Fin n → Bool) (T : ℝ) (x z : Fin n → ℂ) :
    hJ ε (z0v T z) x = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * hJ ε z x := by
  unfold z0v hJ
  simp [Matrix.mulVec_smul, smul_dotProduct, star_smul]

theorem folner_of_haar {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (hμ : IsHaarSub (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u)) :
    IsFolner (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u) := by
  have hn : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := X.n_eq.trans (dimS_eq D.R).symm
  have hT : 0 < Tw (D := D) u := ProductExactness.Tw_pos u
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  refine isFolner_Sinf_gen hn (fun v a => rv X.B.I v (X.eR a)) (fun v a => rv X.B.I v (X.fR a))
    (fun v => X.wfr u v) (fun v => rv X.B.I v (X.zR u)) (fun _ => Tw u) (fun _ => hT) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (Formalism.L2.SG.RealObj.muS X u) hμ
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ee]; simp)
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ff]; simp)
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  · intro v a
    rw [hermitian_scaled_right]
    have : hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
    rw [this, mul_zero]
  · intro v a
    rw [hermitian_scaled_right]
    have : hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).2]; simp)
    rw [this, mul_zero]
  · intro v
    rw [hermitian_scaled_right, hermitian_scaled_left]
    have h5 : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(Tw (D := D) u : ℂ) :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
    rw [h5]
    have hs : ((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) * (Real.sqrt (Tw (D := D) u))⁻¹ * Tw (D := D) u = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
    have : (((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) : ℂ) * ((((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) : ℂ) *
        -((Tw (D := D) u : ℝ) : ℂ)) = -(((Real.sqrt (Tw (D := D) u))⁻¹ * (Real.sqrt (Tw (D := D) u))⁻¹ *
          Tw (D := D) u : ℝ) : ℂ) := by push_cast; ring
    rw [this, hs]
    simp
  · intro v a b
    exact X.wfr_on u v a b
  · intro v c a
    exact ((X.wfr_perp u v a).1 c).1
  · intro v c a
    exact ((X.wfr_perp u v a).1 c).2
  · intro v a
    rw [hermitian_scaled_left]
    have h0 : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := (X.wfr_perp u v a).2
    rw [h0, mul_zero]

theorem stepSubG_of_MN (hN : MeasN) (hQ : NuQSFinite) : Formalism.L2.SG.RealObj.EnergyInst.StepSubG := by
  exact stepSubG_of sDecomp_holds hN (measH_of sDecomp_holds)
    (fun D X u => folner_of_haar X u (isHaarSub_SinfU sDecomp_holds hN (measH_of sDecomp_holds) X u)) hQ

end Formalism.L2.S.Pv.HaarSubS
end
end

section

noncomputable section

open scoped Matrix
open Finset NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.S.Pv.Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hJ_conj {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

theorem blkOf_mono {K : Type*} : ∀ (l : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf l i ≤ blkOf l j
  | [], _, _, _ => le_rfl
  | (x, s) :: bs, i, j, h => by
    unfold blkOf
    by_cases hi : i < s
    · rw [if_pos hi]; exact Nat.zero_le _
    · have hj : ¬ j < s := fun hj => hi (lt_of_le_of_lt h hj)
      rw [if_neg hi, if_neg hj]
      exact Nat.succ_le_succ (blkOf_mono bs (i - s) (j - s) (Nat.sub_le_sub_right h s))

variable {D : D7} {w : Point D.host.E (D.R.rS + 1)}

theorem blk_mid (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) :
    blkOf w.1 p.1.1.1 = blkOf w.1 c.1 ∧ blkOf w.1 c.1 = blkOf w.1 p.1.2.1 := by
  have h1 := blkOf_mono w.1 p.1.1.1 c.1 (le_of_lt h.1)
  have h2 := blkOf_mono w.1 c.1 p.1.2.1 (le_of_lt h.2)
  have h3 := p.2.2
  omega

def midL (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) : FreeE w :=
  ⟨(p.1.1, c), h.1, (blk_mid p c h).1⟩

def midR (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) : FreeE w :=
  ⟨(c, p.1.2), h.2, (blk_mid p c h).2⟩

def BX (p : FreeE w) (x y : FreeE w → ℂ) : ℂ :=
  ∑ c : Fin (D.R.rS + 1), if h : p.1.1 < c ∧ c < p.1.2 then x (midL p c h) * y (midR p c h) else 0

theorem BX_zero (p : FreeE w) (x : FreeE w → ℂ) : BX p x 0 = 0 := by
  unfold BX; simp

theorem BX_lower (p : FreeE w) (x x' y y' : FreeE w → ℂ)
    (h : ∀ q : FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q ∧ y q = y' q) :
    BX p x y = BX p x' y' := by
  unfold BX
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · have h1 := h (midL p c hc) (by
      simp only [midL]; have := hc.1; have := hc.2
      have : c.val < p.1.2.val := hc.2
      have : p.1.1.val < c.val := hc.1
      omega)
    have h2 := h (midR p c hc) (by
      simp only [midR]
      have : c.val < p.1.2.val := hc.2
      have : p.1.1.val < c.val := hc.1
      omega)
    rw [h1.1, h2.2]
  · rfl

theorem BX_measurable (p : FreeE w) : Measurable (fun z : (FreeE w → ℂ) × (FreeE w → ℂ) => BX p z.1 z.2) := by
  unfold BX
  refine Finset.measurable_sum _ fun c _ => ?_
  split_ifs with hc
  · exact ((measurable_pi_apply _).comp measurable_fst).mul ((measurable_pi_apply _).comp measurable_snd)
  · exact measurable_const

section Law

variable (X : HidaSetting D) (v : InfinitePlace X.B.I.F)

theorem dual_v (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if a = b then 1 else 0 := by
  rw [hJ_conj, show X.eR b = X.crd (X.eX b) from rfl, show X.fR a = X.crd (X.fY a) from rfl,
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ef]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, map_zero, star_zero]

theorem fz_v (u' : D.what₂.Word) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u')) = 0 := by
  rw [show X.zR u' = X.crd (X.zu u') from rfl, show X.fR a = X.crd (X.fY a) from rfl,
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u' a).2, map_zero]

theorem ha_free (q : FreeE w) : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega

theorem stCoordV_coef (u' : D.what₂.Word) (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε v)) (q : FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v y q =
      (D.host.rdE : ℂ) ^ (D.R.rS - q.1.1.1) * ((D.host.rdE : ℂ) ^ (D.R.rS - q.1.2.1))⁻¹ *
        hJ (X.B.I.ε v) (rv X.B.I v (X.fR ⟨q.1.1.1, ha_free q⟩))
          (uMat ((γ v)⁻¹ * y * γ v) *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) q.1.2) := by
  unfold Formalism.L2.SG.NGPin.stCoordV frm famSc
  rw [Matrix.mulVec_smul, hJ_smul]
  ring

theorem stCoordV_mul {u u' : D.what₂.Word} {γ : X.B.I.Ginf} {y₁ y₂ : Formalism.REAL.UJ (X.B.I.ε v)}
    (h₁ : y₁ ∈ Formalism.L2.SG.NGPin.StV X u u' γ v) (h₂ : y₂ ∈ Formalism.L2.SG.NGPin.StV X u u' γ v) (p : FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v (y₁ * y₂) p =
      Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₁ p + Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₂ p +
        BX p (Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₁) (Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₂) := by
  have hdual := dual_v X v
  have hfz := fz_v X v u'
  have hS₁ : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat ((γ v)⁻¹ * y₁ * γ v)) := h₁.2.1
  have hS₂ : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat ((γ v)⁻¹ * y₂ * γ v)) := h₂.2.1
  have hmul : uMat ((γ v)⁻¹ * (y₁ * y₂) * γ v) = uMat ((γ v)⁻¹ * y₁ * γ v) * uMat ((γ v)⁻¹ * y₂ * γ v) := by
    rw [show (γ v)⁻¹ * (y₁ * y₂) * γ v = ((γ v)⁻¹ * y₁ * γ v) * ((γ v)⁻¹ * y₂ * γ v) by group]; rfl
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have := Formalism.MainNotions.S.Pv.HH.one_le_rdE D
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one this))
  have hab : (⟨p.1.1.1, ha_free p⟩ : Fin D.R.rS).1 < p.1.2.1 := p.2.1
  unfold BX
  simp only [stCoordV_coef X v u' γ]
  rw [hmul, coef_mul (X.B.I.ε v) _ _ _ hdual hfz hS₁ hS₂ ⟨p.1.1.1, ha_free p⟩ p.1.2 hab,
    Fin.sum_univ_castSucc, dite_eq_right (fun h => (not_lt.2 (Fin.le_last _)) h.2), add_zero]
  rw [mul_add, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : p.1.1 < c.castSucc ∧ c.castSucc < p.1.2
  · rw [dite_eq_left hc, if_pos ⟨hc.1, hc.2⟩]
    simp only [midL, midR]
    have e1 : fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) c.castSucc = rv X.B.I v (X.eR c) := by
      unfold fam; rw [Fin.snoc_castSucc]
    rw [e1]
    simp only [Fin.val_castSucc, Fin.eta]
    have hpow : (D.host.rdE : ℂ) ^ (D.R.rS - c.castSucc.1) ≠ 0 := pow_ne_zero _ hrd
    field_simp
  · rw [dite_eq_right hc, if_neg (fun h => hc ⟨h.1, h.2⟩), mul_zero]

end Law

end Formalism.L2.S.Pv.Chart

end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ}
  {w w' : Fin k → Fin n → ℂ} {sc T T' : ℝ}

def Mv (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (w w' : Fin k → Fin n → ℂ)
    (sc T T' : ℝ) (i0 : Fin k) (c : Fin (r + 1) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fr2M ε e f z' w' (e2 sc c f) (p2 sc c e) (z2 T T' c z w i0) (w2 T T' c z w i0) T'

theorem famSc_castSucc (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (b : Fin r) :
    famSc sc e z (Fin.castSucc b) = sfv sc b • e b := by
  simp only [famSc, fam, Fin.snoc_castSucc, Fin.coe_castSucc, sfv]

theorem famSc_last (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc sc e z (Fin.last r) = z := by
  simp only [famSc, fam, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]

theorem zhat_Mv (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hsc : 0 < sc) {c : Fin (r + 1) → ℂ} (i0 : Fin k) :
    Zhat ε (famSc sc e z) (famSc sc e z') (Mv ε e f z z' w w' sc T T' i0 c) = Matrix.diagonal c := by
  have hMe : ∀ b, Mv ε e f z z' w w' sc T T' i0 c *ᵥ e b = e2 sc c f b := fun b => frameChangeMatrix_isotropic F1 b
  have hMz : Mv ε e f z z' w w' sc T T' i0 c *ᵥ z' = z2 T T' c z w i0 := fr2M_mulVec_z F1
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 F0.T_ne
  have hfe : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0 := F0.ep
  ext a b
  simp only [Zhat]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last =>
      rw [famSc_last, famSc_last, hMz]
      simp only [z2, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.zz, F0.zw, mul_zero, add_zero, diagonal_apply_eq,
        alv]
      field_simp
    | cast b =>
      rw [famSc_last, famSc_castSucc, mulVec_smul, hMe]
      simp only [e2, UnitaryIsometries.hJ_smul_right, hJ_swap0 (F0.pz b), mul_zero]
      rw [diagonal_apply_ne]
      exact fun h => (Fin.castSucc_lt_last b).ne h.symm
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [famSc_castSucc, famSc_last, hMz]
      simp only [z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.ez, F0.ew, mul_zero,
        add_zero]
      rw [diagonal_apply_ne]
      exact (Fin.castSucc_lt_last a).ne
    | cast b =>
      rw [famSc_castSucc, famSc_castSucc, mulVec_smul, hMe]
      simp only [e2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hfe, conj_sfv]
      by_cases h : a = b
      · subst h
        rw [diagonal_apply_eq, if_pos rfl, lamv]
        have hs : sfv sc a ≠ 0 := sfv_ne hsc a
        field_simp
      · rw [if_neg h, diagonal_apply_ne _ (fun h' => h (Fin.castSucc_injective _ h'))]
        ring

theorem measurable_Mv (i0 : Fin k) :
    Measurable (fun c : Fin (r + 1) → ℂ => Mv ε e f z z' w w' sc T T' i0 c) := by
  have hlam : ∀ a, Measurable (fun c : Fin (r + 1) → ℂ => lamv sc c a) := fun a =>
    (measurable_pi_apply _).div_const _
  have hinv : ∀ a, Measurable (fun c : Fin (r + 1) → ℂ => (conj (lamv sc c a))⁻¹) := fun a =>
    (Complex.continuous_conj.measurable.comp (hlam a)).inv
  have hal : Measurable (fun c : Fin (r + 1) → ℂ => alv T c) := (measurable_pi_apply _).neg.div_const _
  have hbe : Measurable (fun c : Fin (r + 1) → ℂ => bev T T' c) := by
    unfold bev
    exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      ((((measurable_pi_apply _).norm.pow_const 2).div_const _).sub_const _))
  have hcal : Measurable (fun c : Fin (r + 1) → ℂ => conj (alv T c)) := Complex.continuous_conj.measurable.comp hal
  have hOf : Measurable (Matrix.of : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ) := by
    letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩
    exact (continuous_matrixOf.mpr continuous_id).measurable
  refine hOf.comp ?_
  refine Measurable.of_eval (f := fun c : Fin (r + 1) → ℂ => fun (i j : Fin n) =>
    Mv ε e f z z' w w' sc T T' i0 c i j) fun i => Measurable.of_eval fun j => ?_
  simp only [Mv, frameChangeMatrix_entry, syn, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ((Finset.measurable_sum _ fun a _ => ?_).add (Finset.measurable_sum _ fun a _ => ?_)).add ?_ |>.add
    (Finset.measurable_sum _ fun l _ => ?_)
  · simp only [e2, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hlam a).mul measurable_const)
  · simp only [p2, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hinv a).mul measurable_const)
  · simp only [z2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hal.mul measurable_const).add (hbe.mul measurable_const))
  · simp only [w2]
    by_cases hl : l = i0
    · simp only [if_pos hl, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      exact measurable_const.mul (measurable_const.mul ((hbe.mul measurable_const).add
        ((hcal.mul measurable_const).mul measurable_const)))
    · simp only [if_neg hl]
      exact measurable_const

instance matrix_borel (m : ℕ) : BorelSpace (Matrix (Fin m) (Fin m) ℂ) :=
  ⟨rfl⟩

theorem measurableEmbedding_uMat (ε : Fin n → Bool) :
    MeasurableEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.measurableEmbedding

def secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T) (hT' : 0 < T')
    (hsc : 0 < sc) (i0 : Fin k) (c : Fin (r + 1) → ℂ) : Formalism.REAL.UJ ε :=
  if h : (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then
    UnitaryIsometries.toUJ ε (frameChangeMatrix_isometry F1 (frm2 (sc := sc) F0 hT hT' hsc h.1 h.2 i0) hdim)
  else 1

theorem uMat_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T)
    (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) (c : Fin (r + 1) → ℂ) :
    Formalism.MainNotions.S.uMat (secV F0 F1 hdim hT hT' hsc i0 c) =
      if (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then Mv ε e f z z' w w' sc T T' i0 c else 1 := by
  unfold secV
  split_ifs with h
  · rfl
  · simp [Formalism.MainNotions.S.uMat]

theorem measurable_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k)
    (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) :
    Measurable (secV F0 F1 hdim hT hT' hsc i0) := by
  rw [← (measurableEmbedding_uMat ε).measurable_comp_iff]
  have he : (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) ∘ secV F0 F1 hdim hT hT' hsc i0 =
      fun c => if (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then Mv ε e f z z' w w' sc T T' i0 c
        else 1 := by
    funext c
    exact uMat_secV F0 F1 hdim hT hT' hsc i0 c
  rw [he]
  have hm1 : MeasurableSet {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun l => (measurableSet_singleton 0).compl.preimage (measurable_pi_apply l)
  have hm2 : MeasurableSet {c : Fin (r + 1) → ℂ | 0 < ‖c (Fin.last r)‖ ^ 2 - T * T'} :=
    measurableSet_lt measurable_const ((((measurable_pi_apply _).norm.pow_const 2)).sub_const _)
  have hm : MeasurableSet {c : Fin (r + 1) → ℂ | (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T'} :=
    hm1.inter hm2
  exact Measurable.ite hm (measurable_Mv i0) measurable_const

theorem zhat_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T)
    (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) {c : Fin (r + 1) → ℂ} (hc : ∀ l, c l ≠ 0)
    (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') :
    Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat (secV F0 F1 hdim hT hT' hsc i0 c)) =
      Matrix.diagonal c := by
  rw [uMat_secV, if_pos ⟨hc, hg⟩]
  exact zhat_Mv F0 F1 hsc i0

end Formalism.L2.S.Pv.SecW
end
end
