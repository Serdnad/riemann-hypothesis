module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaFIntMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle037
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocalCountZeroLocalHolds
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.Bundle001

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Helpers

variable {K : Type*} [CommRing K] {n : ℕ}

theorem isUp_sconj {S X : Matrix (Fin n) (Fin n) K} (s d d' : Fin n → K) (hS : S = Matrix.diagonal s)
    (hs : ∀ a, s a * s a = 1) (hd : ∀ a, d a * d' a = 1) (hX : IsUp X) :
    IsUp (S * Matrix.diagonal d * X * Matrix.diagonal d' * S) := by
  have e : S * Matrix.diagonal d * X * Matrix.diagonal d' * S =
      Matrix.diagonal (fun a => s a * d a) * X * Matrix.diagonal (fun a => d' a * s a) := by
    rw [hS, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc _ (Matrix.diagonal d'), Matrix.diagonal_mul_diagonal]
  rw [e]
  exact isUp_conj hX _ _ fun a => by
    calc s a * d a * (d' a * s a) = (d a * d' a) * (s a * s a) := by ring
      _ = 1 := by rw [hd, hs, one_mul]

theorem isLo_sconj {S X : Matrix (Fin n) (Fin n) K} (s d d' : Fin n → K) (hS : S = Matrix.diagonal s)
    (hs : ∀ a, s a * s a = 1) (hd : ∀ a, d a * d' a = 1) (hX : IsLo X) :
    IsLo (S * Matrix.diagonal d * X * Matrix.diagonal d' * S) := by
  have e : S * Matrix.diagonal d * X * Matrix.diagonal d' * S =
      Matrix.diagonal (fun a => s a * d a) * X * Matrix.diagonal (fun a => d' a * s a) := by
    rw [hS, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc _ (Matrix.diagonal d'), Matrix.diagonal_mul_diagonal]
  rw [e]
  exact isLo_conj hX _ _ fun a => by
    calc s a * d a * (d' a * s a) = (d a * d' a) * (s a * s a) := by ring
      _ = 1 := by rw [hd, hs, one_mul]

theorem isLo_one' {K : Type*} [CommRing K] {n : ℕ} : IsLo (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne]⟩

theorem isUp_one' {K : Type*} [CommRing K] {n : ℕ} : IsUp (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩

end Helpers

section ClearFp

variable {D : Formalism.BasicNotions.D7}

theorem clear_Fp (p : PlF D) {ι : Type} [Fintype ι] (z : ι → (D.s.atP p).Fp) :
    ∃ c : 𝓞 D.host.F, c ≠ 0 ∧ ∀ k,
      (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c) * z k ∈ (haveI := (D.s.atP p).lf; 𝒪[(D.s.atP p).Fp]) := by
  haveI := (D.s.atP p).lf
  have h := fun k => clear_F (fun q => D.s.atP q) p (z k)
  choose t ht0 htz using h
  refine ⟨∏ k, t k, Finset.prod_ne_zero_iff.2 fun k _ => ht0 k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), map_mul, map_mul,
    mul_comm ((D.s.atP p).ιF (algebraMap _ _ (t k))), mul_assoc]
  exact Subring.mul_mem _ (iotaF_int_mem (fun q => D.s.atP q) p _) (htz k)

end ClearFp

section TypedFact

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)
  (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
  (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Zd.M p).L) (hM : (Zd.M p).split = some g)
  (hge : g.e = sg.e) (hgq : g.q = sg.q)
include hR hM hge hgq



theorem zz_fact (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {L B : PairVal.MatR D} (hL : IsLo L)
    (hB : IsUp B) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) * LsDatumB.sgnP p =
      glue sg.e (Matrix.diagonal (cf Zd p) * L.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))
          (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p)) *
        glue sg.e ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
            (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
              (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS)
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
            (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
              ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS) *
        glue sg.e (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))
          (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) := by
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  set S := Sg (D.s.atP p).Fp D.R.rS with hS
  have hZ : (L * ptMat w * B * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w * B := by
    rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  have hΛ1 : IsLo (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) :=
    isLo_conj (isLo_map φ1 hL) _ _ (cf_cfi Zd p)
  have hV1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map φ1 * Matrix.diagonal (cf Zd p)) :=
    isUp_conj (isUp_map φ1 hB) _ _ (cfi_cf Zd p)
  have hBt : IsLo (S * (B.map φ2).transpose * S) :=
    isLo_conj (isLo_transpose (isUp_map φ2 hB)) _ _ (fun a => sgn_sq' D.R.rS a)
  have hLt : IsUp (S * (L.map φ2).transpose * S) :=
    isUp_conj (isUp_transpose (isLo_map φ2 hL)) _ _ (fun a => sgn_sq' D.R.rS a)
  have hΛ2 : IsLo (Matrix.diagonal (cf Zd p) * (S * (B.map φ2).transpose * S) * Matrix.diagonal (cfi Zd p)) :=
    isLo_conj hBt _ _ (cf_cfi Zd p)
  have hV2 : IsUp (Matrix.diagonal (cfi Zd p) * (S * (L.map φ2).transpose * S) * Matrix.diagonal (cf Zd p)) :=
    isUp_conj hLt _ _ (cfi_cf Zd p)
  refine mat_eq sg.e ?_ ?_
  · have l1 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) *
        LsDatumB.sgnP p).map (p1 sg.e) =
        (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) *
          ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map φ1 * Matrix.diagonal (cf Zd p))) *
          (Matrix.diagonal (cfi Zd p) * B.map φ1 * Matrix.diagonal (cf Zd p)) -
        (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
      rw [zz1' Zd p sg hR g hM hge hgq, hZ, Matrix.map_mul, Matrix.map_mul, fact1 _ _ (cfi_cf Zd p)]
    rw [l1, Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, glue_map_fst, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hΛ1 hV1]
  · have e2 : ((L * ptMat w * B * Sg D.host.E D.R.rS).map φ2).transpose * S =
        (S * (B.map φ2).transpose * S) * (S * (ptMat w).map φ2 * S) * (S * (L.map φ2).transpose * S) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
      exact fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])
    have l2 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) *
        LsDatumB.sgnP p).map (p2 sg.e) =
        (Matrix.diagonal (cf Zd p) * (S * (B.map φ2).transpose * S) * Matrix.diagonal (cfi Zd p)) *
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (S * (ptMat w).map φ2 * S) *
            Matrix.diagonal (cf Zd p))) *
          (Matrix.diagonal (cfi Zd p) * (S * (L.map φ2).transpose * S) * Matrix.diagonal (cf Zd p)) -
        ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
      rw [zz2' Zd p sg hR g hM hge hgq, e2, fact1 _ _ (cfi_cf Zd p)]
    rw [l2, Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, glue_map_snd, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hΛ2 hV2]



theorem target_fact (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) :
    ∃ Gl Gu : MatP D p, IsLo Gl ∧ IsUp Gu ∧
      glue sg.e ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
            (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
              (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS)
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
            (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
              ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS) =
        Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0 :=
    fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  obtain ⟨L1, U1, hL1, hU1, h1⟩ := generic_comp (sgF w) (sgF_sgF _) (isLo_one' (K := (D.s.atP p).Fp))
    (isUp_one' (K := (D.s.atP p).Fp))
    (W := (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE))
    (fun a b hb => by simp only [Matrix.map_apply, ptMat_apply', if_neg hb, map_zero])
    (fun a => by
      simp only [Matrix.map_apply, ptMat_apply', if_true]
      exact (map_ne_zero _).2 (pTau_ne' _ a))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (sg.q : (D.s.atP p).Fp)⁻¹ (inv_ne_zero hq)
    (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  obtain ⟨L2, U2, hL2, hU2, h2⟩ := generic_comp (sgF w) (sgF_sgF _) (isLo_one' (K := (D.s.atP p).Fp))
    (isUp_one' (K := (D.s.atP p).Fp))
    (W := Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS)
    (fun a b hb => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb, map_zero,
        mul_zero, zero_mul])
    (fun a => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true]
      exact mul_ne_zero (mul_ne_zero (hs0 _) ((map_ne_zero _).2 (pTau_ne' _ a))) (hs0 _))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (-(sg.q : (D.s.atP p).Fp)⁻¹) (neg_ne_zero.2 (inv_ne_zero hq))
    ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  rw [Matrix.one_mul, Matrix.mul_one] at h1 h2
  refine ⟨glue sg.e L1 L2, glue sg.e U1 U2, isLo_glue sg.e hL1 hL2, isUp_glue sg.e hU1 hU2, mat_eq sg.e ?_ ?_⟩
  · rw [glue_map_fst, h1, Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, mm1' Zd p sg hR g hM hge hgq]
  · rw [glue_map_snd, h2, Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, mm2' Zd p sg hR g hM hge hgq]

end TypedFact

end Formalism.L2.SG.Pf.PCountEx
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def locL (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) * A.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a))
  | some g => glue g.e (Matrix.diagonal (cf Zd p) * A.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))
      (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p))

def locR (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) * B.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))
  | some g => glue g.e (Matrix.diagonal (cfi Zd p) * B.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))
      (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p))

theorem tr_lem {K : Type*} [CommRing K] {n : ℕ} (S L X B : Matrix (Fin n) (Fin n) K) (hS : S * S = 1)
    (hSt : S.transpose = S) :
    (L * (X * S) * B * S).transpose * S = (S * B.transpose * S) * (X.transpose * S) * (S * L.transpose * S) := by
  simp only [Matrix.transpose_mul, hSt, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S S, hS, Matrix.one_mul]

theorem corner_conj {K : Type*} [CommRing K] {r : ℕ} {L U Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hL : IsLo L)
    (hU : IsUp U) (c : K) : L * (Y - c • Ecorner r) * U = L * Y * U - c • Ecorner r := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU]

theorem locMove (u u' : D.what₂.Word) (p : PlF D) {Z₁ Z₂ A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B)
    (h : Z₂ * Sg D.host.E D.R.rS = A * (Z₁ * Sg D.host.E D.R.rS) * B) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p =
      locL Zd p A B * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A B := by
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  · set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)
    set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)
    have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
    rw [zzp_sgn_ord Zd u u' p hM Z₂, zzp_sgn_ord Zd u u' p hM Z₁, h, Matrix.map_mul, Matrix.map_mul,
      regroup fr fri hfr]
    simp only [locL, locR, hM]
    rfl
  · obtain ⟨hge, hgq⟩ := hAg
    have hcc : ∀ a, cf Zd p a * cfi Zd p a = 1 := cf_cfi Zd p
    have hcc' : ∀ a, cfi Zd p a * cf Zd p a = 1 := cfi_cf Zd p
    have hL1 : IsLo (Matrix.diagonal (cf Zd p) * A.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p)) :=
      isLo_conj (isLo_map _ hA) _ _ hcc
    have hU1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) :=
      isUp_conj (isUp_map _ hB) _ _ hcc'
    have hL2a : IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hU2a : IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hA)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hL2 := isLo_conj hL2a (cf Zd p) (cfi Zd p) hcc
    have hU2 := isUp_conj hU2a (cfi Zd p) (cf Zd p) hcc'
    have hZ2 : Z₂ = A * (Z₁ * Sg D.host.E D.R.rS) * B * Sg D.host.E D.R.rS := by
      rw [← h, Matrix.mul_assoc, sg_sq, Matrix.mul_one]
    simp only [locL, locR, hM, hge]
    apply mat_eq sg.e
    · have l1 := zz1' Zd p sg hR g hM hge hgq u u' Z₂
      have r1 := zz1' Zd p sg hR g hM hge hgq u u' Z₁
      have key1 : (A * (Z₁ * Sg D.host.E D.R.rS) * B).map ((p1 sg.e).comp (D.s.atP p).ιE) =
          A.map ((p1 sg.e).comp (D.s.atP p).ιE) * (Z₁ * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) *
            B.map ((p1 sg.e).comp (D.s.atP p).ιE) := by simp only [Matrix.map_mul]
      rw [h, key1, fact1 (cf Zd p) (cfi Zd p) hcc'] at l1
      refine l1.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, r1, corner_conj hL1 hU1]
    · have e2 : (Z₂.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS =
          (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            ((Z₁.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
        rw [hZ2, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
        exact tr_lem _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _)
      have l2 := zz2' Zd p sg hR g hM hge hgq u u' Z₂
      have r2 := zz2' Zd p sg hR g hM hge hgq u u' Z₁
      rw [e2, fact1 (cf Zd p) (cfi Zd p) hcc'] at l2
      refine l2.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, r2, corner_conj hL2 hU2]

end Formalism.L2.SG.Pf.TupGlob
end
end

section

noncomputable section

open scoped Classical Matrix

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeL

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem permSign_mul_self₂ : Formalism.L2.SG.LsDatumB.sgnP (D := D) p * Formalism.L2.SG.LsDatumB.sgnP p = 1 := by
  unfold Formalism.L2.SG.LsDatumB.sgnP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem sgn_conj_intUp {ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (hρ : (∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ (Z.M p).R) :
    (∀ a, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a a = 1) ∧
      (∀ a b, b < a → (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b = 0) ∧
      ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b ∈ (Z.M p).R := by
  have e : ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      ((-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val)) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
    intro a b
    simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
  · rw [e, hρ.1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [e, hρ.2.1 a b h]; simp
  · rw [e]
    refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
      (hρ.2.2 a b)) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

theorem modeL (hs : (Z.M p).split = none) (u u' : D.what₂.Word)
    (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hNU : ∀ a b, b < a → N a b = 0) (hNd : ∀ a, N a a = 1) (hMU : ∀ a b, b < a → M a b = 0)
    (hMd : ∀ a, M a a = 1)
    (hNb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c)
    (hMb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * M c b ∈ aaF D c) (hrel : Nᴴ * Z₂ = Z₁ * M) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Z.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Z.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * Formalism.L2.SG.LsDatumB.sgnP p) * ρ := by
  have hR : (Z.M p).R = (Z.M p).L.O := by
    unfold Formalism.MainNotions.S.Loc.Model.R
    rw [hs]
  have eZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p X = Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X := by
    intro X
    simp only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  obtain ⟨hN1, hN0, hNO⟩ := locU_int Z p N hNU hNd hNb
  obtain ⟨hM1, hM0, hMO⟩ := locU_int Z p M hMU hMd hMb
  set K := ((locU Z p N).map (Z.M p).L.cj)ᵀ with hKdef
  have hK := key_rel Z p N M Z₁ Z₂ hrel
  have hKlow : Formalism.MainNotions.S.TieN.IntLow (Z.M p) K := by
    refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]
    · rw [hR]
      simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply]
      exact PI.LocCntLat.GC.cj_mem_O _ (hNO b a)
  have hρ : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (locU Z p M) := ⟨hM1, hM0, fun a b => by rw [hR]; exact hMO a b⟩
  have hdet : IsUnit K.det := by
    have hb : K.BlockTriangular OrderDual.toDual := fun i j hij => hKlow.2.1 i j hij
    have hd : K.det = 1 := by
      rw [Matrix.det_of_lowerTriangular K hb]
      simp [hKlow.1]
    rw [hd]
    exact isUnit_one
  have hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M := by
    rw [Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hdet, Matrix.one_mul]
  refine ⟨K⁻¹, Formalism.L2.SG.LsDatumB.sgnP p * locU Z p M * Formalism.L2.SG.LsDatumB.sgnP p,
    Formalism.L2.SG.Pf.LocOrbCut.intLow_inv (Z.M p) hKlow, sgn_conj_intUp Z p hρ, ?_⟩
  rw [eZZ, eZZ, hY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]

end ModeL

end Formalism.L2.SG.Pf.FibQ
end
end

section

namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.L2.SG.TypedSets

theorem inColumnsAt_holds :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InColumnsAt X hb hK FdN FdN' u u' X0 L A :=
  massDataColumns_of' Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Closed.AdBridgeGF_holds
    Formalism.L2.SG.Closed.AdBridgeK_holds
    (fun X u hK => Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK))
    (fun X u hK => Formalism.L2.SG.Closed.ClassFin_holds X u hK)
    (fun I hb => ⟨Formalism.L2.SG.Pf.Meas.eFin I hb, fun _ => rfl⟩)
    (fun X => Formalism.L2.SG.Pf.level_subgroup_compact_open X)
    Formalism.L2.SG.Closed.AutKCompact_holds
    Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion
    (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)

end Formalism.L2.SG.Pf.MassDataX
end

section

namespace Formalism.L2.SG.LsDatumA

theorem modSide0L : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n false) :=
  Formalism.L2.SG.LocalCountModules.localCountZeroLocal_holds

theorem modSideUL : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n false) :=
  Formalism.L2.SG.LocalCountModules.localCountUnitLocal_holds

end Formalism.L2.SG.LsDatumA
end
