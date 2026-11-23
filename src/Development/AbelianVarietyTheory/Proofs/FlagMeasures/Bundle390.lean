module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BlkOfOfPtEntry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle349
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupLift
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle017
public import Formalism.PeriodIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle380
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.GramJoint
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle005
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle042
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.CovDict

open Formalism.L2.SG.Pf.VolPinAsm

section Gen

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {m : ℕ}

theorem sum_smul_sum (e : Fin m → V) (P Q : Matrix (Fin m) (Fin m) K) (b : Fin m) :
    ∑ a, P a b • ∑ c, Q c a • e c = ∑ c, (Q * P) c b • e c := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem fm_conj {e f : Fin m → V} (ψ τ : V ≃ₗ[K] V) {P B : Matrix (Fin m) (Fin m) K} (hP : IsUnit P.det)
    (hψ : ∀ b, ψ (e b) = ∑ a, P a b • f a) (hτ : FM f τ B) :
    FM e (fun y => ψ.symm (τ (ψ y))) (P⁻¹ * B * P) := by
  intro b
  have hτ' : ∀ a, τ (f a) = ∑ c, B c a • f c := hτ
  apply ψ.injective
  show ψ (ψ.symm (τ (ψ (e b)))) = _

  rw [LinearEquiv.apply_symm_apply, hψ b, map_sum]
  simp only [map_smul, hτ']

  rw [sum_smul_sum, map_sum]
  simp only [map_smul, hψ]
  rw [sum_smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_assoc P⁻¹ B P, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem mat_eq_of_indep {e : Fin m → V} (he : LinearIndependent K e) (y : Fin m → V)
    {M M' : Matrix (Fin m) (Fin m) K} (h1 : ∀ b, y b = ∑ a, M a b • e a) (h2 : ∀ b, y b = ∑ a, M' a b • e a) :
    M = M' := by
  ext c b
  have h0 : ∑ i, (M i b - M' i b) • e i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h1 b, ← h2 b, sub_self]
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 he) _ h0 c)

end Gen

end GlobalTheory.HL.CovDict

namespace GlobalTheory.HL.CovDict

open Formalism.L2.SG.Pf.VolPinAsm Formalism.L2.SG.Pf.StabilizerIndexVolumes Matrix

theorem dict_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ (γw s s' : X.B.I.Ginf), Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t₀.pt.1 = s * γw * s'⁻¹ → ∃ σ : Formalism.L2.SG.RealObj.FreeE w → ℂ, (∀ p, ‖σ p‖ = (D.host.rdE : ℝ) ^ (p.1.2.val - p.1.1.val)) ∧ ∃ A : InfinitePlace X.B.I.F → (Formalism.L2.SG.RealObj.FreeE w → ℂ) →ₗ[ℂ] (Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ v x x' p, (∀ q : Formalism.L2.SG.RealObj.FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q) → A v x p - x p = A v x' p - x' p) ∧ ∀ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n → c.grp ρ n ∈ G.K0 → ∀ v, Formalism.L2.SG.RealObj.stCoord X u' w γw (s⁻¹ * x.1 * s) v = A v (fun p => σ p * Formalism.L2.SG.Pf.VolPinAsm.phiV X v (GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) p.1.1 p.1.2)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv _ γw s s' _ _ hs' hpt
  obtain ⟨-, -, hU', -, hρ'⟩ := hMv
  have hrd : (0 : ℝ) < D.host.rdE := (Formalism.BasicNotions.rdE_pos_le D).1
  have hrdc : (D.host.rdE : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hrd.ne'
  have hU'u : IsUnit U'.det := by rw [up_det hU']; exact isUnit_one
  choose S hSU hS using fun v => inS_frame (hs' v)
  have hSu : ∀ v, IsUnit (S v).det := fun v => by rw [up_det (hSU v)]; exact isUnit_one
  set N : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v =>
    U'.map (phiV X v) * S v with hN
  have hNU : ∀ v, IsUpUni (N v) := fun v => up_mul (upUni_map (phiV X v) hU') (hSU v)
  have hNu : ∀ v, IsUnit (N v).det := fun v => by rw [up_det (hNU v)]; exact isUnit_one
  refine ⟨fun p => (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1), fun p => ?_,
    fun v => Alin w (D.host.rdE : ℂ) (N v), fun v x x' p hxx => Alin_shear w _ (hNU v) hrdc x x' p hxx, ?_⟩
  · rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hrd.le]
  intro x n hxn hK v
  funext p

  have hStm : c.grp ρ n ∈ G.St := fun q => by
    obtain ⟨g', hg', he⟩ := hK q
    exact ⟨g', hg'.1.1, he⟩
  obtain ⟨B, hBU, hBf, hBblk⟩ :=
    (GlobalTheory.T.rationalCommonStabiliser_unitriangular_coords D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c).1 _ hStm
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  have hli : LinearIndependent D.host.E G.f' := by
    have e : G.f' = fun a => c.e (frame F'0 a) := funext c.f'_eq
    rw [e]
    exact (Formalism.L2.SG.Pf.TupLift.frame_li F'0 hT').map' _ (LinearEquiv.ker _)
  have hB : GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) = B :=
    mat_eq_of_indep hli _ (GlobalTheory.HL.TraceConjugationCover.stMat_spec G _ ⟨B, hBf⟩) hBf
  rw [hB]

  set τ : (VS D).V ≃ₗ[D.host.E] (VS D).V := ρ.symm.trans (n.trans ρ) with hτdef
  have hτ : FM (frame F'0) τ B := by
    intro b
    apply c.e.injective
    have e1 : c.e (τ (frame F'0 b)) = c.grp ρ n (G.f' b) := by
      rw [c.f'_eq]; simp [GCoord.grp, τ]

    rw [e1, hBf b, map_sum]
    simp only [map_smul, c.f'_eq]
  set ψ : (VS D).V ≃ₗ[D.host.E] (VS D).V := t₀.lin.trans ρ with hψdef
  have hψ : ∀ b, ψ ((X.Fu u').fvec b) = ∑ a, U' a b • frame F'0 a := by
    intro b
    show ρ (t₀.lin _) = _
    rw [← Formalism.L2.SG.Pf.FibreCounting.frame_apply]
    exact hρ' b
  have hFMm := fm_conj ψ τ hU'u hψ hτ
  have hFMm' : FM (X.Fu u').fvec (t₀.lin⁻¹ * n * t₀.lin) (U'⁻¹ * B * U') := by
    intro b
    rw [← hFMm b]
    show t₀.lin.symm (n (t₀.lin _)) = _
    simp [ψ, τ]
  have hγx : RatLink X t₀.pt t₀.lin := t₀.rep.2.1
  set zz := t₀.pt⁻¹ * x * t₀.pt with hzz
  have hzL : RatLink X zz (t₀.lin⁻¹ * n * t₀.lin) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
      (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hγx) hxn) hγx
  have hgrp : γw⁻¹ * (s⁻¹ * x.1 * s) * γw = s'⁻¹ * zz.1 * s' := by
    have e1 : zz.1 = t₀.pt.1⁻¹ * x.1 * t₀.pt.1 := by simp only [hzz, Prod.fst_mul, Prod.fst_inv]
    have e2 : γw = s⁻¹ * t₀.pt.1 * s' := by rw [hpt]; group
    rw [e1, e2]; group
  have hmi : ∀ a : Formalism.REAL.UJ (X.B.I.ε v), Formalism.MainNotions.S.uMat a * Formalism.MainNotions.S.uMat a⁻¹ = 1 := by
    intro a
    show _ * (((a⁻¹ : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hu : Formalism.MainNotions.S.uMat ((s'⁻¹ * zz.1 * s') v) =
      (Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) := by
    have hi : Formalism.MainNotions.S.uMat ((s' v)⁻¹) = (Formalism.MainNotions.S.uMat (s' v))⁻¹ :=
      (Matrix.inv_eq_right_inv (hmi (s' v))).symm
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹ * zz.1 v * s' v) = _
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹) * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) = _
    rw [hi]
  have hs'u : IsUnit (Formalism.MainNotions.S.uMat (s' v)).det := by
    have := congrArg Matrix.det (hmi (s' v))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)
  have hFM : FM (efr X u' v) (fun y => ((Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) *
      Formalism.MainNotions.S.uMat (s' v)) *ᵥ y) ((S v)⁻¹ * (U'⁻¹ * B * U').map (phiV X v) * S v) :=
    FMm_mul (FMm_mul (FMm_inv hs'u (hS v) (hSu v)) (realFM X hzL hFMm' v)) (hS v)
  have hG : (S v)⁻¹ * (U'⁻¹ * B * U').map (phiV X v) * S v = (N v)⁻¹ * B.map (phiV X v) * N v := by
    have hinv : (U'.map (phiV X v))⁻¹ = (U'⁻¹).map (phiV X v) :=
      Matrix.inv_eq_left_inv (map_inv_mul (phiV X v) hU'u)
    rw [show N v = U'.map (phiV X v) * S v from rfl, Matrix.mul_inv_rev, hinv, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hY : Yhat w (D.host.rdE : ℂ) (fun q => (D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1) *
      phiV X v (B q.1.1 q.1.2)) = B.map (phiV X v) - 1 := by
    ext c' d
    rw [Matrix.sub_apply, Matrix.map_apply]
    simp only [Yhat]
    split_ifs with hcd
    · rw [Matrix.one_apply_ne (ne_of_lt hcd.1), sub_zero]
      field_simp
    · by_cases hlt : c' < d
      · rw [hBblk c' d (fun he => hcd ⟨hlt, he⟩), map_zero, Matrix.one_apply_ne (ne_of_lt hlt), sub_zero]
      · rcases lt_or_eq_of_le (not_lt.1 hlt) with hgt | heq
        · rw [(hBU c' d).1 hgt, map_zero, Matrix.one_apply_ne (ne_of_gt hgt), sub_zero]
        · rw [heq, (hBU c' c').2 rfl, map_one, Matrix.one_apply_eq, sub_self]
  have hab : p.1.1 < p.1.2 := p.2.1
  have har : p.1.1.1 < D.R.rS := lt_of_lt_of_le hab (Nat.lt_succ_iff.1 p.1.2.2)
  show Formalism.L2.SG.RealObj.stCoord X u' w γw _ v p = Alin w (D.host.rdE : ℂ) (N v) _ p
  unfold Formalism.L2.SG.RealObj.stCoord
  rw [hgrp, hu, Alin_apply, hY]
  have hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 =
      (((D.host.rdE : ℂ)) ^ (D.R.rS - p.1.2.1))⁻¹ • efr X u' v p.1.2 := rfl
  rw [hfrm, coef_efr X u' v hFM ⟨p.1.1.1, har⟩ p.1.2, hG]
  have hcs : (Fin.castSucc (⟨p.1.1.1, har⟩ : Fin D.R.rS)) = p.1.1 := Fin.ext rfl
  rw [hcs, conj_off (hNu v) (ne_of_lt hab)]
  have hpow : (D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) =
      (D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.1) * (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1) := by
    rw [← pow_add]; congr 1
    have : (p.1.2 : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.1 p.1.2.2
    have : (p.1.1 : ℕ) < p.1.2 := hab
    omega
  rw [hpow]
  field_simp

end GlobalTheory.HL.CovDict
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.WittFrames

theorem zhatOM_injective {K : Type*} [CommRing K] {r : ℕ} {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : ZhatOM Z = ZhatOM Z') : Z = Z' := by
  ext a b
  have h1 := congrFun (congrFun h a) b
  simp only [ZhatOM] at h1
  exact ((isUnit_one.neg).pow (r - b.val)).mul_left_cancel h1

theorem tri_symm {E W : Type} [Field E] [AddCommGroup W] [Module E W] {n : ℕ} {f g : Fin n → W}
    (h : Tri E f g) : Tri E g f := by
  obtain ⟨A, ⟨hA1, hA2⟩, hc⟩ := h
  have hbt : A.BlockTriangular id := fun i j hij => hA1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [hA2]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  obtain ⟨hB1, hB2⟩ := inv_unitri A hA1 hA2
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  refine ⟨A⁻¹, ⟨hB1, hB2⟩, fun b => ?_⟩
  show f b = ∑ a, A⁻¹ a b • g a
  have hm := Matrix.mul_nonsing_inv A hu
  simp_rw [hc', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ a, (A⁻¹ a b * A c a) • f c = (A * A⁻¹) c b • f c := by
    intro c
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  simp_rw [this, hm, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

theorem tri_map {E W : Type} [Field E] [AddCommGroup W] [Module E W] {n : ℕ} {f g : Fin n → W}
    (γ : W →ₗ[E] W) (h : Tri E f g) : Tri E (fun a => γ (f a)) (fun a => γ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  refine ⟨A, hA, fun b => ?_⟩
  show γ (g b) = ∑ a, A a b • γ (f a)

  rw [hc' b, map_sum]
  simp [map_smul]

theorem exists_isom_of_gram (hW : PI.WittExtension) {K V : Type} [Field K] [StarRing K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (B x y) = B y x) (hn : ∀ x, (∀ y, B x y = 0) → x = 0)
    {ι : Type} (v v' : ι → V) (hv : LinearIndependent K v) (hv' : LinearIndependent K v')
    (hg : ∀ i j, B (v i) (v j) = B (v' i) (v' j)) :
    ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ i, g (v i) = v' i := by
  let U := Submodule.span K (Set.range v)
  let bU : Module.Basis ι K U := Module.Basis.span hv
  have hbU : ∀ i, (bU i : V) = v i := fun i => congrArg Subtype.val (Module.Basis.span_apply hv i)
  let f : U →ₗ[K] V := bU.constr K v'
  have hf : ∀ i, f (bU i) = v' i := fun i => by simp [f, Module.Basis.constr_basis]
  have hfe : f = Finsupp.linearCombination K v' ∘ₗ bU.repr.toLinearMap := by
    refine bU.ext (fun i => ?_)
    rw [hf]; simp
  have hinj : Function.Injective f := by
    rw [hfe, LinearMap.coe_comp]
    exact Function.Injective.comp hv' bU.repr.injective
  have hiso : ∀ x y : U, B (f x) (f y) = B x y := by
    have : (B.comp f).compl₂ f = (B.comp U.subtype).compl₂ U.subtype := by
      refine LinearMap.ext_basis bU bU (fun i j => ?_)
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply, hf, hbU]
      exact (hg i j).symm
    intro x y
    have := LinearMap.congr_fun₂ this x y
    simpa using this
  obtain ⟨g, hg1, hg2⟩ := hW K V B hs hn U f hinj hiso
  exact ⟨g, hg1, fun i => by rw [← hbU i, hg2, hf]⟩

end GlobalTheory.LocOver.WittFrames

namespace GlobalTheory.LocOver


open GlobalTheory.LocOver.WittFrames Formalism.L2.SG.GramJoint in
theorem witt_frames_at_point : ∀ (D : D7) {T T' : D.host.E} (F F00 : LFlag (D.sp.Y 0) D.R.rS T)
    (F' F'0 : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → Gval F F' ≠ 0 →
    IsInCell (ZhatOM (ZhatL F F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w →
    Gval F00 F'0 = Gval F F' ∧ ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT,
      Tri D.host.E (frame F00) (fun a => γ (frame F a)) ∧ Tri D.host.E (frame F'0) (fun a => γ (frame F' a)) := by
  intro D T T' F F00 F' F'0 w hT hT' hG hcell hpt
  obtain ⟨⟨Fb, Fb', h1, h2, hb⟩, hall⟩ := GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D F F' w hT hT' hcell
  have hGb : Gval Fb Fb' = Gval F F' := (hall Fb Fb' h1 h2).2
  have hZ : ZhatL Fb Fb' = ZhatL F00 F'0 := zhatOM_injective (hb.trans hpt.symm)
  have hG0 : Gval F00 F'0 = Gval Fb Fb' := by
    show Gmat (Zhat F00.fl F'0.fl) T T' = Gmat (Zhat Fb.fl Fb'.fl) T T'
    exact congrArg (fun Z => Gmat Z T T') hZ.symm
  refine ⟨hG0.trans hGb, ?_⟩
  have hGb0 : Gflag Fb.fl Fb'.fl ≠ 0 := by rw [← hGb] at hG; exact hG
  have hG00 : Gflag F00.fl F'0.fl ≠ 0 := by
    have := hG0.trans hGb; rw [← this] at hG; exact hG
  have hli := (gramIndep D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl hGb0).1
  have hli' := (gramIndep D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl hG00).1
  have hgram : ∀ i j, (VS D).hT (pairVec Fb.fl Fb'.fl i) (pairVec Fb.fl Fb'.fl j) =
      (VS D).hT (pairVec F00.fl F'0.fl i) (pairVec F00.fl F'0.fl j) := by
    intro i j
    have e := congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl) i) j
    have e' := congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl) i) j
    have hZ' : Zhat Fb.fl Fb'.fl = Zhat F00.fl F'0.fl := hZ
    rw [hZ'] at e
    exact e.trans e'.symm
  have hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := fun x y => (VS D).herm.eq x y
  have hn : ∀ x, (∀ y, (VS D).hT x y = 0) → x = 0 := fun x hx => (VS D).nondeg.1 x hx
  obtain ⟨γ, hγ, hγv⟩ := exists_isom_of_gram witt_extension_theorem (VS D).hT hs hn _ _ hli hli' hgram
  refine ⟨γ, fun x y => hγ x y, ?_, ?_⟩
  · have := tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h1
    have e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb a)) = frame F00 :=
      funext fun a => hγv (Sum.inl a)
    rw [e] at this
    exact tri_symm this
  · have := tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h2
    have e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb' a)) = frame F'0 :=
      funext fun a => hγv (Sum.inr a)
    rw [e] at this
    exact tri_symm this

end GlobalTheory.LocOver
end

section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeAsm.GLinkPf

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem inN_of_nlam (F : FlagG S r T) (hT : T ≠ 0) {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (h : n ∈ NLam Λ (⟨F, F.z⟩ : LFlag S r T)) : (frF F hT).InN (n : S.V →ₗ[E] S.V) := by
  obtain ⟨⟨hiso, -⟩, hXa, hperp⟩ := h
  refine ⟨fun x y => hiso y x, n.bijective, fun a => ?_, fun y hy => ?_⟩
  · rw [GlobalTheory.TypeAsm.FibProof.frF_e, fv_cast, GlobalTheory.TypeAsm.FibProof.frF_Xa]
    exact hXa a.val (F.e a) (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
  · rw [GlobalTheory.TypeAsm.FibProof.frF_X]
    apply hperp
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    change x ∈ F.X at hx
    rw [← GlobalTheory.TypeAsm.FibProof.frF_X F hT] at hx
    have hle : (frF F hT).X ≤ LinearMap.ker (S.hT.flip y) := by
      unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
      rw [Submodule.span_le]
      rintro _ ⟨a, -, rfl⟩
      have := hy a
      rw [GlobalTheory.TypeAsm.FibProof.spH_B] at this
      exact p_symm_zero S this
    exact hle hx

end Gen

variable {D : D7} {X : HidaSetting D}

theorem smul_top (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    n • (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤ := by
  rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.2 n.surjective

theorem mem_gam_iff (u : D.what₂.Word) (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (hF : N.F = F0 X u)
    (hF' : N.F' = F0 X u) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    n ∈ N.Gam (VS D).L0 ↔ n ∈ NLam (VS D).L0 (lf D (X.Fu u)) := by
  unfold GlobalTheory.DegCnt.NF.Gam GlobalTheory.DegCnt.NF.R
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨hR, hst⟩
    have hT : n ∈ NLam ⊤ (lf D (X.Fu u)) := by
      clear hst
      induction hR using Subgroup.closure_induction with
      | mem s hs =>
        have h1 := hs.1
        rw [hF] at h1
        exact GlobalTheory.TypeAsm.FibProof.nlam_of_inN (lf D (X.Fu u)).fl (tu_ne D u) h1 (smul_top s)
      | one => exact GlobalTheory.LoopC.FrEqv.one_mem_NLam
      | mul x y _ _ hx hy => exact GlobalTheory.LoopC.FrEqv.mul_mem_NLam hy hx
      | inv x _ hx => exact GlobalTheory.LoopC.FrEqv.symm_mem_NLam hx
    exact ⟨⟨hT.1.1, by rw [GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact hst⟩, hT.2.1, hT.2.2⟩
  · intro h
    refine ⟨Subgroup.subset_closure ?_, ?_⟩
    · have h1 : (F0 X u).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) := inN_of_nlam (lf D (X.Fu u)).fl (tu_ne D u) h
      rw [hF, hF']
      exact ⟨h1, h1⟩
    · rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact h.1.2

theorem trI_act (C : Choice X 1) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (τ : D.what₂.Tau) (y : (VS D).V) :
    Matrix.of (trI C x.1 τ) *ᵥ phiV C τ y = phiV C τ (n y) := by
  obtain ⟨_, hQQi, _, _⟩ := C.isT τ
  obtain ⟨M, _, hM1, _, hM3⟩ := hx
  have hM1' : uMat (x.1 (vOf X τ)) = (X.B.I.P (vOf X τ))⁻¹ *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) * X.B.I.P (vOf X τ) := hM1 _
  have hM3' : X.crd (n y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3 y
  have e : Matrix.of (trI C x.1 τ) = Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x.1 (vOf X τ)) := by
    unfold trI; exact Matrix.of.apply_symm_apply _
  rw [e]
  unfold GlobalTheory.TypeAsm.phiV Formalism.L2.SG.RealObj.trG
  rw [hM3', ← Formalism.L2.SG.Pf.rv_mulVec X (vOf X τ), ← hM1']
  have hQ : ∀ w, C.Q τ *ᵥ (C.Qi τ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec]
  rw [hQ]

theorem eq_of_act (C : Choice X 1) {m m' : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (h : ∀ τ y, Matrix.of (m τ) *ᵥ phiV C τ y = phiV C τ (n y))
    (h' : ∀ τ y, Matrix.of (m' τ) *ᵥ phiV C τ y = phiV C τ (n y)) : m = m' := by
  funext τ
  have hL : Matrix.mulVecLin (Matrix.of (m τ)) = Matrix.mulVecLin (Matrix.of (m' τ)) :=
    LinearMap.ext_on_range (GlobalTheory.TypeAsm.GramPf.phiV_span C τ) (fun y => by
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, h τ y, h' τ y])
  apply Matrix.of.injective
  ext i j
  have := congrFun (LinearMap.congr_fun hL (Pi.single j 1)) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this

end GlobalTheory.TypeAsm.GLinkPf

namespace GlobalTheory.TypeAsm

theorem realPts_Gam_eq_trI_image_NOinf : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u →
      GlobalTheory.DegVol.realPts (fun τ => phiV C τ) (N.Gam (VS D).L0 : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) =
        trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := by
  intro D _ X _ u C _ N hF hF'
  ext m
  constructor
  · rintro ⟨n, hn, hm⟩
    have hL := (GLinkPf.mem_gam_iff u N hF hF' n).1 hn
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hL.1.1
    refine ⟨x.1, (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u x.1).2 ⟨x, n, hx, rfl, hL⟩, ?_⟩
    exact GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x, n, hx, rfl, hL⟩ := (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u s).1 hs
    exact ⟨n, (GLinkPf.mem_gam_iff u N hF hF' n).2 hL, fun τ y => GLinkPf.trI_act C hx τ y⟩

end GlobalTheory.TypeAsm
end
end
