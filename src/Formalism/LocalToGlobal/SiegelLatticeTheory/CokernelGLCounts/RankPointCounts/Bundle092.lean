module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle080
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle073
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle082
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle089
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle065
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle009

@[expose] public section

section

noncomputable section

open Matrix ValuativeRel
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount
  Formalism.L2.SG.LsDatumB

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents



attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cross_of_comp {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ} {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (h1 : Cross (A.map (π1 M g)) (A'.map (π1 M g))) (h2 : Cross (A.map (π2 M g)) (A'.map (π2 M g))) : Cross A A' := by
  unfold Cross at h1 h2 ⊢
  have d : ∀ (f : E →+* F) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (B.map f).det = f B.det :=
    fun f B => (RingHom.map_det f B).symm
  rw [ld_map, ld_map, d, d, ← map_mul, ← map_mul] at h1 h2
  apply g.e.injective
  exact Prod.ext h1 h2

theorem gaPlusTh_of (hLO : LiftOrb) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) : GaPlusTh M δ u u' := by
  intro hA hT hPH w w' Z Z' hk hZ hZ' p hne heq
  set c := cornerSh δ (D.mem u).A.T (D.mem u').A.T p w with hc
  have hc' : cornerSh δ (D.mem u).A.T (D.mem u').A.T p w' = c := (cornerSh_of_kind δ _ _ p hk).symm
  set Y := CntLocal.ZZP (M := M) δ u u' p Z + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY
  set Y' := CntLocal.ZZP (M := M) δ u u' p Z' + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY'
  have hcm : ∀ cc : (D.s.atP p).Ep, (Matrix.of fun a b : Fin (D.R.rS + 1) =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cc else 0) = cc • Ec (K := (D.s.atP p).Ep) D.R.rS := by
    intro cc; ext a b; simp only [Ec, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  have eY : FCount.thZ M δ u u' w Z p = clsOf (M p) Y := by
    unfold FCount.thZ thL; rw [hcm]
  have eY' : FCount.thZ M δ u u' w' Z' p = clsOf (M p) Y' := by
    unfold FCount.thZ thL; rw [hcm, hc']
  rw [eY] at hne heq
  rw [eY'] at heq

  have hXc : Cross (ZhatLoc M δ p Z) (ZhatLoc M δ p Z') := cross_zhatLoc δ M p (cross_global hk hZ hZ')
  have hZc : Cross (CntLocal.ZZP (M := M) δ u u' p Z) (CntLocal.ZZP (M := M) δ u u' p Z') := by
    unfold CntLocal.ZZP
    rcases hs : (M p).split with _ | g
    · unfold Loc.HermSp.ZZplusOf; rw [hs]; exact hXc
    · refine cross_of_comp (M p) g ?_ ?_
      · rw [zzPlus_map_firstComponent (M p) g hs, zzPlus_map_firstComponent (M p) g hs]
        exact cross_shift (cross_map _ hXc) _ _
      · rw [zzPlus_map_secondComponent (M p) g hs, zzPlus_map_secondComponent (M p) g hs]
        exact cross_shift (cross_transpose (cross_map _ hXc)) _ _
  unfold clsOf at hne heq
  by_cases h1 : (∀ a b, Y a b ∈ (M p).R) ∧ IsUnit Y.det
  swap
  · exact absurd (dif_neg h1) hne
  rw [dite_eq_left h1] at heq
  by_cases h2 : (∀ a b, Y' a b ∈ (M p).R) ∧ IsUnit Y'.det
  swap
  · rw [dif_neg h2] at heq; exact absurd heq (by simp)
  rw [dite_eq_left h2] at heq
  set ZZ : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y a b, h1.1 a b⟩, h1.2⟩ with hZZ
  set ZZ' : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y' a b, h2.1 a b⟩, h2.2⟩ with hZZ'
  have hmap : ZZ.Z.map (M p).R.subtype = Y := rfl
  have hmap' : ZZ'.Z.map (M p).R.subtype = Y' := rfl
  have hiso : Nonempty ((M p).Iso ZZ ZZ') := Quotient.exact (Option.some.inj heq)
  have hκ : (ZZ.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) =
      (ZZ'.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) := by
    rw [hmap, hmap']
    exact kappa_eq hZc c h1.2 h2.2
  obtain ⟨l, ρ, hlu, hρu, hle, hρl, hrel⟩ := hLO (M p) (hA p).1 D.R.rS ZZ ZZ' hiso hκ
  set L := l.map (M p).R.subtype with hLdef
  set P := ρ.map (M p).R.subtype with hPdef
  have hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0 := by
    intro i; simp only [hLdef, Matrix.map_apply, hle i]; split_ifs <;> simp
  have hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0 := by
    intro j; simp only [hPdef, Matrix.map_apply, hρl j]; split_ifs <;> simp
  have hYrel : Y' = L * Y * P := by
    rw [← hmap, ← hmap', hrel, Matrix.map_mul, Matrix.map_mul]
  have hZrel : CntLocal.ZZP (M := M) δ u u' p Z' = L * CntLocal.ZZP (M := M) δ u u' p Z * P := by
    have e := hYrel
    rw [hY, hY', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Ec_eq_cornerM,
      corner_sandwich L P hL hP 1] at e
    exact add_right_cancel e
  have hLR : ∀ i j, L i j ∈ (M p).R := fun i j => (l i j).2
  have hPR : ∀ i j, P i j ∈ (M p).R := fun i j => (ρ i j).2
  have hLu : ∃ y ∈ (M p).R, L.det * y = 1 := by
    obtain ⟨v, hv⟩ := hlu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : L.det = ((l.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype l).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  have hPu : ∃ y ∈ (M p).R, P.det * y = 1 := by
    obtain ⟨v, hv⟩ := hρu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : P.det = ((ρ.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype ρ).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rcases hs : (M p).split with _ | g
  · have hRO : (M p).R = (M p).L.O := by unfold Loc.Model.R; rw [hs]
    have hX : ZhatLoc M δ p Z' = L * ZhatLoc M δ p Z * P := by
      have e := hZrel
      unfold CntLocal.ZZP Loc.HermSp.ZZplusOf at e
      rw [hs] at e
      exact e
    obtain ⟨yL, hyL, hLy⟩ := hLu
    obtain ⟨yP, hyP, hPy⟩ := hPu
    exact gaCong_L δ M hA p hs _ _ Z Z' L P hL hP (fun i j => hRO ▸ hLR i j) (fun i j => hRO ▸ hPR i j)
      ⟨yL, hRO ▸ hyL, hLy⟩ ⟨yP, hRO ▸ hyP, hPy⟩ hX
  · exact gaCong_G δ M hA p g hs _ _ _ _ Z Z' L P hL hP hLR hPR hLu hPu hZrel

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem pinOm_cancel {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {a k d₁ d₂ : R} {A B C : W}
    (ha : IsUnit a) (hk : IsUnit k) (hd : IsUnit d₂) (h1 : (a * d₂ * k) • A = (a * d₁ * k) • B)
    (h2 : d₂ • C = d₁ • B) : A = C := by
  have key : (a * d₂ * k) • A = (a * d₂ * k) • C := by
    rw [h1]
    calc (a * d₁ * k) • B = (a * k) • (d₁ • B) := by rw [smul_smul]; congr 1; ring
      _ = (a * k) • (d₂ • C) := by rw [h2]
      _ = (a * d₂ * k) • C := by rw [smul_smul]; congr 1; ring
  obtain ⟨v, hv⟩ := (ha.mul hd).mul hk
  have := congrArg (fun w => ((v⁻¹ : Rˣ) : R) • w) key
  simp only [← hv, smul_smul, Units.inv_mul, one_smul] at this
  exact this



theorem pinOm_holds : PinOm Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hβ hfr hW hO p hm hm₂
  obtain ⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩ := hB
  obtain ⟨hZd, -, -⟩ := starMinors_holds u u' F0 what₂ γ Z hCtx
  have hT2 := hS.2.1 p
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  obtain ⟨K, hK⟩ : ∃ K : (D.s.atP p).Ep, K = (Zd.M p).L.cj (∏ j ∈ Finset.univ.erase (Fin.last D.R.rS), sF' Zd p j) *
      ∏ j, sF Zd p j := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : (D.s.atP p).Ep, P = (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sF Zd p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Zd p (Fin.castLE le_rfl i)) := ⟨_, rfl⟩
  have ho1 : (locH Zd p).om (tLoc Zd p γ).f (tLoc Zd p γ).f' = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame (repF γ))) := by
    have e := om_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p)
    rw [Gom_frameAct (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hK] at e
    exact e
  have ho2 : (locH Zd p).om (tLoc Zd p γ).f (locF' Zd p F'₂) = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) := by
    have e := om_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p)
    rw [← hK] at e
    exact e
  have hd1 : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [GDl_frameAct_top (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hP] at e
    exact e
  have hd2 : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [← hP] at e
    exact e
  have hid := hT2.2.2.2.1
  have hs := hid.2.2.2.2.1
  dsimp only at hs
  rw [ho1, ho2, hd1, hd2] at hs
  have hω₂ : baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) :=
    baseChangeAt_perp' Zd p F'₂ (Gom_orth (lf D F0) F'₂)
  have h1 := hs (K • ⟨_, hm⟩) (K • ⟨_, hω₂⟩) rfl rfl
  have e1 := ((locH Zd p).mkW (tLoc Zd p γ).f').map_smul K ⟨_, hm⟩
  have e2 := ((locH Zd p).mkW (locF' Zd p F'₂)).map_smul K ⟨_, hω₂⟩
  have e3 := ((φ' p).toLinearMap).map_smul K ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hm⟩)
  rw [e1, e2, e3, smul_smul, smul_smul] at h1
  have hD2 : GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [GDl_top']
    have e : GZ (frame (lf D F0)) (frame F'₂) = Z := hS.1
    rw [e]; exact hZd
  have hOp : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        baseChange₂ D p (β₀ (Gom (frame (lf D F0)) (frame (repF γ)))) -
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).X (locF' Zd p F'₂) := by
    have := bcP_X' Zd p (liftF F'₂) hO
    rw [map_sub, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂] at this
    exact this
  have hcls : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hm₂⟩ =
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hω₂⟩ := by
    rw [← LinearMap.map_smul, ← LinearMap.map_smul]
    apply (Submodule.Quotient.eq _).2
    exact hOp
  rw [map_mul, map_mul, cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)] at h1
  have hPu : IsUnit P := by
    rw [hP]
    exact (IsUnit.prod_univ_iff.2 fun i => (isUnit_sF Zd p _).map _).mul
      (IsUnit.prod_univ_iff.2 fun i => isUnit_sF' Zd p _)
  have hKu : IsUnit K := by
    rw [hK]
    exact ((IsUnit.prod_iff.2 fun j _ => isUnit_sF' Zd p j).map _).mul
      (IsUnit.prod_univ_iff.2 fun j => isUnit_sF Zd p j)
  have hDu : IsUnit ((D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)))) :=
    (isUnit_iff_ne_zero.2 (star_ne_zero.2 hD2)).map _
  exact pinOm_cancel (hPu.map _) hKu hDu h1 hcls

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.RealFrameCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)

def g0 (γ : X.B.I.Ginf) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ))

private theorem rdE_pos_rank_point_counts (D : D7) : 0 < D.host.rdE := by
  simp only [Formalism.BasicNotions.Host.rdE]
  apply Real.rpow_pos_of_pos
  rw [abs_pos]
  exact_mod_cast NumberField.discr_ne_zero (K := D.host.E)

private theorem frS_eq_inv_rdE (D : D7) : frS D = ((D.host.rdE : ℝ) : ℂ)⁻¹ := by
  have hne := (rdE_pos_rank_point_counts D).ne'
  have hpi := Real.pi_ne_zero
  have h : D.host.ka / (2 * Real.pi) = D.host.rdE⁻¹ := by
    simp only [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v]
    field_simp <;> ring
  simp only [frS, h, Complex.ofReal_inv]

private theorem rhoF_eq_frS_pow (D : D7) (a : Fin (D.R.rS + 1)) :
    ((rhoF D a : ℝ) : ℂ) = frS D ^ (D.R.rS - (a : ℕ)) := by
  have hpos := rdE_pos_rank_point_counts D
  have ha : (a : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.mp a.isLt
  rw [frS_eq_inv_rdE]
  simp only [rhoF]
  rw [show (-((D.R.rS : ℝ) - ((a : ℕ) : ℝ))) = -(((D.R.rS - (a : ℕ) : ℕ) : ℝ)) by rw [Nat.cast_sub ha],
    Real.rpow_neg hpos.le, Real.rpow_natCast, Complex.ofReal_inv, Complex.ofReal_pow, inv_pow]

private theorem Q_mulVec_fvec_eq_smul_frm (τ : D.what₂.Tau) (a : Fin (D.R.rS + 1)) :
    C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a =
      ((rhoF D a : ℝ) : ℂ) • Formalism.L2.SG.RealObj.frm X u 1 (vOf X τ) a := by
  obtain ⟨-, h2, -, h4⟩ := C.isT τ
  induction a using Fin.lastCases with
  | last =>
    simp only [Formalism.QuantumDeterminants.fvec, Fin.val_last, lt_self_iff_false, dite_false, zB, Matrix.mulVec_mulVec, h2,
      Matrix.one_mulVec, rhoF_eq_frS_pow, Nat.sub_self, pow_zero, one_smul, Formalism.L2.SG.RealObj.frm,
      Formalism.L2.SG.RealObj.famSc, Formalism.L2.SG.RealObj.fam, Fin.snoc_last, Complex.ofReal_one, one_pow, inv_one]
  | cast i =>
    obtain ⟨hq, -⟩ := h4 i i rfl
    simp only [Formalism.QuantumDeterminants.fvec, Fin.coe_castSucc, i.isLt, dite_true, Fin.eta, Formalism.QuantumDeterminants.bvec, hq, rhoF_eq_frS_pow,
      Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc,
      Complex.ofReal_one, one_pow, inv_one, one_smul]

private theorem herm_Hpk_eq_hJ_Q_mulVec (τ : D.what₂.Tau) (x y : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) x y =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ y) (C.Q τ *ᵥ x) := by
  obtain ⟨-, -, h3, -⟩ := C.isT τ
  rw [← h3]
  simp only [Formalism.QuantumDeterminants.herm, hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

private theorem Q_mulVec_g0_mulVec_eq (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    C.Q τ *ᵥ ((g0 C γ τ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) *ᵥ w) =
      uMat (γ (vOf X τ)) *ᵥ (C.Q τ *ᵥ w) := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  simp only [g0, Formalism.L2.SG.RealObj.trG, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem zhat_conjugator_scaled (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (g0 C γ τ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) * Formalism.L2.SG.RealObj.ZX X u u' 1 γ (vOf X τ) a b := by
  simp only [Formalism.QuantumDeterminants.Zhat]
  rw [herm_Hpk_eq_hJ_Q_mulVec C τ, Q_mulVec_g0_mulVec_eq C γ τ, Q_mulVec_fvec_eq_smul_frm C u τ, Q_mulVec_fvec_eq_smul_frm C u' τ]
  have hs : ∀ x : ℝ, star (x : ℂ) = (x : ℂ) := fun x => Complex.conj_ofReal x
  simp only [Formalism.L2.SG.RealObj.ZX, Formalism.L2.SG.RealObj.Zhat, hJ, Matrix.mulVec_smul, star_smul, hs,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  push_cast
  ring

private theorem ptEntry_locBlocksFrom_eq (D : D7) (τ : D.what₂.Tau) :
    ∀ (L : List (D.host.E × ℕ)) (A i j : ℕ),
      ptEntry (locBlocksFrom D (rhoReal D) τ A L) i j =
        ((D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + i : ℕ) : ℤ))) *
          D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + j : ℕ) : ℤ))) : ℝ) : ℂ) * plEmb D τ (ptEntry L i j) := by
  have hne : D.host.rdE ≠ 0 := (rdE_pos_rank_point_counts D).ne'
  intro L
  induction L with
  | nil =>
    intro A i j
    simp only [locBlocksFrom, ptEntry, map_zero, mul_zero]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    intro A i j
    simp only [locBlocksFrom, ptEntry]
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : i + j + 1 = s
      · rw [if_pos h2, if_pos h2]
        have hz : rhoReal D (A + 1) s = D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + i : ℕ) : ℤ))) *
            D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + j : ℕ) : ℤ))) := by
          rw [← zpow_add₀ hne]
          simp only [rhoReal]
          congr 1
          push_cast
          omega
        rw [hz]
      · rw [if_neg h2, if_neg h2, map_zero, mul_zero]
    · rw [if_neg h1, if_neg h1]
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [if_pos h3, if_pos h3, ih]
        obtain ⟨h3i, h3j⟩ := h3
        rw [show A + s + (i - s) = A + i by omega, show A + s + (j - s) = A + j by omega]
      · rw [if_neg h3, if_neg h3, map_zero, mul_zero]

theorem zhat_conjugator_eq_point (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w γ)
    (τ : D.what₂.Tau) :
    ZhatO D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (g0 C γ τ) = ptMat (ptLoc D τ w) := by
  funext a b
  have hv : X.pl (vOf X τ) = τ := X.pl.apply_symm_apply τ
  have hpe : ∀ x, plEmb D τ x = embS D τ x := fun x => rfl
  have hρ : ∀ c : Fin (D.R.rS + 1), rhoF D c = D.host.rdE ^ (-((D.R.rS : ℤ) - ((c : ℕ) : ℤ))) := by
    intro c
    simp only [rhoF]
    rw [← Real.rpow_intCast]
    norm_num
  have hr := congrFun (congrFun (hrep (vOf X τ)) a) b
  simp only [Formalism.L2.SG.RealObj.ZhatO, Formalism.L2.SG.RealObj.ptC, Matrix.map_apply, X.φ_eq,
    RingEquiv.apply_symm_apply, hv, ptMat] at hr
  simp only [ZhatO, zhat_conjugator_scaled C u u' γ τ, ptMat, ptLoc, ptLocS, locBlocks, ptEntry_locBlocksFrom_eq, Nat.zero_add, hpe, hρ]
  rw [← hr]
  push_cast
  ring

theorem frS_mul_rd (D : D7) : frS D * (D.host.rdE : ℂ) = 1 := by
  rw [frS_eq_inv_rdE]
  exact inv_mul_cancel₀ (by exact_mod_cast (rdE_pos_rank_point_counts D).ne')

theorem rho_eq (D : D7) (b : Fin (D.R.rS + 1)) :
    ((rhoF D b : ℝ) : ℂ) = ((D.host.rdE : ℂ) ^ (D.R.rS - b.val))⁻¹ := by
  rw [rhoF_eq_frS_pow, frS_eq_inv_rdE, inv_pow]

theorem hpk_esI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) (Formalism.QuantumDeterminants.esI k r a) = v (Formalism.QuantumDeterminants.eI k r a) := by
  have ha := a.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Formalism.QuantumDeterminants.eI k r a)]
  · have h1 : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.esI k r a) (Formalism.QuantumDeterminants.eI k r a) = 1 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Formalism.QuantumDeterminants.eI, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext (by simp [Formalism.QuantumDeterminants.eI, h]))
    have h0 : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.esI k r a) j = 0 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

def cMg (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  C.Qi τ * ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) * C.Q τ

private theorem mulVec_apply_eq_herm_single {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) (i : Fin m) :
    (H *ᵥ x) i = Formalism.QuantumDeterminants.herm H x (Pi.single i 1) := by
  have hs : star (Pi.single i 1 : Fin m → ℂ) = Pi.single i 1 := by
    ext j
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  simp [Formalism.QuantumDeterminants.herm, hs, dotProduct, Pi.single_apply]

private theorem Q_mulVec_cMg_mulVec_eq (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (f : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    C.Q τ *ᵥ (cMg C γ τ y *ᵥ f) =
      ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) *ᵥ (C.Q τ *ᵥ f) := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  simp only [cMg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem stCoordV_eq (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)
    (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (p : Formalism.L2.SG.RealObj.FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y p =
      (cMg C γ τ y *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) p.1.2)
        (Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨p.1.1.1, by have := p.2.1; have := p.1.2.isLt; omega⟩) := by
  obtain ⟨-, -, -, h4⟩ := C.isT τ
  have hlt : p.1.1.1 < D.R.rS := by have := p.2.1; have := p.1.2.isLt; omega
  have hs : ∀ x : ℝ, star (x : ℂ) = (x : ℂ) := fun x => Complex.conj_ofReal x
  have hU : uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) =
      (uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ)) := by
    simp [uMat, Matrix.coe_units_inv]
  have hc : (star (frS D ^ (D.R.rS - ((⟨p.1.1.1, hlt⟩ : Fin D.R.rS) : ℕ))))⁻¹ =
      (D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) := by
    rw [frS_eq_inv_rdE, ← Complex.ofReal_inv, ← Complex.ofReal_pow, hs, Complex.ofReal_pow, Complex.ofReal_inv,
      inv_pow, inv_inv]
  obtain ⟨-, hf⟩ := h4 ⟨p.1.1.1, hlt⟩ ⟨p.1.1.1, hlt⟩ rfl
  rw [← hpk_esI D.R.k D.R.rS ⟨p.1.1.1, hlt⟩
      (cMg C γ τ y *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) p.1.2),
    mulVec_apply_eq_herm_single, herm_Hpk_eq_hJ_Q_mulVec C τ, hf, hc, Q_mulVec_cMg_mulVec_eq C γ τ, Q_mulVec_fvec_eq_smul_frm C u' τ]
  simp only [Formalism.L2.SG.NGPin.stCoordV, hU, rho_eq, Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc,
    Complex.ofReal_one, one_pow, inv_one, one_smul, hJ, Matrix.mulVec_smul, star_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hs, star_pow]
  ring

end Formalism.L2.SG.RealFrameCoordinates

end
end
