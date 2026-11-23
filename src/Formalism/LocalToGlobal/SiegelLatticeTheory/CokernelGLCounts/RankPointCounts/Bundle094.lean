module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLocInB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle090
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle081
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle080
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle071
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle079
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSDLoc
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocMassTyp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle004
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Corner

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLo_of_uni {L : Matrix (Fin n) (Fin n) R} (h : IsLoUni L) : IsLo L :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩

theorem isUp_of_uni {U : Matrix (Fin n) (Fin n) R} (h : IsUpUni U) : IsUp U :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h b a).1 hab⟩

theorem uni_of_isLo {L : Matrix (Fin n) (Fin n) R} (h : IsLo L) : IsLoUni L :=
  fun a b => ⟨fun hab => h.2 a b hab, fun e => by subst e; exact h.1 a⟩

theorem uni_of_isUp {U : Matrix (Fin n) (Fin n) R} (h : IsUp U) : IsUpUni U :=
  fun a b => ⟨fun hab => h.2 b a hab, fun e => by subst e; exact h.1 a⟩

end Corner

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def glOfLo {L : MP p} (h : IsLo L) : GLp p :=
  ⟨L, L⁻¹, Matrix.mul_nonsing_inv L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1])⟩

def glOfUp {U : MP p} (h : IsUp U) : GLp p :=
  ⟨U, U⁻¹, Matrix.mul_nonsing_inv U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1])⟩

theorem glue_one_one {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ} :
    glue e (1 : Matrix (Fin n) (Fin n) Fp) 1 = 1 :=
  mat_eq e (by rw [glue_map_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [glue_map_snd, Matrix.map_one _ (map_zero _) (map_one _)])

theorem corner_fix {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ}
    {l ρ Δ : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hl : IsLoUni l) (hρ : IsUpUni ρ) (k1 k2 : Fp)
    (h1 : Δ.map (p1 e) = k1 • Ecorner n) (h2 : Δ.map (p2 e) = k2 • Ecorner n) : l * Δ * ρ = Δ := by
  apply mat_eq e
  · rw [Matrix.map_mul, Matrix.map_mul, h1, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]
  · rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]



theorem baseAt_typed (hA : ∀ p, Agree δ M p) (g : Loc.SplitG (M p).L) (hM : (M p).split = some g)
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    BaseAt M δ u u' w p a := by
  have hAg := (hA p).2.2.2.2.2
  rw [hM] at hAg
  obtain ⟨sg, hR, hge, hgq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
    rcases hs : (D.s.atP p).split with _ | sg
    · rw [hs] at hAg; exact hAg.elim
    · rw [hs] at hAg; exact ⟨sg, rfl, hAg.1, hAg.2⟩
  let Zd : LocDat D := ⟨δ, M, hA⟩
  have hzz := Formalism.L2.SG.Pf.PCountEx.zz_fact Zd p sg hR g hM hge hgq u u' w (L := 1) (B := 1)
    Formalism.L2.SG.Pf.PCountEx.isLo_one' Formalism.L2.SG.Pf.PCountEx.isUp_one'
  have e1 : Matrix.diagonal (cf Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e2 : Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e3 : Matrix.diagonal (cfi Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  have e4 : Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  rw [e1, e2, e3, e4, glue_one_one, Matrix.one_mul, Matrix.mul_one] at hzz
  have hz : ZhatOM (ptMat w) = ptMat w * Sg D.host.E D.R.rS := by
    have h := Formalism.L2.SG.Pf.CountBase.zhatOM_sg (ptMat w)
    calc ZhatOM (ptMat w) = ZhatOM (ptMat w) * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
      _ = ptMat w * Sg D.host.E D.R.rS := by rw [h]
  rw [Matrix.one_mul, Matrix.mul_one, ← hz] at hzz
  have hYg : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = _ := hzz
  obtain ⟨Gl, Gu, hGl, hGu, hT⟩ := Formalism.L2.SG.Pf.PCountEx.target_fact Zd p sg hR g hM hge hgq u u' w
  have hY0 : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = Gl * modMat δ (D.mem u).A.T (D.mem u').A.T p w * Gu :=
    hzz.trans hT
  have hshE : Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Formalism.MainNotions.S.LocalSplitGroups.cornerSh δ (D.mem u).A.T (D.mem u').A.T p w • Ecorner D.R.rS := by
    ext i j
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Ecorner, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hsh : Gl * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w * Gu =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [hshE, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hGl hGu]
  have hmod := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  refine ⟨⟨(glOfLo p hGl, MulOpposite.op (glOfUp p hGu)), uni_of_isLo hGl, uni_of_isUp hGu⟩, ?_, ?_⟩
  · show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Gl * a.mat * Gu
    rw [hmod, Matrix.mul_add, Matrix.add_mul, hsh, ← hY0]
  · intro x

    have hd1 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p1 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then -((D.mem u).A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_fst, Formalism.L2.SG.Pf.PCount.mm1' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hd2 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p2 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then ((D.mem u').A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_snd, Formalism.L2.SG.Pf.PCount.mm2' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hfix := corner_fix sg.e x.2.1 x.2.2 _ _ hd1 hd2
    have hphi : phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat +
        (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w) := by
      show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
        _
      rw [hmod]; abel
    rw [hphi, smul_def, smul_def, Matrix.mul_add, Matrix.add_mul, hfix]
    constructor
    · intro h; exact add_right_cancel h
    · intro h; rw [h]

theorem baseAt_holds (hA : ∀ p, Agree δ M p) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) : BaseAt M δ u u' w p a := by
  rcases hM : (M p).split with _ | g
  · have h := Formalism.L2.SG.Pf.CountBase.baseConj_L hA u u' w p hM a ha
    refine ⟨1, ?_, fun x => ?_⟩
    · rw [OneMemClass.coe_one, one_smul]; exact h
    · show _ ↔ _
      rw [show phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat from h]
  · exact baseAt_typed M δ u u' w p hA g hM a ha

end Formalism.L2.SG.Pf.CountAt
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdBeta'_of_leaves (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) :
    BwdBeta' Zd u u' F0 what₂ :=
  bwdBeta'_of_core Zd repG_holds (betaCore_of₂ Zd (betaCore₂_of Zd hRat (scalarOf_holds Zd) hInt))

theorem fStarC_of_leaves' (hC : CtxP u u' F0 what₂) (hLP : LprPart Zd u u' F0 what₂)
    (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ :=
  fStarC_of_route2 Zd (starExists2_holds Zd u u' F0 what₂ hC)
    (fwdC_of_loc Zd hC.2.1 (omega_part_holds Zd u u' F0 what₂) (genXi_holds Zd) hLP)
    (bwdC_of''' Zd hC (bwdN_holds Zd u u' F0 what₂) (bwdTerm'_holds Zd u u' F0 what₂) (bwdBeta'_of_leaves Zd hRat hInt))
    (Uniq.uniqC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem frameAct_mem_Xplus {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (b : Fin (D.R.rS + 1)) :
    frameAct (frame G) ξ b ∈ G.fl.Xplus := by
  rw [SpanOmPf.Xplus_eq]
  show ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • frame G a ∈ _
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem form_zero (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {w : (VS D).V}
    (hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus)) {v : (VS D).V}
    (hv : v ∈ F0.Xplus ⊔ (repF γ).fl.Xplus) (c : (D.s.atP p).Ep) :
    LocFacts₂ Zd.M p (baseChange₂ D p w) (c • baseChange₂ D p v) = 0 := by
  rw [LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, map_zero,
    mul_zero]

theorem baseChange_mem_W0 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {w : (VS D).V}
    (hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus)) :
    baseChange₂ D p w ∈ (locH Zd p).W0 (tLoc Zd p γ).f (tLoc Zd p γ).f' := by
  show ∀ x ∈ (locH Zd p).Xp (tLoc Zd p γ).f ⊔ (locH Zd p).Xp (tLoc Zd p γ).f', (locH Zd p).h (baseChange₂ D p w) x = 0
  intro x hx
  rw [h_eq]
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  rw [LocFacts.localForm_add_right]
  have hA : LocFacts₂ Zd.M p (baseChange₂ D p w) a = 0 := by
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [tf]
      refine form_zero Zd p γ hw (Submodule.mem_sup_left ?_) _
      rw [SpanOmPf.Xplus_eq]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact LocFacts.localForm_zero_right Zd p _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
    | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]
  clear ha
  have hB : LocFacts₂ Zd.M p (baseChange₂ D p w) b = 0 := by
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [tf']
      exact form_zero Zd p γ hw (Submodule.mem_sup_right (frameAct_mem_Xplus _ _ i)) _
    | zero => exact LocFacts.localForm_zero_right Zd p _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
    | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]
  rw [hA, hB, add_zero]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement
end
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

def SDLocX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), IsSDLoc X.B.I.cm.sig X.B.I.J v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def UnramTypX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), TypAt X v → UnramAt (E := X.B.I.E) v

def STypIdx : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X), X.MeasTie hb →
    ((X.measW u).μSv p.1).IsHaarMeasure →
    ((X.measW u).μSv p.1 (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1)).toReal =
      ((glkC D.R.k (gOf p) : ℕ) : ℝ) / ((ukC D.R.k (gOf p) : ℕ) : ℝ) *
        ((X.measW u).μSv p.1 (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1)).toReal

theorem gAt_mem {D : D7} (X : HidaSetting D) (p : TypX X) : ((gAt X p.1 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  obtain ⟨p, hp⟩ := p
  have hT : IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) p := by
    unfold typSet at hp
    split_ifs at hp with hfin
    · simpa using hp
    · simp at hp
  unfold gAt
  split_ifs with h0
  · exact h0
  · unfold IsTyped at hT
    exact hT.resolve_left h0

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem inTypedC_loc (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) (hψ : IsCharAF X.B.I.F ψ) (hψs : IsStdChar ψ) :
    InTypedC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro hX _hP hL hL' hTF p
  have : Submodule.IsFullLattice X.B.I.E X.B.I.L :=
    { toIsLattice := Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg
      span_eq_top := X.B.I.L_span }
  have hTyp : TypAt X p.1 := p.2
  refine ⟨?_, hI X hb u p hX.1 (hL p.1).2.1, hI X hb u' p hX.1 (hL' p.1).2.1⟩
  have h := locMassTyp X.B.I.cm.sig X.B.I.J ψ p.1 (gAt X p.1) (frameOf X u) (frameOf X u')
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hψ, hψs⟩ _ _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u) (MassDataLevelSSteps.FrameW.frameOf_isStd X u')
    (hSD X p.1) (hUn X p.1 hTyp) ⟨X.B.I.L, inferInstance, rfl⟩
    (hTF p).1 (gAt_mem X p) (hTF p).2.1 (hTF p).2.2.1 (hTF p).2.2.2.2
    _ (hL p.1).1 _ (hL p.1).2.1 (hL p.1).2.2.1 _ (hL' p.1).2.1 (hL' p.1).2.2.1 (hL p.1).2.2.2 (hL' p.1).2.2.2
  show MX X u u' ψ p.1 / localVolumeUnit X ψ p.1 = _
  unfold MX localVolumeUnit OmX
  rw [if_pos hTyp, if_pos hTyp]
  exact h

theorem typedAll_of (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  exact inTypedC_loc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSD hUn hI T.ψ_char T.ψ_std

theorem typedAll_of_idx (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll :=
  typedAll_of (fun X v => Formalism.L2.SG.Pf.MassDataX.SDL.sdLocX_holds X v)
    (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) hI

end Main

end Formalism.L2.SG.Pf.MassDataX
end
end
