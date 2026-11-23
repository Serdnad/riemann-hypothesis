module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle060
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle056
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMemAsp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle029

@[expose] public section

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem lm_one {N l : ℕ} (hl : l ≤ N) : leadMinorE (1 : Matrix (Fin N) (Fin N) E) l = 1 := by
  unfold leadMinorE
  rw [dite_eq_left hl, Matrix.submatrix_one _ (Fin.castLE_injective hl), Matrix.det_one]

theorem lm_diag_right {N : ℕ} (X Dg : Matrix (Fin N) (Fin N) E) (hD : ∀ c b, c ≠ b → Dg c b = 0) (l : ℕ) :
    leadMinorE (X * Dg) l = leadMinorE X l * leadMinorE Dg l := by
  unfold leadMinorE
  split_ifs with h
  · have hsub : (X * Dg).submatrix (Fin.castLE h) (Fin.castLE h) =
        X.submatrix (Fin.castLE h) (Fin.castLE h) * Dg.submatrix (Fin.castLE h) (Fin.castLE h) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [Formalism.L2.SG.Pf.sum_castLE_td h]
      intro d hd
      have hj := j.isLt
      rw [hD d _ (fun e => by have h1 := congrArg Fin.val e; simp at h1; omega), mul_zero]
    rw [hsub, Matrix.det_mul]
  · simp

theorem zhatOM_one_eq {r : ℕ} :
    ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) = Matrix.diagonal fun b => (-1 : E) ^ (r - b.val) := by
  ext a b
  simp only [ZhatOM, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; rw [mul_one]
  · rw [mul_zero]

theorem zhatOM_eq_mul {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ZhatOM X = X * ZhatOM 1 := by
  rw [zhatOM_one_eq]
  ext a b
  rw [Matrix.mul_diagonal]
  simp only [ZhatOM]
  rw [mul_comm]

theorem zhatOM_zhatOM {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ZhatOM (ZhatOM X) = X := by
  ext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem lm_zhatOM {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (l : ℕ) :
    leadMinorE (ZhatOM X) l = leadMinorE X l * leadMinorE (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l := by
  rw [zhatOM_eq_mul X]
  refine lm_diag_right X _ (fun c b hcb => ?_) l
  rw [zhatOM_one_eq, Matrix.diagonal_apply_ne _ hcb]

theorem lm_sign_ne {r l : ℕ} (hl : l ≤ r + 1) :
    leadMinorE (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l ≠ 0 := by
  intro h0
  have := lm_zhatOM (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l
  rw [zhatOM_zhatOM, lm_one hl, h0, mul_zero] at this
  exact one_ne_zero this

theorem lm_cell {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (w : Point E (r + 1))
    (h : IsInCell (ZhatOM X) w) (l : ℕ) :
    leadMinorE X l * leadMinorE (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l = leadMinorE (ptMat w) l := by
  obtain ⟨L, U, hL, hU, hX⟩ := h
  rw [← lm_zhatOM, hX]
  exact Formalism.L2.SG.Pf.leadMinor_uni L (ptMat w) U (fun a c h => (hL a c).1 h) (fun a => (hL a a).2 rfl)
    (fun d b h => (hU d b).1 h) (fun b => (hU b b).2 rfl) l

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem starDmin_eq (w : Point D.host.E (D.R.rS + 1)) (l : ℕ) : Dmin w l = leadMinorE (ptMat w) l := by
  unfold Dmin leadMinorE
  split_ifs <;> rfl

theorem starRepF_rep (γ : TermDef.Term D u u' F0 what₂) :
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls (repF γ) := by
  unfold repF
  rcases hn : nrep γ with _ | x
  · exact ⟨(Quot.out γ.cls).2, Quot.out_eq _⟩
  · unfold nrep at hn
    split_ifs at hn with h
    cases hn
    exact h.choose_spec.1

theorem star_frame_cell_minor (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w)
    (l : ℕ) : leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) l *
      leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l = leadMinorE (ptMat w) l := by
  obtain ⟨F', ⟨h1, h1e⟩, -, hcell⟩ := hγ.2
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
    (h1e.trans h2e.symm)
  have hc := Formalism.L2.SG.Pf.cell_rel (lf D F0) hrel w hcell
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  have hZ : starZh (frame (lf D F0)) (starFrame γ) =
      1 * ZhatL (lf D F0) (repF γ) * (Matrix.of fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E)) := by
    rw [Matrix.one_mul]
    exact FsLA.gram_comb_left (S := VS D) (frame (repF γ)) _ (frame (lf D F0))
  rw [hZ, Formalism.L2.SG.Pf.leadMinor_uni 1 _ _ (fun a c h => Matrix.one_apply_ne (ne_of_lt h)) (fun a => Matrix.one_apply_eq a)
    (fun d b h => by simp [Matrix.of_apply, hξ1 d b h]) (fun b => by simp [Matrix.of_apply, hξ2 b]) l]
  exact FsLA.lm_cell _ w hc l

variable (u u' F0 what₂)

theorem starMinors_holds : StarMinors u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨w, hγ, w', -, hk, hZ⟩ := hC
  have hs : ∀ l, l ≤ D.R.rS + 1 →
      leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l ≠ 0 :=
    fun l hl => FsLA.lm_sign_ne hl
  have c1 := star_frame_cell_minor γ w hγ
  have c2 := FsLA.lm_cell Z w' hZ
  have hdet : ∀ v : Point D.host.E (D.R.rS + 1), leadMinorE (ptMat v) (D.R.rS + 1) ≠ 0 := fun v => by
    rw [FsLA.leadMinorE_full]; exact Formalism.L2.SG.Pf.det_ptMat_ne v
  have hcross : Dmin w D.R.rS * Dmin w' (D.R.rS + 1) = Dmin w' D.R.rS * Dmin w (D.R.rS + 1) := by
    unfold kind at hk
    by_cases h0 : Dmin w D.R.rS = 0
    · rw [if_pos h0] at hk
      have h0' : Dmin w' D.R.rS = 0 := by
        by_contra h; rw [if_neg h] at hk; cases hk
      rw [h0, h0', zero_mul, zero_mul]
    · rw [if_neg h0] at hk
      have h0' : Dmin w' D.R.rS ≠ 0 := by
        intro h; rw [if_pos h] at hk; cases hk
      rw [if_neg h0'] at hk
      have hz := Option.some.inj hk
      unfold zetaOf at hz
      field_simp at hz
      linear_combination hz
  rw [starDmin_eq, starDmin_eq, starDmin_eq, starDmin_eq, ← c1, ← c1, ← c2, ← c2] at hcross
  refine ⟨?_, ?_, ?_⟩
  · rw [← FsLA.leadMinorE_full]
    intro h; apply hdet w'; rw [← c2, h, zero_mul]
  · rw [← FsLA.leadMinorE_full]
    intro h; apply hdet w; rw [← c1, h, zero_mul]
  · rw [← FsLA.leadMinorE_full, ← FsLA.leadMinorE_full]
    have hr := hs D.R.rS (Nat.le_succ _)
    have hr1 := hs (D.R.rS + 1) le_rfl
    apply mul_right_cancel₀ (mul_ne_zero hr hr1)
    linear_combination hcross

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.L2.SG.RowsConc
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGCut in
theorem stepNormOneG_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepNormOneG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV D X Y u u t hr
    show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt D X Y u u t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, hGv, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hun := hrow.2.1.2.1
  have hz := hrow.2.1.2.2.1.1
  have hX := hrow.2.2
  have hz' := hP.1.1
  have hX' := hP.2.2.2
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := PtPf.frame_mem _ hz hX
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := PtPf.frame_mem _ hz' hX'
  rw [← hpt]
  show 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) ∧
    1 ≤ NDPt D.host.rdE (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm))
  have hlead : ∀ q, q ≤ D.R.rS + 1 → ∃ o ∈ dI D ^ (q * (2 * D.R.rS + 1 - q)),
      (o : D.host.E) = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) q := fun q hq => by
    obtain ⟨o, ho, e⟩ := lead_mem hun (lf D (X.Fu u)) F' hz hX hz' hX' q hq
    exact ⟨o, ho, e.trans (lead_cell _ _ hcell q).symm⟩
  constructor
  · have hGeq := gpt_eq (T := Tu D u) (T' := Tu D u) (lf D (X.Fu u)) F' _ hcell
    obtain ⟨o1, ho1, e1⟩ := hlead (D.R.rS + 1) le_rfl
    obtain ⟨o0, ho0, e0⟩ := hlead D.R.rS (Nat.le_succ _)
    obtain ⟨o1', ho1', e1'⟩ := star_mem_pow _ o1 ho1
    obtain ⟨o0', ho0', e0'⟩ := star_mem_pow _ o0 ho0
    have ex1 : (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) + (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - (D.R.rS + 1) = D.R.rS by omega]; ring
    have ex0 : D.R.rS * (2 * D.R.rS + 1 - D.R.rS) + D.R.rS * (2 * D.R.rS + 1 - D.R.rS) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - D.R.rS = D.R.rS + 1 by omega]; ring
    have hm1 : o1 * o1' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex1, pow_add]; exact Ideal.mul_mem_mul ho1 ho1'
    have hm0 : o0 * o0' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex0, pow_add]; exact Ideal.mul_mem_mul ho0 ho0'
    refine one_le_NGPt _ _ (o1 * o1' - (((Tu D u : ℕ) * (Tu D u : ℕ) : ℕ) : 𝓞 D.host.E) * (o0 * o0'))
      (Ideal.sub_mem _ hm1 (Ideal.mul_mem_left _ _ hm0)) ?_ (by rw [hGeq]; exact hGv)
    have e1a : algebraMap (𝓞 D.host.E) D.host.E o1 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) (D.R.rS + 1) := e1
    have e0a : algebraMap (𝓞 D.host.E) D.host.E o0 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) D.R.rS := e0
    have e1b : algebraMap (𝓞 D.host.E) D.host.E o1' = star (algebraMap (𝓞 D.host.E) D.host.E o1) := e1'
    have e0b : algebraMap (𝓞 D.host.E) D.host.E o0' = star (algebraMap (𝓞 D.host.E) D.host.E o0) := e0'
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    unfold GPt
    rw [dlast_eq, dr_eq, map_sub, map_mul, map_mul, map_mul, map_natCast, e1b, e0b, e1a, e0a]
  · refine one_le_NDPt _ fun a => ?_
    have hj : endIdx (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) a ≤ D.R.rS + 1 :=
      (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)).1.sizeUpTo_le _
    obtain ⟨o, ho, e⟩ := hlead _ hj
    have hE := PtPf.blockEndMinors_of_cell _ (PtPf.zhatOM_isIntegral _ _ hun hF hF') _ hcell
    exact ⟨o, ho, by rw [e, endMin_eq], (hE a).2⟩


open Formalism.L2.SG.TermOp.Vanish in
theorem stepNormOneG_of_leaves (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (hAt : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    Formalism.L2.SG.Pf.MainEqSteps.StepNormOneG := by
  refine stepNormOneG_of ?_ hAt
  intro D X Y u u'
  unfold Formalism.L2.SG.TermOp.KExpCut.OOVanish
  intro t ht
  exact ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht

end Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf.MainEqAna

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AnaAtG (CSt CB : ℝ) (C1 C0n A : ℕ) {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    {P : Type} [Fintype P] (B : S3.MassData P) (Ire : ℝ) : Prop :=
  ∃ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (cSt e1 : ℝ),
    Formalism.L2.SG.RealObj.NuQOK X u u νL ∧ Formalism.L2.SG.RealObj.NuQOK X u u νB ∧
    0 ≤ cSt ∧ cSt ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
    AmpVanishG Y u νL ∧
    LocalInputG (genT (Y.tO u u)) (NOfG Y u νL νB ng) C1 C0n ∧
    PN.GenMassInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 ∧
    PN.MeasureInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) cSt ∧
    PN.PointSumInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) (A * (D.R.rS + 1) ^ 2)
      (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

def StepAnalyticCG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∀ A : ℕ, ∃ CB CSt : ℝ, 0 ≤ CB ∧ 0 ≤ CSt ∧
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
        AnaAtG CSt CB C1 C0n A large₂ Y u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Ire

section Pin

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

private theorem Jw_sc_eq_smul {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (s : X.B.I.Ginf → NNReal)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1)) :
    Jw Y u u (sc s ν) w = ((s (RealObj.gamW X u u w) : NNReal) : ℝ) • Jw Y u u ν w := by
  simp only [Jw, OO, sc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
  rw [smul_comm]

theorem ampVanishG_sc (s : X.B.I.Ginf → NNReal) (hs : ∀ γ, 0 < s γ) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : AmpVanishG Y u ν) : AmpVanishG Y u (sc s ν) := by
  intro c γ ν' hJ
  refine h c γ ν' ?_
  unfold J2of at hJ ⊢
  split_ifs at hJ ⊢ with hc
  · rw [Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow] at hJ
    rcases mul_eq_zero.mp hJ with h1 | h1
    · exfalso
      have hp : (0 : ℝ) < ((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ) := hs _
      have : (0 : ℝ) < ‖((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ)‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr hp.ne') 2
      linarith
    · exact h1
  · rfl

theorem measureInputG_sc (s : X.B.I.Ginf → NNReal) (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (c : ℝ)
    (hs : ∀ γ, (s γ : ℝ) ^ 2 ≤ c) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.MeasureInput (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng) c := by
  intro γ _
  simp only [NOfG]
  unfold J2of
  split_ifs with hc
  · rw [Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact ⟨by positivity, mul_le_mul_of_nonneg_right (hs _) (by positivity)⟩
  · simp

theorem ampVanishG_of_term (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u ν (ptPN t) = 0 → (Y.tO u u).vec t = 0) : AmpVanishG Y u ν := by
  intro c γ ν' hJ
  unfold grpGC
  refine (tsum_congr fun t => ?_).trans tsum_zero
  by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | clsG Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν'}
  · rw [Set.indicator_of_mem ht]
    exact h t ht.1 (by rw [ht.2.2.1]; exact hJ)
  · simp [Set.indicator, ht]

end Pin

def StepTermVanishG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ ν, Pinned X u u ν → ∀ t ∈ (Y.tO u u).genSet, J2of Y u u ν (ptPN t) = 0 → (Y.tO u u).vec t = 0

def StepLocGenPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ (s : X.B.I.Ginf → NNReal) (ng : PN.Pts D.host.E D.R.rS → ℝ) (e1 : ℝ),
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
        LocalInputG (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng) C1 C0n ∧
        PN.GenMassInput (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng)
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA) e1

end Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqAna

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UUE_eq_Asp {D : D7} {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : Submodule.IsFullLattice D.host.E Λ) (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (hL : IsLift Λ F) (hL' : IsLift Λ F') : UUE Λ F F' = Asp F.fl F'.fl := by
  refine le_antisymm ?_ ?_
  · have hX' : F'.fl.X ≤ Asp F.fl F'.fl := by rw [← Asp_symm]; exact X_le_Asp F'.fl F.fl
    have hz' : F'.fl.z ∈ Asp F.fl F'.fl := by rw [← Asp_symm]; exact z_mem_Asp F'.fl F.fl
    have key : UU Λ F F' ≤ (Asp F.fl F'.fl).restrictScalars (𝓞 D.host.E) := by
      unfold UU
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro y hy
        exact X_le_Asp F.fl F'.fl (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL.2]
        exact z_mem_Asp F.fl F'.fl
      · intro y hy
        exact hX' (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL'.2]
        exact hz'
    unfold UUE spanE
    rw [Submodule.span_le]
    intro x hx
    exact key hx
  · rw [Asp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL' i

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end
