module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle042
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle028
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle083
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle085
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle082
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.IdxCocycle
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle086
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle067
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle065
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle061
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CjTFromBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

theorem normExpDegC_of_leaves (hFL : Formalism.L2.SG.Pf.FinLeviC) (hOL : Formalism.L2.SG.Pf.OOLintSumC) : NormExpDegC :=
  normExpDegC_of hilbert_schmidt_blocks (Formalism.L2.SG.Closed.FoldOKC_holds hFL) (Formalism.L2.SG.Closed.OOIntAllC_holds hOL)
    (Formalism.L2.SG.Closed.AbsConvC_holds hOL) Formalism.L2.SG.Closed.AmpWellDefC_holds Formalism.L2.SG.Closed.OOFundIndepC_holds
    (fun _ X => chi_n_bilinear X) (fun D X Y u _ => Formalism.L2.SG.NormCut.colFreeAll D X Y u)
    (fun D X Y u _ h1 h2 h3 =>
      Formalism.L2.SG.NormCut.degLeftAct_of_PD (fun D => Formalism.L2.SG.Pf.positive_definite_isomorphism D) D X Y u h1 h2 h3)
    (fun D X Y u _ h1 h2 h3 => Formalism.L2.SG.NormCut.degRightAct_holds D X Y u h1 h2 h3)

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem mem_stSet_of_pat (a : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a)
    (hpat : ∀ i j, Formalism.L2.SG.Pf.fσ w j < Formalism.L2.SG.Pf.fσ w i → a i j = 0) :
    ∃ b : Formalism.L2.SG.PairVal.MatR D, IsUpUni b ∧ a * ptMat w * b = ptMat w := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ x, σ (σ x) = x := Formalism.L2.SG.Pf.fσ_fσ w
  set ν : Fin (D.R.rS + 1) → D.host.E := fun x => Formalism.L2.SG.Pf.pv w.1 x
  have hν : ∀ x, IsUnit (ν x) := fun x => isUnit_iff_ne_zero.2 (Formalism.L2.SG.Pf.pv_ne' w x)
  have hfix := fix_cOf hσ ν hν a
  obtain ⟨hc1, hc2⟩ := cOf_up hσ ν a (fun i => (ha i i).2 rfl) hpat hν
  have hcU : IsUpUni (cOf σ ν a) := fun i j => ⟨fun h => hc2 i j h, fun h => by subst h; exact hc1 i⟩
  obtain ⟨hbU, -, hcb⟩ := ZsVolGrp.isUpUni_inv hcU
  refine ⟨(cOf σ ν a)⁻¹, hbU, ?_⟩
  rw [ptMat_mono, hfix, Matrix.mul_assoc, hcb, Matrix.mul_one]

theorem approx_core (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (S : Finset (PlF D))
    (hS : ∀ p, p ∉ S → ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
      (∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O) →
        ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p)
    (h : ∀ p, ProdE.StP M δ u u' w p) :
    ∃ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
      (∀ p ∈ S, (h p)⁻¹ * ProdE.πP M δ u u' w (hA p) g ∈
        ProdE.AP M δ u u' w p ⊓ ProdE.CPL M δ u u' w (hA p) L U hL hU) ∧
      ∀ p, p ∉ S → ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p := by
  classical
  set σ := Formalism.L2.SG.Pf.fσ w with hσd
  choose c hc0 hcO hcong using fun p => cong_at M δ u u' w (hA p) L U hL hU
  choose τ hτ1 hτ2 hτ3 c' hc'0 hc'O hcl using fun p => close_at M δ u u' w (hA p) (h p) (c p) (hc0 p) (hcO p)
  choose t ht1 ht2 using fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
    sa_lat (fun p => D.s.atP p) S (fun p => τ p ij.1 ij.2) c' (fun p _ => hc'0 p)
  set a : Formalism.L2.SG.PairVal.MatR D := fun i j =>
    if j < i ∧ σ i < σ j then t (i, j) else (1 : Formalism.L2.SG.PairVal.MatR D) i j with had
  have ha : IsLoUni a := by
    intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · have : ¬ (j < i ∧ σ i < σ j) := fun h' => absurd h'.1 (not_lt.2 hij.le)
      simp only [had, if_neg this]
      exact Matrix.one_apply_ne (ne_of_lt hij)
    · subst hij
      have : ¬ (i < i ∧ σ i < σ i) := fun h' => lt_irrefl _ h'.1
      simp only [had, if_neg this, Matrix.one_apply_eq]
  have hpat : ∀ i j, σ j < σ i → a i j = 0 := by
    intro i j hij
    have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    have : ¬ (j < i ∧ σ i < σ j) := fun h' => absurd h'.2 (not_lt.2 hij.le)
    simp only [had, if_neg this]
    exact Matrix.one_apply_ne hne
  have hdet : IsUnit a.det := by rw [ZsVolGrp.det_lo (fun x => (ha x x).2 rfl) (fun x y hxy => (ha x y).1 hxy)]; exact isUnit_one
  obtain ⟨b, hb, hab⟩ := mem_stSet_of_pat w a ha hpat
  let gGL : Formalism.L2.SG.PairVal.GLR D := Matrix.nonsingInvUnit a hdet
  have hgv : (gGL : Formalism.L2.SG.PairVal.MatR D) = a := rfl
  let g : Formalism.L2.SG.Pf.VolPinAsm.StG w := ⟨gGL, ⟨by rw [hgv]; exact ha, b, hb, by rw [hgv]; exact hab⟩⟩
  have hgv' : ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = a := rfl
  refine ⟨g, fun p hp => ?_, fun p hp => hS p hp g ?_⟩
  · have hclose : EntIn (latS (D.s.atP p) (c' p))
        (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE - τ p) := by
      intro i j
      rw [hgv', Matrix.sub_apply, Matrix.map_apply]
      by_cases hz : j < i ∧ σ i < σ j
      · simp only [had, if_pos hz]
        exact mem_latS.2 (ht1 (i, j) p hp)
      · simp only [had, if_neg hz]
        have e : (D.s.atP p).ιE ((1 : Formalism.L2.SG.PairVal.MatR D) i j) - τ p i j = 0 := by
          rcases lt_trichotomy i j with hij | hij | hij
          · rw [Matrix.one_apply_ne (ne_of_lt hij), map_zero, hτ1 p i j hij, sub_zero]
          · subst hij; rw [Matrix.one_apply_eq, map_one, hτ2 p i, sub_self]
          · have hs : σ j < σ i := by
              rcases lt_or_gt_of_ne (fun e : σ i = σ j => (ne_of_gt hij) (by
                rw [← Formalism.L2.SG.Pf.fσ_fσ w i, ← Formalism.L2.SG.Pf.fσ_fσ w j]; exact congrArg _ e)) with h' | h'
              · exact absurd ⟨hij, h'⟩ hz
              · exact h'
            rw [Matrix.one_apply_ne (ne_of_gt hij), map_zero, hτ3 p i j hs, sub_zero]
        rw [e]; exact (latS (D.s.atP p) (c' p)).zero_mem
    obtain ⟨h1, h2⟩ := hcl p g hclose
    exact hcong p _ h1 h2
  · intro i j
    rw [hgv']
    by_cases hz : j < i ∧ σ i < σ j
    · simp only [had, if_pos hz]
      exact ht2 (i, j) p hp
    · simp only [had, if_neg hz]
      rw [Matrix.one_apply]
      split_ifs
      · rw [map_one]; exact (D.s.atP p).O.one_mem
      · rw [map_zero]; exact (D.s.atP p).O.zero_mem

end Main

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section

noncomputable section

open Matrix ValuativeRel
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents



variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem e_alg (p : PlF D) (g : Loc.SplitG (M p).L) (x : (D.s.atP p).Fp) :
    g.e (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep x) = (x, x) := by
  rw [AlgEquiv.commutes]; rfl

theorem gaCong_G (hA : ∀ q, Agree δ M q) (p : PlF D) (g : Loc.SplitG (M p).L) (hs : (M p).split = some g)
    (T T' : D.host.E) (Tf Tf' : (D.s.atP p).Fp) (Z Z' : MatZ D)
    (L P : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)
    (hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0)
    (hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0)
    (hLR : ∀ i j, L i j ∈ (M p).R) (hPR : ∀ i j, P i j ∈ (M p).R)
    (hLu : ∃ y ∈ (M p).R, L.det * y = 1) (hPu : ∃ y ∈ (M p).R, P.det * y = 1)
    (hX : Loc.HermSp.ZZplusOf (M p) (ZhatLoc M δ p Z') Tf Tf' =
      L * Loc.HermSp.ZZplusOf (M p) (ZhatLoc M δ p Z) Tf Tf' * P) :
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      GaPlus M δ p T T' Z' = (A.map (M p).L.cj).transpose * GaPlus M δ p T T' Z * A := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) with hcj
  have hinv : ∀ x, cj (cj x) = x := fun x => (M p).L.cj_cj x
  set Mm := mmG (M p) g L P with hMm
  set U := uuG (M p) g L P with hU
  set qi : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) with hqi
  set A0 : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.fromBlocks 1 (-qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) 0
      (qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) with hA0
  set B : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.fromBlocks Mm (qi • (U - Mm)) 0 U with hB
  set At : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.fromBlocks Mm 0 0 U with hAt
  have hplus : ∀ Y : MatZ D, GaPlus M δ p T T' Y = cjT cj A0 * GaLoc M δ p T T' Y * A0 := by
    intro Y; unfold GaPlus; rw [hs]; rfl
  have hloc : GaLoc M δ p T T' Z' = cjT cj At * GaLoc M δ p T T' Z * At := by
    rw [gaLoc_blocks δ M hA, gaLoc_blocks δ M hA]
    refine (block_cong cj hinv _ _ _ _ _ _ _ _ ?_ ?_ ?_).symm
    · rw [gDiag_corner]; exact condM_G (M p) g hL hP _
    · exact condX_G (M p) g hs hL hP Tf Tf' hX
    · rw [gDiag_corner]; exact condU_G (M p) g hL hP _
  have hcomm : A0 * B = At * A0 := by
    rw [hA0, hB, hAt, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_zero] <;> module
  refine ⟨B, ?_, ?_, ?_⟩
  ·
    have hcomp : ∀ x ∈ (M p).R, (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp] ∧
        ∃ c : 𝒪[(D.s.atP p).Fp], (g.e x).1 - (g.e x).2 = (g.q : (D.s.atP p).Fp) * c :=
      fun x hx => Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.comp_of_mem_R hs hx
    have hq := q_ne (M p) g
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · refine Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ ?_ ?_
      · simp [hB, hMm, mmG, (hcomp _ (hPR i j)).2.1]
      · simp [hB, hMm, mmG, (hcomp _ (hLR j i)).1]
    · obtain ⟨-, -, c, hc⟩ := hcomp _ (hPR i j)
      obtain ⟨-, -, c', hc'⟩ := hcomp _ (hLR j i)
      refine Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ ?_ ?_
      · have : (g.e (B (Sum.inl i) (Sum.inr j))).1 = c := by
          simp only [hB, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul,
            map_sub, hqi, e_alg, hU, hMm, uuG, mmG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Prod.fst_mul,
            Prod.fst_sub]
          rw [hc]; field_simp
        rw [this]; exact c.2
      · have : (g.e (B (Sum.inl i) (Sum.inr j))).2 = -c' := by
          simp only [hB, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul,
            map_sub, hqi, e_alg, hU, hMm, uuG, mmG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Prod.snd_mul,
            Prod.snd_sub]
          rw [show (g.e (L j i)).2 - (g.e (L j i)).1 = -((g.e (L j i)).1 - (g.e (L j i)).2) by ring, hc']
          field_simp
        rw [this]; exact (-c').2
    · simp [hB]
    · refine Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ ?_ ?_
      · simp [hB, hU, uuG, (hcomp _ (hPR i j)).1]
      · simp [hB, hU, uuG, (hcomp _ (hLR j i)).2.1]
  ·
    obtain ⟨yL, hyL, hLy⟩ := hLu
    obtain ⟨yP, hyP, hPy⟩ := hPu
    have cL := Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.comp_of_mem_R hs hyL
    have cP := Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.comp_of_mem_R hs hyP
    refine ⟨g.e.symm ((g.e yP).2 * (g.e yP).1, (g.e yL).1 * (g.e yL).2),
      Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ (by simpa using mul_mem cP.2.1 cP.1)
        (by simpa using mul_mem cL.1 cL.2.1), ?_⟩
    rw [hB, Matrix.det_fromBlocks_zero₂₁]
    apply g.e.injective
    have d1 : (g.e Mm.det).1 = (g.e P.det).2 := by
      have := RingHom.map_det (π1 (M p) g) Mm
      rw [π1_apply] at this
      rw [this, RingHom.mapMatrix_apply, middleMatrix_map_firstComponent, ← RingHom.mapMatrix_apply, ← RingHom.map_det, π2_apply]
    have d2 : (g.e Mm.det).2 = (g.e L.det).1 := by
      have := RingHom.map_det (π2 (M p) g) Mm
      rw [π2_apply] at this
      rw [this, RingHom.mapMatrix_apply, middleMatrix_map_secondComponent, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, π1_apply]
    have d3 : (g.e U.det).1 = (g.e P.det).1 := by
      have := RingHom.map_det (π1 (M p) g) U
      rw [π1_apply] at this
      rw [this, RingHom.mapMatrix_apply, unipotentMatrix_map_firstComponent, ← RingHom.mapMatrix_apply, ← RingHom.map_det, π1_apply]
    have d4 : (g.e U.det).2 = (g.e L.det).2 := by
      have := RingHom.map_det (π2 (M p) g) U
      rw [π2_apply] at this
      rw [this, RingHom.mapMatrix_apply, unipotentMatrix_map_secondComponent, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, π2_apply]
    have eL := congrArg g.e hLy
    have eP := congrArg g.e hPy
    rw [map_mul, map_one] at eL eP
    refine Prod.ext ?_ ?_
    · simp only [map_mul, Prod.fst_mul, AlgEquiv.apply_symm_apply, map_one, Prod.fst_one, d1, d3]
      have e1 := congrArg Prod.fst eP
      have e2 := congrArg Prod.snd eP
      simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one] at e1 e2
      linear_combination (g.e P.det).1 * (g.e yP).1 * e2 + e1
    · simp only [map_mul, Prod.snd_mul, AlgEquiv.apply_symm_apply, map_one, Prod.snd_one, d2, d4]
      have e1 := congrArg Prod.fst eL
      have e2 := congrArg Prod.snd eL
      simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one] at e1 e2
      linear_combination (g.e L.det).2 * (g.e yL).2 * e1 + e2
  ·
    show GaPlus M δ p T T' Z' = cjT cj B * GaPlus M δ p T T' Z * B
    rw [hplus, hplus, hloc]
    calc cjT cj A0 * (cjT cj At * GaLoc M δ p T T' Z * At) * A0
        = cjT cj (At * A0) * GaLoc M δ p T T' Z * (At * A0) := by
          rw [cjT_mul]; simp only [Matrix.mul_assoc]
      _ = cjT cj (A0 * B) * GaLoc M δ p T T' Z * (A0 * B) := by rw [hcomm]
      _ = cjT cj B * (cjT cj A0 * GaLoc M δ p T T' Z * A0) * B := by
          rw [cjT_mul]; simp only [Matrix.mul_assoc]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core Formalism.L2.SG.Pf.IndexCocycleOrbits

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxRatio_conj_of_unimod {G : Type} [Group G] (A B : Subgroup G) (s : G) (hBA : B ≤ A) (hf : B.relIndex A ≠ 0)
    (hU : IdxRatio A (cj s A) = 1) : IdxRatio A (cj s B) = (B.relIndex A : ℝ) := by
  rw [idxCocycle G A (cj s B) (cj s A) (cj_le hBA) (by rw [relIndex_cj]; exact hf), hU, relIndex_cj, mul_one]

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

def UnimodAt (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ s ∈ StP M δ u u' w p, IdxRatio (Ag M δ u u' (p := p) w) (cj s (Ag M δ u u' (p := p) w)) = 1

theorem locIdx_at' (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hL : IsLoUni L) (hU : IsUpUni U) (v : ℝ) (hN : CountAt M δ u u' w hA L U hL hU v)
    (hO : UnimodAt M δ u u' (p := p) w) :
    IdxRatio (AP M δ u u' w p) (CPL M δ u u' w hA L U hL hU) = v := by
  rw [idxRatio_map]
  obtain ⟨N, π, hR, hHN, hg, hBA, hfA, hv⟩ := hN
  have hC := cShape M δ u u' hA L U hL hU w
  have hCS : cj (g0 M δ hA L U hL hU) (KP M p ⊓ StabX p (XP M δ u u' w L U)) ≤ StP M δ u u' w p := by
    rw [← hC]
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  show IdxRatio (Ag M δ u u' w) (Cg M δ u u' w hA L U hL hU) = v
  rw [hC, cj_eq_cj_img hR hHN hg hCS, idxRatio_conj_of_unimod _ _ _ hBA hfA (hO _ (hR.mem _ hg)), hv]

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def StepsU : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D),
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) ∧
    UnimodAt M δ u u' (p := p) w

theorem locIdxC_of_count (h : StepsU M δ u u' F0 what₂) : LocIdxC M δ u u' F0 what₂ := by
  intro γ w F' L U hE p
  obtain ⟨hN, hO⟩ := h γ w F' L U hE p
  exact locIdx_at' M δ u u' w _ L U _ _ _ hN hO

end Formalism.L2.SG.Pf.ProdEP2Cut
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

theorem sconj_apply (ρ : MP p) (a b : Fin (D.R.rS + 1)) :
    (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      (-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
  simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem sconj_up {ρ : MP p} (h : IsUpUni ρ) :
    IsUpUni (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [sconj_apply, (h a b).1 hab]; simp
  · subst hab
    rw [sconj_apply, (h a a).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]; simp

theorem tau_second_value (x : GG p) : (((tau p x).2.unop : GLp p) : MP p) =
    Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p := rfl

theorem tau_mem_UP {x : GG p} (hx : x ∈ UP p) : tau p x ∈ UP p :=
  ⟨hx.1, by rw [tau_second_value]; exact sconj_up p hx.2⟩

theorem tau_mem_KP {x : GG p} (hx : x ∈ KP M p) : tau p x ∈ KP M p := by
  refine ⟨hx.1, ?_⟩
  show Formalism.MainNotions.S.TieN.IntUp (M p) (((tau p x).2.unop : GLp p) : MP p)
  rw [tau_second_value]
  obtain ⟨h1, h2, h3⟩ := hx.2
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [sconj_apply, h1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [sconj_apply, h2 a b hab]; simp
  · rw [sconj_apply]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _) (h3 a b))
      (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

def phi (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (Z : MP p) : MP p :=
  Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w

theorem phi_smul (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {x : GG p}
    (hx : x ∈ UP p) (Z : MP p) : phi p δ T T' w (x • Z) = tau p x • phi p δ T T' w Z := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  have hc : ((x.1 : GLp p) : MP p) * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p) =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w := by
    have hu := sconj_up p hx.2
    refine Formalism.L2.SG.Pf.FibQ.corner_fix p (fun a b h => (hx.1 a b).1 h) (fun a => (hx.1 a a).2 rfl)
      (fun a b h => (hu a b).1 h) (fun a => (hu a a).2 rfl) (fun a b h => ?_)
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Matrix.of_apply]
    rw [if_neg h]
  simp only [phi, smul_def, tau_second_value]
  show ((x.1 : GLp p) : MP p) * Z * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w =
    ((x.1 : GLp p) : MP p) * (Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w) *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p)
  rw [Matrix.mul_add, Matrix.add_mul, hc]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), hss, Matrix.one_mul]

theorem phi_inj (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {Z Z' : MP p}
    (h : phi p δ T T' w Z = phi p δ T T' w Z') : Z = Z' := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  unfold phi at h
  have h2 := add_right_cancel h
  calc Z = Z * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]
    _ = Z' * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [h2]
    _ = Z' := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]

end Formalism.L2.SG.Pf.CountAt
end
end
