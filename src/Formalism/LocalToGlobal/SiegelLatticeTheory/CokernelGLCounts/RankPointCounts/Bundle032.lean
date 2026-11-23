module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfJ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle032
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClmEqZeroOfSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SubOneMulVecFix
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
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

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}

theorem LprExistB_equiv {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) :
    Equivalence (Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ) :=
  Formalism.L2.SG.Corank.scalarEquiv_of_G scalar_equiv_general u u' F0 Λ hΛ

theorem LprExistB_repFree : Formalism.L2.SG.Corank.ScalarRepFree D u u' :=
  scalar_rep_free D u u'

theorem scal_move {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ)
    (x1 x2 y1 y2 : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0})
    (h1 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y1.1)
    (h2 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y2.1)
    (a : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 x2) : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y1 y2 := by
  have hEq := LprExistB_equiv (u := u) (u' := u') hΛ
  have hRF := LprExistB_repFree (D := D) (u := u) (u' := u') F0 Λ hΛ
  have r2 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 y2.1).1 h2
  have a2 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 y2 := hRF x1 x2 y2 r2 a
  have r1 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 y1.1).1 h1
  have a3 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y2 y1 := hRF y2 x1 y1 r1 (hEq.symm a2)
  exact hEq.symm a3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')

theorem GZ_eq : GZ F.fvec F'.fvec = Zhat F F' := by
  ext a b; rfl

theorem GDl_eq (l : ℕ) : GDl F.fvec F'.fvec l = Dl F F' l := by
  unfold GDl Dl leadMinorE
  rw [GZ_eq]

theorem om_X' {y : (VS D).V} (hy : y ∈ F'.X) : (VS D).hT (Gom F.fvec F'.fvec) y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy

  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, ← fvec_cs F' i, om_pair, if_neg (Fin.castSucc_ne_last i), smul_zero]

theorem omega_hermitian_z : (VS D).hT (Gom F.fvec F'.fvec) F'.z = GDl F.fvec F'.fvec (D.R.rS + 1) := by
  rw [← fvec_last F', om_pair, if_pos rfl]

theorem f_om (a : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (Gom F.fvec F'.fvec) =
      if a = Fin.last D.R.rS then star ((GZ F.fvec F'.fvec).adjugate (Fin.last _) (Fin.last _)) * -T else 0 := by
  unfold Gom

  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hff]
  rw [Finset.sum_eq_single (Fin.last D.R.rS)]
  · by_cases ha : a = Fin.last D.R.rS
    · rw [if_pos ⟨ha, rfl⟩, if_pos ha]
    · rw [if_neg (fun h => ha h.1), if_neg ha, mul_zero]
  · intro b _ hb
    rw [if_neg (fun h => hb h.2), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem om_om : (VS D).hT (Gom F.fvec F'.fvec) (Gom F.fvec F'.fvec) =
    -T * (GDl F.fvec F'.fvec D.R.rS * star (GDl F.fvec F'.fvec D.R.rS)) := by
  have e : (VS D).hT (Gom F.fvec F'.fvec) (Gom F.fvec F'.fvec) =
      ∑ a, (GZ F.fvec F'.fvec).adjugate (Fin.last _) a * (VS D).hT (F.fvec a) (Gom F.fvec F'.fvec) := by
    conv_lhs => arg 1; unfold Gom

    rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  rw [e, Finset.sum_eq_single (Fin.last D.R.rS)]
  · rw [f_om, if_pos rfl, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r']
    ring
  · intro b _ hb
    rw [f_om, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem om_uniq (hdet : GDl F.fvec F'.fvec (D.R.rS + 1) ≠ 0) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range F.fvec)) (hxX : ∀ y ∈ F'.X, (VS D).hT y x = 0) :
    ∃ c : D.host.E, x = c • Gom F.fvec F'.fvec := by
  set c : D.host.E := star ((VS D).hT x F'.z / GDl F.fvec F'.fvec (D.R.rS + 1)) with hc
  refine ⟨c, sub_eq_zero.1 (eq_zero_of_orth_of_det_ne_zero F.fvec F'.fvec hdet
    (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (Gom_mem _ _))) fun b => ?_)⟩
  rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, om_pair]
  induction b using Fin.lastCases with
  | last =>
    rw [if_pos rfl, fvec_last, hc, star_star, div_mul_cancel₀ _ hdet, sub_self]
  | cast i =>
    rw [if_neg (Fin.castSucc_ne_last i), mul_zero, sub_zero, fvec_cs, hsw',
      hxX _ (Submodule.subset_span ⟨i, rfl⟩), star_zero]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf
end
end

section

noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.Pf

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.MainNotions.BridgeLemma Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.NGDict

section HpSec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

omit [TopologicalSpace E] [MeasurableSpace E] [CommRing E] in
theorem le_mul_mul_rpow_neg_half_of_le_inv_sq {a b c q : ℝ} (hq : 0 < q) (a0 : 0 < a) (a1 : a ≤ 1) (b0 : 0 < b) (b1 : b ≤ 1)
    (c0 : 0 < c) (h : c ≤ (q ^ 2)⁻¹) : q ≤ (a * b * c) ^ (-(1 / 2 : ℝ)) := by
  have hx : a * b * c ≤ (q ^ 2)⁻¹ := by
    calc a * b * c ≤ 1 * 1 * c := by gcongr
      _ = c := by ring
      _ ≤ _ := h
  have e : ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) = q := by
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hq.le]
  calc q = ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) := e.symm
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hx (by norm_num)

theorem ends_isUnit {l : ℕ} (hl : l ∈ P.ends) : IsUnit (P.Dm l) :=
  (((@Finset.mem_filter _ _ (Classical.decPred _) _ _).1 hl).2).2

theorem residue_le_height_nonprime (hOK : M.OK) (hR : P.RelG (theta M))
    (hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) (hp : ¬ P.PrimeTo) : StepHp P := by
  obtain ⟨d, t, ht⟩ := hex
  have hG : P.Gv ≠ 0 := hR.2.2.1
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := ng_factors hOK hG ht
  have hq : (0 : ℝ) < qF F := by
    have := two_le_residue_card hOK
    exact_mod_cast (by omega : 0 < qF F)
  have hnt := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
  have hm1 : ((-1 : F) ^ (r + 1)) ∈ 𝒪[F] := pow_mem (neg_mem (one_mem _)) _
  unfold StepHp FPair.Hp
  rcases hs : M.split with _ | g
  · have hnot : ¬ IsUnitO M P.Gv ∨ ∃ l ∈ P.ends, ¬ IsUnitO M (P.Dm l) := by
      by_contra hc
      push Not at hc
      exact hp ⟨hs, hc.1, hc.2⟩
    rcases hnot with hGn | ⟨l, hl, hDn⟩
    · refine ng_real_q hq a0 a1 b0 b1 c0 c1 (Or.inr ?_)
      have hfix : M.L.cj P.Gv = P.Gv := by
        unfold FPair.Gv HermSp.Gdet HermSp.normE
        simp only [map_sub, map_mul, M.L.cj_cj, AlgEquiv.commutes]
        ring
      obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
      have hdet : (H.gram P.MMgen).det = algebraMap F E ((-1) ^ (r + 1) * a) := by
        rw [gram_det_eq P hs, ← ha, map_mul, map_pow, map_neg, map_one]
      have hmem : (H.gram P.MMgen).det ∈ M.L.O := by
        rw [← ng_term_gram ht]
        exact ng_det_mem _ (fun a b => ng_term_int ht (ng_term_MM ht _) (ng_term_MM ht _))
      have haO : (-1) ^ (r + 1) * a ∈ 𝒪[F] :=
        Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [← hdet]; exact hmem)
      have haO' : a ∈ 𝒪[F] := by
        have h2 := mul_mem hm1 haO
        have e : ((-1 : F) ^ (r + 1)) * ((-1) ^ (r + 1) * a) = a := by
          rw [← mul_assoc, ← mul_pow]; simp
        rwa [e] at h2
      have ha0 : (-1) ^ (r + 1) * a ≠ 0 := by
        refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (fun h => hG ?_)
        rw [← ha, h, map_zero]
      rw [hdet]
      refine ng_modK_nonunit hOK ⟨_, haO⟩ ha0 (fun hu => hGn ?_)
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hy' : ((-1) ^ (r + 1) * a) * (y : F) = 1 := congrArg Subtype.val hy
      refine ⟨?_, algebraMap F E ((-1) ^ (r + 1) * (y : F)), ?_, ?_⟩
      · rw [← ha]; exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨a, haO'⟩
      · exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨_, mul_mem hm1 y.2⟩
      · rw [← ha, ← map_mul]
        have : a * ((-1) ^ (r + 1) * (y : F)) = ((-1) ^ (r + 1) * a) * (y : F) := by ring
        rw [this, hy', map_one]
    · have hlu : IsUnit (P.Dm l) := ends_isUnit hl
      have hfac : ∀ l' ∈ P.ends, 0 < M.modK (P.Dm l' * M.L.cj (P.Dm l')) ∧
          M.modK (P.Dm l' * M.L.cj (P.Dm l')) ≤ 1 := by
        intro l' hl'
        have hu := ends_isUnit hl'
        have h := ng_modK hOK (hu.mul (hu.map M.L.cj))
        exact ⟨h.1, h.2 (M.L.O.mul_mem (ng_term_Dm ht l')
          (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l')))⟩
      have hcl : ∏ l' ∈ P.ends, M.modK (P.Dm l' * M.L.cj (P.Dm l')) ≤
          M.modK (P.Dm l * M.L.cj (P.Dm l)) := by
        rw [← Finset.mul_prod_erase _ _ hl]
        have h1 : ∏ x ∈ P.ends.erase l, M.modK (P.Dm x * M.L.cj (P.Dm x)) ≤ 1 :=
          Finset.prod_le_one₀ (fun x hx => (hfac x (Finset.mem_of_mem_erase hx)).1.le)
            (fun x hx => (hfac x (Finset.mem_of_mem_erase hx)).2)
        have h0 := (hfac l hl).1.le
        calc _ ≤ M.modK (P.Dm l * M.L.cj (P.Dm l)) * 1 := mul_le_mul_of_nonneg_left h1 h0
          _ = _ := mul_one _
      refine le_mul_mul_rpow_neg_half_of_le_inv_sq hq a0 a1 b0 b1 c0 (le_trans hcl ?_)
      have hfix : M.L.cj (P.Dm l * M.L.cj (P.Dm l)) = P.Dm l * M.L.cj (P.Dm l) := by
        rw [map_mul, M.L.cj_cj, mul_comm]
      obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
      have hxO : P.Dm l * M.L.cj (P.Dm l) ∈ M.L.O :=
        M.L.O.mul_mem (ng_term_Dm ht l) (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l))
      have haO : a ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [ha]; exact hxO)
      have hxu : IsUnit (P.Dm l * M.L.cj (P.Dm l)) := hlu.mul (hlu.map M.L.cj)
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [map_zero] at ha
        rw [← ha] at hxu
        exact not_isUnit_zero hxu
      rw [← ha]
      refine ng_modK_nonunit hOK ⟨a, haO⟩ ha0 (fun hu => hDn ?_)
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hy' : a * (y : F) = 1 := congrArg Subtype.val hy
      refine ⟨ng_term_Dm ht l, M.L.cj (P.Dm l) * algebraMap F E (y : F),
        M.L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l))
          (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L y), ?_⟩
      rw [← mul_assoc, ← ha, ← map_mul, hy', map_one]
  · refine ng_real_q hq a0 a1 b0 b1 c0 c1 (Or.inl ?_)
    have hθ : theta M = (g.q : F) := by
      unfold theta
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    rw [hθ]
    exact ng_modK_nonunit hOK g.q (fun h => g.q_irr.ne_zero (Subtype.ext h)) g.q_irr.not_isUnit

end HpSec

section GlueSec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

end GlueSec

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {α : Type*} {r : α → α → Prop}

theorem eqvGen_iff_of (f : α → Prop) (hf : ∀ a b, r a b → (f a ↔ f b)) {a b : α} (h : Relation.EqvGen r a b) :
    (f a ↔ f b) := by
  induction h with
  | rel x y hxy => exact hf x y hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem eqvGen_eq_of {β : Type*} (f : α → β) (hf : ∀ a b, r a b → f a = f b) {a b : α} (h : Relation.EqvGen r a b) :
    f a = f b := by
  induction h with
  | rel x y hxy => exact hf x y hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

end Gen

theorem relRepC : RelRepC := by
  intro D X Y u u' t hr hG
  have hΛ : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨hGF, -, hRF, -, -⟩ := term_function_const D u u' (X.Fu u) t.lam hΛ

  set x : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') := ⟨frq X t.rep, t.rep.2.2.2.2⟩ with hx
  have hcls : t.toTerm.cls = TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x := rfl
  constructor
  · obtain ⟨F', ⟨hP, hmk⟩, hrel⟩ := hr
    have hcls' : t.toTerm.cls = TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x := hcls
    rw [hcls'] at hmk
    have he : Relation.EqvGen (TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u')) ⟨F', hP⟩ x :=
      Quot.eqvGen_exact hmk
    exact (eqvGen_iff_of (fun y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') =>
      Relevant D.host.F (lf D (X.Fu u)).fl y.1.fl) (fun a b hab => hRF a b hab) he).1 hrel
  · have hG' : TermDef.Gt t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u')
        (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x) = 0 := hG
    unfold TermDef.Gt at hG'
    have hout := Quot.out_eq (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x)
    have he : Relation.EqvGen (TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u'))
        (Quot.out (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x)) x :=
      Quot.eqvGen_exact hout
    have := eqvGen_eq_of (fun y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') =>
      Gval (lf D (X.Fu u)) y.1) (fun a b hab => hGF a b hab) he
    rw [← this]; exact hG'

end Formalism.L2.SG.KappaOffDiagonal
end
end

section

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem schurNFC_of (hA : SchurCoreA) (hB : GeomB) : SchurNFC := by
  intro D X u u' Λ Λ' q hdiff hrel hG P hP
  obtain ⟨C, hC, hM⟩ := hB D X u u' Λ Λ' q hrel hG
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  refine hA D.R.k (InfinitePlace X.B.I.F) (X.Vloc u) (X.Vloc u') (X.Vpi u) (X.Vpi u') (X.tensU u) (X.tensU u')
    (X.tensU_inner u) (X.tensU_span u) (X.tensU_inner u') (X.tensU_span u') (X.piLoc u) (X.piLoc u')
    (fun v i => ((D.hcW u (X.pl v)).u i : ℝ)) (fun v i => ((D.hcW u' (X.pl v)).u i : ℝ))
    (fun v => X.piLoc_type u v) (fun v => X.piLoc_type u' v) v₀ (hdiff (X.pl v₀)) C hC P ?_
  intro M hMu
  obtain ⟨h, hh, h1, h2⟩ := hM M hMu
  exact ⟨X.piU u h, X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1), h1, h2, hP h hh⟩

end PI.SchurPlaces

theorem schurNFC : Formalism.L2.SG.KappaOffDiagonal.SchurNFC :=
  PI.SchurPlaces.schurNFC_of (PI.SchurPlaces.schurCoreA_of Formalism.MainNotions.BridgeLemma.schur_lemma_unitary_distinct_params)
    (PI.SchurPlaces.Geo.geomB_of PI.SchurPlaces.leviTens PI.SchurPlaces.wfrSpan PI.SchurPlaces.cplxNF)
end
end
