module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVSDBwdHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OneMemOev
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FixedMemRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem zu_orth_X (y : (VS D).V) (hy : y ∈ (X.Fu u').X) : (VS D).hT y (X.zu u') = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [← X.flagZVector u']
    exact (X.Fu u').z_orth a
  | zero => simp
  | add x y _ _ h1 h2 => simp [h1, h2]
  | smul c x _ h => simp [h]

theorem glob_prim (g : X.B.I.E) (hg : g • crdOf X.B.I X.ιE X.bas (X.zu u') ∈ X.B.I.L) : IsIntegral ℤ g := by
  have hL0 : X.ιE g • X.zu u' ∈ (VS D).L0 := by
    have h := (X.L_eq _).1 hg
    have e : (∑ i, X.ιE ((g • crdOf X.B.I X.ιE X.bas (X.zu u')) i) • X.bas i) = X.ιE g • X.zu u' := by
      simp only [Pi.smul_apply, smul_eq_mul, crdOf, map_mul, RingEquiv.apply_symm_apply, mul_smul]
      rw [← Finset.smul_sum, X.bas.sum_repr]
    rwa [e] at h
  have horth : X.ιE g • X.zu u' ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u').X := by
    simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker, map_smul, smul_eq_mul]
    intro x hx
    rw [zu_orth_X X u' x hx, mul_zero]
  obtain ⟨o, ho⟩ := (X.Fu_fixed u').2.2.2.2 (X.ιE g) (by
    change X.ιE g • (X.Fu u').z ∈ _
    rw [X.flagZVector u']
    unfold Formalism.MainNotions.S.Lat.Lsub Formalism.MainNotions.S.Lat.Lrep
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hL0, horth⟩), horth⟩)
  have e : g = X.ιE.symm (o : D.host.E) := by rw [ho, RingEquiv.symm_apply_apply]
  rw [e]
  exact (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom

theorem yTup_zi (v : PlX X) :
    yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas (X.zu u')) := by
  have hs : scl X v (zi (D := D)) = 1 := by
    simp only [scl, zi, Fin.append_left]; exact alp_last v D.R.rS
  have h1 : yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (tupH (frameOf X u') (zi (D := D))) := by
    funext i
    change sc (E := X.B.I.E) v (scl X v (zi (D := D))) * _ = _
    rw [hs]
    simp only [sc, ← Algebra.TensorProduct.one_def, one_mul]
    rfl
  have h2 : hv X u' (zi (D := D)) = X.zu u' := by simp only [hv, zi, Fin.append_left, Fin.snoc_last]
  rw [h1, tupH_eq, h2]

theorem omVZPrim_holds : OmVZPrim X u' := by
  intro v _ c hc
  set z := crdOf X.B.I X.ιE X.bas (X.zu u') with hz_def
  have hz : z ∈ abelian₂ X := crdOf_mem X (frame_vector_mem_base_lattice X u')
  rw [yTup_zi] at hc
  obtain ⟨c', w, hw, hcw⟩ := approx v 1 one_ne_zero c
  have hw' : c - inclR (F := X.B.I.F) (Fv X.B.I.F v) c' = w := by rw [hcw]; simp
  have h1 : ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
    have e : ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z) =
        c • ratV (F := X.B.I.F) (Fv X.B.I.F v) z - w • ratV (F := X.B.I.F) (Fv X.B.I.F v) z := by
      funext i
      simp only [ratV, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul]
      rw [← hw']; ring
    rw [e]
    exact Submodule.sub_mem _ hc (lat_oev_smul X v hw (Submodule.subset_span ⟨z, hz, rfl⟩))
  have hpair : ∀ l ∈ X.B.I.L, inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    have h2 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) =
        hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
          (ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z)) :=
      (hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![l, c' • z] 0 1).symm
    rw [h2]
    exact omVSD_fwd X v (Submodule.subset_span ⟨l, hl, rfl⟩) h1
  obtain ⟨t, ht, htL⟩ := locGlob X v _ hpair
  have hg : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c') :=
    glob_prim X u' _ (by rw [mul_smul]; exact htL)
  obtain ⟨hinv, hne⟩ := unit_of_notMem v t ht
  have hc' : inclR (F := X.B.I.F) (Fv X.B.I.F v) c' ∈ OEv (E := X.B.I.E) v := by
    have e : inclR (F := X.B.I.F) (Fv X.B.I.F v) c' =
        (⟨(algebraMap X.B.I.F (Fv X.B.I.F v) (t : X.B.I.F))⁻¹, hinv⟩ : v.adicCompletionIntegers X.B.I.F) •
          inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c') := by
      show inclR (F := X.B.I.F) (Fv X.B.I.F v) c' = (algebraMap X.B.I.F (Fv X.B.I.F v) (t : X.B.I.F))⁻¹ •
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c')
      rw [map_mul, ← alg_alg, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (incl_mem v (⟨_, (mem_integralClosure_iff ℤ _).2 hg⟩ : 𝓞 X.B.I.E))
  have e2 : c = w + inclR (F := X.B.I.F) (Fv X.B.I.F v) c' := by rw [← hw']; ring
  rw [e2]
  exact Submodule.add_mem _ hw hc'

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

def OmVDdLoc : Prop :=
  ∀ (v : PlX X) (a : Fin D.R.rS),
    (∀ x ∈ (aaD D a)⁻¹, sc (E := X.B.I.E) v (alp v D.R.rS a.castSucc) *
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v) ∧
    (∀ x ∈ aaD D a, sc (E := X.B.I.E) v (alp v D.R.rS a.castSucc)⁻¹ *
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v)

def Pm (v : PlX X) (c : Fv X.B.I.F v) (w : (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {y | sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((VS D).hT w y)) ∈
    OEv (E := X.B.I.E) v}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro y y' hy hy'
    simp only [Set.mem_ofPred_eq, map_add (f := _), mul_add] at *
    exact Submodule.add_mem _ hy hy'
  smul_mem' := by
    intro o y hy
    simp only [Set.mem_ofPred_eq] at *
    rw [← algebraMap_smul D.host.E o y, map_smul, smul_eq_mul, map_mul, map_mul, mul_left_comm]
    exact oev_mul v (incl_mem v (⟨X.ιE.symm (o : D.host.E),
      (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E)) hy

theorem pm_iff (v : PlX X) (c : Fv X.B.I.F v) (w y : (VS D).V) : y ∈ Pm X v c w ↔
    sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((VS D).hT w y)) ∈ OEv (E := X.B.I.E) v :=
  Iff.rfl

theorem pm_zero (v : PlX X) (c : Fv X.B.I.F v) (w y : (VS D).V) (h : (VS D).hT w y = 0) : y ∈ Pm X v c w := by
  rw [pm_iff, h, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _

theorem hT_smul_right (w y : (VS D).V) (x : D.host.E) : (VS D).hT w (x • y) = x * (VS D).hT w y := by
  rw [map_smul, smul_eq_mul]

theorem base_lattice_le_first_isotropic (hD : OmVDdLoc X) (v : PlX X) (a : Fin D.R.rS) :
    (VS D).L0 ≤ Pm X v (alp v D.R.rS a.castSucc) (X.eX a) := by
  rw [X.Lam_split]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, _, rfl⟩
    exact pm_zero X v _ _ _ (by rw [hT_smul_right, X.ee, mul_zero])
  · intro y hy
    exact pm_zero X v _ _ _ (X.Lb_perp y hy a).1
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, hx, rfl⟩
    refine (pm_iff X v _ _ _).2 ?_
    rw [hT_smul_right, X.ef]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, mul_one]; exact (hD v a).1 x hx
    · rw [if_neg hab, mul_zero, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _

theorem base_lattice_le_second_isotropic (hD : OmVDdLoc X) (v : PlX X) (a : Fin D.R.rS) :
    (VS D).L0 ≤ Pm X v (alp v D.R.rS a.castSucc)⁻¹ (X.fY a) := by
  rw [X.Lam_split]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, hx, rfl⟩
    refine (pm_iff X v _ _ _).2 ?_
    rw [hT_smul_right, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
    by_cases hab : b = a
    · subst hab; rw [if_pos rfl, map_one, mul_one]; exact (hD v b).2 x hx
    · rw [if_neg hab, map_zero, mul_zero, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _
  · intro y hy
    exact pm_zero X v _ _ _ (X.Lb_perp y hy a).2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, _, rfl⟩
    exact pm_zero X v _ _ _ (by rw [hT_smul_right, X.ff, mul_zero])

theorem crd_of_L (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L) :
    ∃ y ∈ (VS D).L0, crdOf X.B.I X.ιE X.bas y = l := by
  refine ⟨∑ i, X.ιE (l i) • X.bas i, (X.L_eq l).1 hl, ?_⟩
  funext j
  have h : X.bas.repr (∑ i, X.ιE (l i) • X.bas i) j = X.ιE (l j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [crdOf]
  rw [h, RingEquiv.symm_apply_apply]

theorem hform_star (l x : Fin X.B.I.n → X.B.I.E) :
    star (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x l := by
  have herm_entry : ∀ i j, star (X.B.I.J i j) = X.B.I.J j i := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm j) i
    simpa [Formalism.UG.IsHerm, Formalism.UG.cT, starRingEnd_apply] using this
  unfold Formalism.UG.hform
  rw [Finset.sum_comm, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [starRingEnd_apply, star_mul, star_star]
  rw [herm_entry]
  ring

theorem pair_mem (v : PlX X) (s : Fv X.B.I.F v) (w : (VS D).V) (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L)
    (hP : (VS D).L0 ≤ Pm X v s w) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
      (sc (E := X.B.I.E) v s • ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas w)) ∈ OEv (E := X.B.I.E) v := by
  obtain ⟨y, hy, rfl⟩ := crd_of_L X l hl
  rw [hR_smulE_right]
  have h1 : hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas y))
      (ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas w)) =
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas y) (crdOf X.B.I X.ιE X.bas w)) :=
    hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![crdOf X.B.I X.ιE X.bas y, crdOf X.B.I X.ιE X.bas w] 0 1
  have h2 : hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas y) (crdOf X.B.I X.ιE X.bas w) =
      X.B.I.cm.sig (X.ιE.symm ((VS D).hT w y)) := by
    rw [← hE_crdOf]
    exact (hform_star X _ _).symm
  rw [h1, h2, ← sigR_inclR]
  have hsc : sc (E := X.B.I.E) v s = sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc (E := X.B.I.E) v s) :=
    (sigR_tmul_one (Fv X.B.I.F v) X.B.I.cm.sig s).symm
  rw [hsc, ← map_mul]
  exact sigR_oev X.B.I.cm.sig v ((pm_iff X v s w y).1 (hP hy))

theorem yTup_eq (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) :
    yTup X u' v i = sc (E := X.B.I.E) v (scl X v i) •
      ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas (hv X u' i)) := by
  rw [← tupH_eq]; rfl

theorem omVMemEF_of (hD : OmVDdLoc X) : OmVMemEF X u' := by
  intro v i hi
  have hpair : ∀ l ∈ X.B.I.L, hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
      (yTup X u' v i) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    rw [yTup_eq]
    refine Fin.addCases (fun j hj => ?_) (fun b _ => ?_) i hi
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
      · have hs : scl X v (Fin.castAdd D.R.rS a.castSucc) = alp v D.R.rS a.castSucc := by
          simp only [scl, Fin.append_left]
        have hw : hv X u' (Fin.castAdd D.R.rS a.castSucc) = X.eX a := by
          simp only [hv, Fin.append_left, Fin.snoc_castSucc]
        rw [hs, hw]
        exact pair_mem X v _ _ l hl (base_lattice_le_first_isotropic X hD v a)
      · exact absurd rfl hj
    · have hs : scl X v (Fin.natAdd (D.R.rS + 1) b) = (alp v D.R.rS b.castSucc)⁻¹ := by
        simp only [scl, Fin.append_right]
      have hw : hv X u' (Fin.natAdd (D.R.rS + 1) b) = X.fY b := by
        simp only [hv, Fin.append_right]
      rw [hs, hw]
      exact pair_mem X v _ _ l hl (base_lattice_le_second_isotropic X hD v b)
  refine ((omVSD_of X (omVSDBwd_holds X)) v _).2 fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact hpair l hl
  | zero => rw [OmW.hR_zero_left]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [OmW.hR_add_left]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ((c : Fv X.B.I.F v) • x) _ ∈ _
    rw [OmW.hR_smul_left]; exact oev_smul v h

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix

theorem fFInertB_holds : PI.OmVd.FFInertB := by
  intro k K _ _ _ _ σ hσ h2 hne M a haM J hJ hdJ T hT hTu
  classical
  obtain ⟨i₀, hr, hc, hu⟩ := hTu
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := i₀.pos; omega⟩
  have := Fintype.ofFinite k
  have : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  have : Finite K := Module.finite_of_finite k
  have := Fintype.ofFinite K
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have hJ' : ∀ i j, (σ : K →+* K) (J j i) = J i j := hJ
  have hu0 : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det := by
    have e := det_corOne T i₀ hr 1
    rw [one_mul] at e
    rw [← e]; exact hu
  have hTt : ∀ c : k, c ≠ 0 →
      (∀ i j, σ ((T + Matrix.single i₀ i₀ (algebraMap k K c)) j i) =
        (T + Matrix.single i₀ i₀ (algebraMap k K c)) i j) ∧
      IsUnit (T + Matrix.single i₀ i₀ (algebraMap k K c)).det := by
    intro c hc0
    refine ⟨fun i j => ?_, ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, map_add (f := _), hT, Matrix.single_apply, Matrix.single_apply]
      congr 1
      split_ifs with h1 h2 h2 <;> first | exact AlgEquiv.commutes σ c | exact map_zero σ | (exfalso; tauto)
    · rw [det_corOne T i₀ hr]
      exact (isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hc0)).mul hu0
  have hN : ∀ c : k, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K //
      ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K c)} =
      Nat.card {X : Fin (a' + 1) → Fin M → K //
        ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K 1)} := by
    intro c hc0
    have e1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt c hc0).1 (hTt c hc0).2
    have e2 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
      (hTt 1 one_ne_zero).2
    exact_mod_cast e1.trans e2.symm
  have hD : ∀ Y : Fin a' → Fin M → K, ffGram (σ : K →+* K) J Y = T.submatrix i₀.succAbove i₀.succAbove →
      Nat.card {x : Fin M → K // (∀ j, ffH (σ : K →+* K) J (Y j) x = 0) ∧ ffH (σ : K →+* K) J x x = 0 ∧
        ¬ ∀ c : K, c • x = 0 → c = 0} = 1 := by
    intro Y _
    rw [Nat.card_eq_one_iff_unique]
    have h0 : ∀ z : Fin M → K, ¬ (∀ c : K, c • z = 0 → c = 0) → z = 0 := fun z hz => by
      by_contra h0
      exact hz (fun c hc => (smul_eq_zero.1 hc).resolve_right h0)
    refine ⟨⟨fun x y => Subtype.ext ((h0 x.1 x.2.2.2).trans (h0 y.1 y.2.2.2).symm)⟩, ⟨⟨0, ?_⟩⟩⟩
    exact ⟨fun j => ffH_zero_right _ _ _, ffH_zero_left _ _ _, fun h => one_ne_zero (h 1 (smul_zero 1))⟩
  have hcnt := count_gen (σ : K →+* K) J hσ' hJ' T i₀ hr hc hu (by omega) (ι := algebraMap k K)
    (algebraMap k K).injective (map_zero _)
    (fun x => fixed_mem_range σ h2 hne _ (ffH_herm (σ : K →+* K) J hσ' hJ' x x).symm) _ 1 hN hD
  have hF0 := fFInert2_holds k K σ hσ h2 hne M a' (by omega) J hJ hdJ
    (T.submatrix i₀.succAbove i₀.succAbove) (fun i j => hT _ _) hu0
  have hN1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
    (hTt 1 one_ne_zero).2
  have h1k : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hKk : Nat.card K = Nat.card k ^ 2 := by simp only [Nat.card_eq_fintype_card]; exact hK
  rw [hKk] at hcnt
  have hR := congrArg (fun n : ℕ => (n : ℝ)) hcnt
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h1k, Nat.cast_one] at hR
  rw [hF0, hN1] at hR
  have hx : (Nat.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [prodInert_closed _ hx M a' (by omega), prodInert_closed _ hx M (a' + 1) haM] at hR
  obtain ⟨n, hn⟩ : ∃ n, M = a' + 1 + n := ⟨M - (a' + 1), by omega⟩
  have eE : 2 * M * (a' + 1) - (a' + 1) ^ 2 = (2 * M * a' - a' ^ 2) + (2 * n + 1) := by
    subst hn
    have h3 : a' ^ 2 ≤ 2 * (a' + 1 + n) * a' := by nlinarith
    have h4 : (a' + 1) ^ 2 ≤ 2 * (a' + 1 + n) * (a' + 1) := by nlinarith
    zify [h3, h4]
    ring
  have i1 : Finset.Icc (M - (a' + 1) + 1) M = insert (n + 1) (Finset.Icc (n + 2) M) := by
    rw [show M - (a' + 1) + 1 = n + 1 by omega]
    exact (Finset.insert_Icc_add_one_left_eq_Icc (by omega)).symm
  have i0 : Finset.Icc (M - (a' + 1)) M = insert n (insert (n + 1) (Finset.Icc (n + 2) M)) := by
    rw [show M - (a' + 1) = n by omega, ← Finset.insert_Icc_add_one_left_eq_Icc (show n ≤ M by omega),
      ← Finset.insert_Icc_add_one_left_eq_Icc (show n + 1 ≤ M by omega)]
    rfl
  rw [show M - a' + 1 = n + 2 by omega, show M - a' = n + 1 by omega, eE, pow_add, i1,
    Finset.prod_insert (by simp)] at hR
  rw [eE, pow_add, i0, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  set P0 := ∏ j ∈ Finset.Icc (n + 2) M, (1 - (-1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))
  set x := (Nat.card k : ℝ)
  set E0 := 2 * M * a' - a' ^ 2
  linear_combination hR + (x ^ E0 * P0) * keyInert x hx n

end PI.OmVe
end
end
