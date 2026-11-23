module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubS
public import Formalism.PeriodIntegrals.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle014
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepSection_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSection := by
  intro D X u u' sc hsc
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  let i0 : Fin D.R.k := ⟨0, hk⟩
  choose w Fw using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u v
  choose w' Fw' using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u' v
  have hdim : ∀ v, X.B.I.n = 2 * D.R.rS + 1 + D.R.k := fun v => (ProductExactness.frameLoc_X X u u v).dim
  have hT : 0 < Tw (D := D) u := ProductExactness.Tw_pos u
  have hT' : 0 < Tw (D := D) u' := ProductExactness.Tw_pos u'
  refine ⟨fun c v => secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 (c v), ?_, ?_⟩
  · exact Measurable.of_eval fun v => (measurable_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0).comp
      (measurable_pi_apply v)
  · intro c hc v
    have hcv := hc v
    have hg := ProductExactness.normSq_last_sub_pos_of_Gv_diagonal_pos (Tw (D := D) u) (Tw (D := D) u') (c v) hcv.2
    exact zhat_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 hcv.1 hg

end Formalism.L2.S.Pv.SecW
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.S.Pv.HaarSubS

theorem hform_crdX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  unfold Formalism.UG.hform crdOf

  simp only [map_sum, map_mul, X.ιE_conj, X.J_eq, RingEquiv.apply_symm_apply, LinearMap.map_smulₛₗ,
  LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
  have hst : ∀ x : D.host.E, star x = D.host.conj x := fun x => Formalism.MainNotions.S.Inh.tie_star D x
  simp only [hst]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_eqX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w) =
      X.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdX X v w, RingEquiv.symm_apply_apply]

theorem frameRelX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    PI.NMeasInv.FrameRel X.B.I X.eR X.fR (X.zR u) := by
  have h : ∀ v w, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) =
      X.ιE.symm ((VS D).hT v w) := fun v w => hform_eqX X v w
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.eR Formalism.L2.SG.HidaSetting.HidaSetting.fR Formalism.L2.SG.HidaSetting.HidaSetting.zR
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [h, X.ee, map_zero]
  · rw [h, X.ff, map_zero]
  · rw [h, X.ef]
    split_ifs <;> simp
  · rw [h, (X.zu_orth u a).1, map_zero]
  · rw [h, (X.zu_orth u a).2, map_zero]
  · rw [h, X.zu_norm, map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact (D.mem u).A.T_prime.ne_zero

theorem measN_holds : MeasN := by
  obtain ⟨h1, h2, h3, h4⟩ := PI.n_measure_invariant
  intro D X u
  have hF := frameRelX X u
  have hμ : PI.NMeasInv.IsHaarOnSet X.B.I (PI.NMeasInv.Ninf X.B.I X.eR (X.zR u)) (X.muN u) := X.muN_haar u
  exact ⟨h1 _ _ _ _ _ hF _ hμ, h2 _ _ _ _ _ hF _ hμ, h3 _ _ _ _ _ hF _ hμ, h4 _ _ _ _ _ hF _ hμ⟩

theorem nuQSFinite_holds : NuQSFinite := by
  intro D X u
  haveI : SigmaFinite (X.nuQ u) :=
    quotient_sigma_finite X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ _ (X.muN u) (X.muH u) (X.nuQ u)
      (X.muN_haar u) (X.muH_haar u) (X.nuQ_weil u)
  infer_instance

theorem stepSubG_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSubG := stepSubG_of_MN measN_holds nuQSFinite_holds

end Formalism.L2.S.Pv.HaarSubS
end
end
