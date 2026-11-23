module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAdjointScalarParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle591
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle830
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.FockWeightWedgeLowerModes
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemTensorFockOfCoeffs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ProdModeCharExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle481
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem highestWeightKernel_lowestType : AlgDatum := by
  intro n ε lam hg M _ _ E hE hU z hz0 hzp hz hcas S hSfd hSk hzS

  have hz' : IsKHWVec ε (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) (gaW ε lam) z := by
    have e : (diagE ε (eT E) cpT cmT : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))) =
        fun a b => TensorProduct.map (E a b) LinearMap.id + LinearMap.lTensor M (sgE ε cpFock cmFock a b) := by
      funext a b
      delta diagE eT
      rw [sgE_cpT]
    rw [← e]; exact hz
  obtain ⟨s, hy0, hy⟩ := khw_extract ε hg.1 hz' hz0
  set y := tcoef ((fockBasis n).coord s) z with hydef

  have hs : s ⊆ lfPhysModes ε := by
    intro m hm
    by_contra hnm
    apply hy0
    refine tco_physSub_zero hzp hm fun hp => hnm ?_
    obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
    rw [Equiv.symm_apply_apply] at hp
    exact (lf_mem_phys ε x.1 x.2).2 hp
  set Ph := gcPh ε s with hPh
  have hwt : gaW ε lam - fockWt ε s = lowK ε lam - phSum Ph := by
    rw [gc_wt_eq ε hs]
    funext a
    delta gaW lowK
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [hwt] at hy
  have hyS : y ∈ S := hzS s
  set V := kLowSpan ε E y with hV
  have hVS : V ≤ S := kLowSpan_le hSk hyS
  haveI : FiniteDimensional ℂ S := hSfd
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVS
  have hVirr : IsKIrrHW ε E (lowK ε lam - phSum Ph) V := kLowSpan_kIrrHW hE hU hy hy0 hVfd

  set T : Submodule ℂ M := LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • (1 : Module.End ℂ M)) with hT
  have hTk : IsKStableSub ε E T := by
    intro a b _ v hv
    rw [hT, LinearMap.mem_ker] at hv ⊢
    have hc := congrArg (fun X : Module.End ℂ M => X v) (casimir_comm hE a b)
    simp only [Module.End.mul_apply] at hc
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
    rw [hc, sub_eq_zero.1 hv, map_smul, sub_self]
  have hyT : y ∈ T := by
    rw [hT, LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hcas s, sub_self]
  have hVT : V ≤ T := kLowSpan_le hTk hyT
  have hVc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v := by
    intro v hv
    have := hVT hv
    rw [hT, LinearMap.mem_ker] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
    exact sub_eq_zero.1 this

  have hPh0 : Ph = ∅ := by
    by_contra hne
    exact dirac_sharp hg hE hU (gc_isPosNC ε hs) (Finset.nonempty_iff_ne_empty.2 hne) hVirr hVc
  rw [hPh0] at hVirr
  delta phSum at hVirr
  simp only [Finset.sum_empty, sub_zero] at hVirr
  refine ⟨V, hVirr, ?_, hVc⟩
  intro h0
  apply hy0
  have : y ∈ V := self_mem_kLowSpan y
  rw [h0] at this
  exact (Submodule.mem_bot ℂ).1 this

end GlobalTheory.PsCo.PcEF
end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.PsCo.Pc1 (Mat)

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem intertwiner_preserves_highestWeight : HWVec := by
  intro n ε H _ _ σ D E hσ hD Z _ hZK γ W _ _ _ T hT Φ hΦ hint
  obtain ⟨-, -, hTy⟩ := hT
  obtain ⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hTy

  have hker : LinearMap.ker Φ = ⊥ := by
    rcases hirr (LinearMap.ker Φ) le_top (fun g hg w hw => by
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hint g hg w, hw, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hΦ
  have hinj : Function.Injective Φ := LinearMap.ker_eq_bot.1 hker
  let ι : W →ₗ[ℂ] TensorProduct ℂ D (Fock n) := tsubVal Z ∘ₗ Φ
  have hιinj : Function.Injective ι := tsubVal_injective.comp hinj
  have hιK : ∀ (k : Mat n) (hk : k ∈ Kset ε) (w : W), wK hD hk (ι w) = ι (T k w) := by
    intro k hk w
    show wK hD hk (tsubVal Z (Φ w)) = tsubVal Z (Φ (T k w))
    rw [hint k (by rw [mir_Kset_eq]; exact hk) w, tOp_apply hD hZK hk]
  let S' : Submodule ℂ (TensorProduct ℂ D (Fock n)) := LinearMap.range ι
  have hS'fin : FiniteDimensional ℂ S' := LinearMap.finiteDimensional_range ι
  have hS'K : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S' := by
    rintro k hk _ ⟨w, rfl⟩
    exact ⟨T k w, (hιK k hk w).symm⟩

  have hwt : ∀ (μ : Fin n → ℝ) (w : W), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w →
      ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w := by
    intro μ w hw θ
    rw [hιK _ _ w, hw θ (by rw [mir_Kset_eq]; exact diag_mem_Kset' ε θ), map_smul]
  have hwt' : ∀ (μ : Fin n → ℝ) (w : W),
      (∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w) →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w := by
    intro μ w hw θ _
    apply hιinj
    rw [map_smul, ← hιK _ (diag_mem_Kset' ε θ) w, hw θ]
  set z := ι v with hz
  have hz0 : z ≠ 0 := fun h => hv0 (hιinj (h.trans (map_zero ι).symm))
  have hzd : ∀ a, diagE ε (eT E) cpT cmT a a z = ((γ a : ℝ) : ℂ) • z :=
    diagE_wt_of_wK hσ hD (hwt γ v hvw)
  refine ⟨z, tsubVal_mem (Φ v), hz0, hzd, fun a b hab hε => ?_⟩
  set y := diagE ε (eT E) cpT cmT a b z with hy
  have hyS : y ∈ S' := diagE_mem_of_wK hσ hD S' hS'fin hS'K hε ⟨v, rfl⟩
  obtain ⟨w', hw'⟩ := hyS
  have hyd : ∀ c, diagE ε (eT E) cpT cmT c c y = (((γ + root a b) c : ℝ) : ℂ) • y := by
    intro c
    have hc := congrArg (fun F => F z)
      (diagAction_commutator (eT_isGlRep hD.glRep) cpT_cmT_isCAR (eT_commutesCAR E) ε c c a b rfl hε)
    simp only [Module.End.mul_apply, LinearMap.sub_apply] at hc
    rw [hzd c, map_smul] at hc
    have e1 : diagE ε (eT E) cpT cmT c c y =
        ((γ c : ℝ) : ℂ) • y + ((if c = a then diagE ε (eT E) cpT cmT c b else 0) -
          (if b = c then diagE ε (eT E) cpT cmT a c else 0)) z := by
      rw [hy, LinearMap.sub_apply, ← hc]; abel
    rw [e1]
    by_cases hca : c = a
    · subst hca
      have hcb : ¬ b = c := fun h => (ne_of_lt hab) h.symm
      simp only [if_neg hcb, sub_zero, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same, ↓reduceIte]
      rw [Pi.single_eq_of_ne (ne_of_lt hab)]
      simp only [sub_zero, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
      rfl
    · by_cases hcb : b = c
      · subst hcb
        simp only [if_neg hca, zero_sub, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same,
          LinearMap.neg_apply, ↓reduceIte]
        rw [Pi.single_eq_of_ne hca]
        simp only [zero_sub, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_one, add_smul, neg_smul,
          one_smul]
        rfl
      · simp only [if_neg hca, if_neg hcb, sub_zero, LinearMap.zero_apply, add_zero, Pi.add_apply, root,
          Pi.sub_apply]
        rw [Pi.single_eq_of_ne hca, Pi.single_eq_of_ne (Ne.symm hcb)]
        simp
  have hw'w : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T (γ + root a b) w' := by
    apply hwt'
    intro θ
    rw [hw']
    exact wK_diag_wt hσ hD hyd θ
  by_contra hne
  have hw'0 : w' ≠ 0 := by
    intro h; apply hne; rw [← hw', h, map_zero]
  exact not_cdom_add_root ε γ hab (hdom _ w' (Submodule.mem_top) hw'0 hw'w)

end GlobalTheory.PsCo.PcEF
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ZetaProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_fin_getD_list (f : ℂˣ → ℂ) : ∀ l : List ℂˣ, ∏ a : Fin l.length, f (l.getD a 1) = (l.map f).prod
  | [] => by simp
  | b :: l => by
    rw [List.length_cons, Fin.prod_univ_succ]
    simp [prod_fin_getD_list f l]

theorem prod_fin_getD (m : Multiset ℂˣ) {n : ℕ} (hn : m.card = n) (f : ℂˣ → ℂ) :
    ∏ a : Fin n, f (m.toList.getD a 1) = (m.map f).prod := by
  have hl : m.toList.length = n := (Multiset.length_toList m).trans hn
  subst hl
  rw [prod_fin_getD_list]
  conv_rhs => rw [← Multiset.coe_toList m]
  rw [Multiset.map_coe, Multiset.prod_coe]

variable {D : D7}


open Classical in
def zetaParams (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : GlobalTheory.LFun.Fam D.host.E) (cμ : (AE D)ˣ →* Circle) :
    HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ := fun w a =>
  if OffS D S w then
    (((B w).toList.getD a 1 : ℂˣ) : ℂ) * ((((GlobalTheory.LFun.val cμ)⁻¹ w : ℂˣ)) : ℂ) * GlobalTheory.LFun.npow w (-((1 + (D.R.t : ℂ)) / 2))
  else 0

theorem re_neg_half : (-((1 + (D.R.t : ℂ)) / 2)).re = -((1 + (D.R.t : ℝ)) / 2) := by
  rw [show -((1 + (D.R.t : ℂ)) / 2) = ((-((1 + (D.R.t : ℝ)) / 2) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

theorem norm_zetaParams_le {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.r) :
    ‖zetaParams S B cμ w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2) := by
  unfold zetaParams
  split_ifs with hw
  · have ha : (a : ℕ) < (B w).toList.length := by rw [Multiset.length_toList, hcard w hw]; exact a.2
    have hβ : (B w).toList.getD a 1 ∈ B w := by
      rw [List.getD_eq_getElem _ _ ha]
      exact Multiset.mem_toList.1 (List.getElem_mem ha)
    have hN : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
      have := two_le_absNorm w
      linarith
    rw [norm_mul, norm_mul, Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one, mul_one,
      GlobalTheory.LFun.norm_npow, re_neg_half, sub_eq_add_neg, Real.rpow_add hN]
    exact mul_le_mul_of_nonneg_right (hb w hw _ hβ) (Real.rpow_nonneg hN.le _)
  · rw [norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem eulerOff_zetaParams {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) :
    eulerOff D S (zetaParams S B cμ) = GlobalTheory.LFun.LSD D S B cμ ((1 + (D.R.t : ℂ)) / 2) := by
  set x := zetaParams S B cμ with hxdef
  have hx := norm_zetaParams_le cμ hcard hb
  obtain ⟨h1, h2, -⟩ := sum_bound (OffS D S) (κ := Fin D.R.r) (fun a => ‖x a.1.1 a.2‖) (fun _ => norm_nonneg _) fun a => by
    refine (hx _ _).trans ?_
    have ht : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have := two_le_absNorm a.1.1
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  have hm : Multipliable fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ := by
    have := multipliable_one_add_of_summable (f := fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ - 1)
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (h2.mul_left 2))
    · simpa using this
    · have hx2 : ‖x p.1.1 p.2‖ ≤ 1 / 2 := h1 p
      have h3 : 1 / 2 ≤ ‖1 - x p.1.1 p.2‖ := by
        have := norm_sub_norm_le (1 : ℂ) (x p.1.1 p.2)
        rw [norm_one] at this
        linarith
      have hne : 1 - x p.1.1 p.2 ≠ 0 := fun h => by rw [h, norm_zero] at h3; linarith
      have e : (1 - x p.1.1 p.2)⁻¹ - 1 = x p.1.1 p.2 * (1 - x p.1.1 p.2)⁻¹ := by
        field_simp
        ring
      have h4 : ‖1 - x p.1.1 p.2‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) two_pos]
        linarith
      rw [e, norm_mul, norm_inv]
      nlinarith [norm_nonneg (x p.1.1 p.2)]
  have hp := hm.hasProd.prod_fiberwise fun b => hasProd_fintype _
  rw [eulerOff, ← hp.tprod_eq]
  show _ = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))))
    (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val cμ)⁻¹) ((1 + (D.R.t : ℂ)) / 2)
  rw [GlobalTheory.LFun.eulerProd]
  let e : {w // OffS D S w} ≃ {w // w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))} :=
    Equiv.subtypeEquivRight fun w => (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff S w).trans (by simp [GlobalTheory.LFun.above])
  rw [← e.tprod_eq]
  refine tprod_congr fun w => ?_
  show _ = GlobalTheory.LFun.locL _ w.1 _
  rw [GlobalTheory.LFun.locL_twist, ← prod_fin_getD (B w.1) (hcard w.1 w.2)]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [hxdef, zetaParams, if_pos w.2]

end GlobalTheory.LowRow.ZetaProd

namespace GlobalTheory.LowRow

theorem finiteZetaC_of_finiteZetaL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    FiniteZetaL R F → FiniteZetaC R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  obtain ⟨B, hsys, hb, -, hsum⟩ := hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  have hcard : ∀ w, OffS D (finS R t) w → (B w).card = D.R.r := fun w hw => by
    have hv : w.under (𝓞 D.host.F) ∉ ((finS R t : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
      simpa using (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff _ w).1 hw
    rcases hsys _ hv w rfl with ⟨-, h, -⟩ | ⟨-, τ, ϖ, α, -, -, h, -⟩
    · exact h
    · rw [h]
      exact GlobalTheory.LGrp.card_bcParam _ α
  refine ⟨ZetaProd.zetaParams (finS R t) B cμ, ZetaProd.norm_zetaParams_le cμ hcard hb, fun U₁ h₁ U₂ h₂ v₁ v₂ => ?_⟩
  rw [ZetaProd.eulerOff_zetaParams cμ hcard hb]
  exact hsum U₁ h₁ U₂ h₂ v₁ v₂

end GlobalTheory.LowRow

end
end

section

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.HCChar (dsChar)

namespace GlobalTheory.PsCo.PcEF

namespace WeylCompactTorusIdentity

theorem alg {W S C M s p x : ℂ} (hs : s * s = 1) (hp : p * p = 1) (hW : W ≠ 0) (hM : M ≠ 0) (hs0 : s ≠ 0)
    (hx : W * x = S * C) : s * x = p * S / (W * (s * M)) * (p * M * C) := by
  have hden : W * (s * M) ≠ 0 := mul_ne_zero hW (mul_ne_zero hs0 hM)
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (M * s * s) * hx + (M * S * C) * hs - (M * S * C) * hp

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

end WeylCompactTorusIdentity


open WeylCompactTorusIdentity in
theorem weylFormulaCompactTorusIdentity_of_ingredients : VdmSplit → PhysTor → NumShift → TorusId := by
  intro hV hP hN n ε lam Λ m hm hΛ θ hinj x hx
  have ht0 : ∀ a, tor θ a ≠ 0 := fun a => Complex.exp_ne_zero _
  obtain ⟨hPD, -⟩ := hP n ε θ
  have hVd := hV n ε (tor θ)
  have hx' : ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x =
      (∑ w ∈ GlobalTheory.HCChar.compactWeyl ε,
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, tor θ a ^ m (w.symm a)) *
        ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) := by
    rw [hx]
    exact (congrArg (fun μ => ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε μ (tor θ)) (funext hΛ)).trans
      (hN n ε m (fun b : Bool => if b then (0 : ℤ) else (pOf ε : ℤ)) (tor θ) ht0)
  have hV0 : (∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
    exact sub_ne_zero.mpr (fun h => (Finset.mem_Ioi.mp hb).ne (hinj h))
  rw [hVd] at hV0
  rw [GlobalTheory.HCChar.dsChar_eq ε hm θ, hPD, hVd]
  exact alg (neg_one_pow_mul_self _) (neg_one_pow_mul_self _)
    (left_ne_zero_of_mul hV0) (right_ne_zero_of_mul (right_ne_zero_of_mul hV0))
    (pow_ne_zero _ (by norm_num)) hx'

end GlobalTheory.PsCo.PcEF

end
end

namespace GlobalTheory.PsCo.PcEF
open GlobalTheory.PsCo.PcEG

theorem torusId_full : TorusId := weylFormulaCompactTorusIdentity_of_ingredients vandermonde_splits_compactNoncompact adjointDet_onCompactTorus numShift_holds

end GlobalTheory.PsCo.PcEF
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem small_second : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j)) l))) → ∀ j, ¬IsUnit (F.θ (b j)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hc k e he hA U hU b hW j
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hC
  have hcμ : (fun i => map F.θ (μ' i)) = c.μ := funext hc
  have hconst : ∀ i, constantCoeff (μ' i) = 0 := hμ'.const

  have hQL : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => hcμ ▸ ql_map hΘ μ' hconst (he.1 i)
  have hlog : ∀ i, cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := fun i =>
    hcμ ▸ formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hconst (hA i).1
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.quasiLogarithm_secondBlock_tangent_basis_dual_lie p C v O hv ε hε F G d c μ' hμ' hc k e he hA Θ hΘ

  have hT := GlobalTheory.T.frobenius_linearCombination_zero_left_ainfFrame p O ε F d k e U (fun i => (hU i).1) b
  have hC1 := GlobalTheory.T.coboundary_frobenius_commute_mod_p_quasiLog p O ε F d μ' hμ' (Fin d ⊕ Fin k) e he.1 (Sum.elim (fun _ => 0) b)
  obtain ⟨F₁, t, hF₁, hlin, hpβ, hα⟩ := GlobalTheory.T.frobenius_congruence_combination_over_integers p C v O hv ε F d c.μ μ' hμ' hc k e he.1 _ b hW hT hC1
  have ht := GlobalTheory.T.not_isUnit_coeff_of_coboundary_small' p C v O hv d c.μ c.isLaw t hlin hα
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integral_coboundaryOne_congr_frobenius p C v O hv d c.μ c.isLaw (map F.θ F₁) t ht
    (fun β => by rw [coeff_map]; exact hpβ β)
  have key : cob1 (up C c.μ) (comb (Sum.elim 0 fun j => F.θ (b j)) fun i => map Θ (e i)) =
      map (algebraMap O C) (map F.θ F₁) := by
    have h1 : (Sum.elim 0 fun j => F.θ (b j) : Fin d ⊕ Fin k → O) =
        fun i => F.θ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) i) := by
      funext i; rcases i with i | i <;> simp
    rw [h1, ← map_comb hΘ, ← hcμ, ← map_formalGroupLawCoboundaryOne_square hΘ μ' hconst, ← hF₁]
    ext α; simp [coeff_map, hΘ]
  refine GlobalTheory.T.tangent_coords_nonunit_alt p C v O hv G d c C hC k (fun i => map Θ (e i)) lb hQL hlb hlog
    (fun j => F.θ (b j)) u (fun α => ⟨_, hu α, ?_⟩) j
  rw [key, ← map_sub, coeff_map, map_sub]

end GlobalTheory.SmallSecond
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, Subgroup.Commensurable ((KHT p G.m G.n r G.Fw).map (MulAut.conj g).toMonoidHom) (KHT p G.m G.n r G.Fw)) ∧ (KHT p G.m G.n r G.Fw).comap (inclG G r) = Kp0 G ∧ (KHT p G.m G.n r G.Fw).map (sigG G r) ≤ KHT p G.m G.n r G.Fw := by
  first | (exact @GlobalTheory.heckeOperator_integral) | (exact GlobalTheory.heckeOperator_integral) | (intros; apply GlobalTheory.heckeOperator_integral  <;> assumption)
end
