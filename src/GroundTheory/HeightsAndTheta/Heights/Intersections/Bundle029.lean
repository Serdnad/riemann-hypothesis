module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.LogCardLocIdealUnitMul
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle002
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial GroundTheory.Heights₂.Heights.Bridge GroundTheory.Heights₂.Heights.Bridge.GeoNum
  GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

theorem C_charOf_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) :
    (C ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := by
  have h : ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) ∈
      V.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := by
    rw [← Submodule.IsPrincipal.span_singleton_generator (V.comap C), Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.mpr dvd_rfl
  exact h

theorem GeoNumCut.full : GeoNumCut.Statement := by
  intro K _ ι _ V n a b t hV hp hdim ht htV
  classical
  set p := ReciprocityTheory.ChartRestriction.G.Geo.charOf V with hp_def
  have : Fact p.Prime := ⟨hp⟩
  have hpV : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := C_charOf_mem V
  have hker : RingHom.ker (red (ι := ι) p) ≤ V := by
    rw [ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpV
  have hcm : (V.map (red p)).comap (red p) = V := comap_map_eq p hker
  have : V.IsPrime := hV.1

  have hQ : IsMultiProjPrime (V.map (red p)) := by
    refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) hker, ?_, ?_⟩
    · rw [isMultiHomogIdeal_iff]
      obtain ⟨S, hS, hVS⟩ := hV.2.1
      refine ⟨red p '' S, ?_, by rw [hVS, Ideal.map_span]⟩
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨c, hc⟩ := hS f hf
      exact ⟨c, fun m hm k => hc m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [← isRelevant_comap_iff p, hcm]
      exact hV.2.2
  have hd : relDim (V.map (red p)) = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (quotEquiv p (V.map (red p)))
    rw [hcm] at this
    exact this.symm

  have htr : IsMultiHomog (red p t) b := by
    rw [isMultiHomog_iff]
    exact fun m hm k => ht m (MvPolynomial.support_map_subset _ _ hm) k
  have htrV : red p t ∉ V.map (red p) := by
    intro h
    apply htV
    rw [← hcm]
    exact h

  rw [← intNum_map_eq_geoNum p (n + 1) V hV hpV hdim,
    CutRegular.full (ZMod p) K ι (V.map (red p)) hQ n hd b (red p t) htr htrV a]
  have hcut := cycEval_divCycle_eq p (V.map (red p)) t
    (fun W => intNum (ZMod p) W a) (fun W => ReciprocityTheory.ChartRestriction.G.Geo.geoNum n W a)
    (fun W' hW' => by
      obtain ⟨hW'm, hW'd⟩ :=
        DivCycleSupport.full (ZMod p) K ι (V.map (red p)) hQ n hd b _ htr htrV W' hW'
      exact intNum_eq_geoNum_comap p n W' hW'm hW'd a)
  rw [hcm] at hcut
  exact hcut

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingInj.le_of_locRing_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W W' : Ideal (MRing ι)} (hP : P.IsPrime) (hW : IsMultiProjPrime W) (hW' : IsMultiProjPrime W')
    (hPW : P ≤ W) (hPW' : P ≤ W') (heq : locRing P W = locRing P W') : W ≤ W' := by
  classical
  have := hP
  have hL := LocRingLocal.proof LocRingFrac.proof
  set φ := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) with hφ
  have hne : ∀ {f : MRing ι}, f ∉ P → φ (Ideal.Quotient.mk P f) ≠ 0 := fun hf h => hf <| by
    rwa [hφ, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h

  have hunit : ∀ {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) (hy' : y ∈ locRing P W'),
      IsUnit (⟨y, hy'⟩ : locRing P W') → IsUnit (⟨y, hy⟩ : locRing P W) := by
    intro y hy hy' hu
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    have hb' : y * (b : FractionRing (MRing ι ⧸ P)) = 1 := by
      have := congrArg Subtype.val hb
      rwa [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk] at this
    have hbW : (b : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by rw [heq]; exact b.2
    refine IsUnit.of_mul_eq_one (⟨b, hbW⟩ : locRing P W) (Subtype.ext ?_)
    rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk, hb']
  choose i hi using hW.2.2
  choose j hj using hW'.2.2

  have hjW : ∀ k, (X ⟨k, j k⟩ : MRing ι) ∉ W := by
    intro k
    have hiP : (X ⟨k, i k⟩ : MRing ι) ∉ P := fun h => hi k (hPW h)
    have hjP : (X ⟨k, j k⟩ : MRing ι) ∉ P := fun h => hj k (hPW' h)
    have h1 : φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) ∈ locRing P W :=
      heq ▸ frac_mem_locRing hPW' (AvoidRing.isMultiHomog_X k (i k)) (AvoidRing.isMultiHomog_X k (j k))
        (hj k) (div_mul_cancel₀ _ (hne hjP))
    have h2 : φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) ∈ locRing P W :=
      frac_mem_locRing hPW (AvoidRing.isMultiHomog_X k (j k)) (AvoidRing.isMultiHomog_X k (i k))
        (hi k) (div_mul_cancel₀ _ (hne hiP))
    have hu : IsUnit (⟨_, h2⟩ : locRing P W) := by
      refine IsUnit.of_mul_eq_one (⟨_, h1⟩ : locRing P W) (Subtype.ext ?_)
      rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk]
      have := hne hiP
      have := hne hjP
      field_simp
    exact ((hL K ι P W hP hW.1 hPW).2 _ _ _ _ (AvoidRing.isMultiHomog_X k (j k))
      (AvoidRing.isMultiHomog_X k (i k)) (hi k) (div_mul_cancel₀ _ (hne hiP))).mp hu

  obtain ⟨S, hS, hWS⟩ := hW.2.1
  rw [hWS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have hfW : f ∈ W := hWS ▸ Ideal.subset_span hf
  by_contra hfW'
  have htW := AvoidRing.coordProd_not_mem hW.1 j hjW a
  have htW' := AvoidRing.coordProd_not_mem hW'.1 j hj a
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) (ι := ι) j a
  have hy := div_mul_cancel₀ (φ (Ideal.Quotient.mk P f)) (hne fun h => htW (hPW h))
  have hyW := frac_mem_locRing hPW ha ht htW hy
  have hyW' := frac_mem_locRing hPW' ha ht htW' hy
  have hu' : IsUnit (⟨_, hyW'⟩ : locRing P W') :=
    ((hL K ι P W' hP hW'.1 hPW').2 _ f _ a ha ht htW' hy).mpr hfW'
  exact ((hL K ι P W hP hW.1 hPW).2 _ f _ a ha ht htW hy).mp (hunit hyW hyW' hu') hfW

theorem LocRingInj.proof : LocRingInj.Statement := by
  intro K _ ι _ P W W' hP hW hW' hPW hPW' heq
  exact le_antisymm (LocRingInj.le_of_locRing_eq hP hW hW' hPW hPW' heq)
    (LocRingInj.le_of_locRing_eq hP hW' hW hPW' hPW heq.symm)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ComplexOrder

theorem analyticAt_of_eventually_differentiableAt {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {e : ℕ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') : AnalyticAt ℂ γ y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp h
  rw [analyticAt_pi_iff]
  intro p
  exact osgood e U (fun y' => γ y' p) hUo
    (fun y' hy' => ((differentiableAt_pi.mp (hU y' hy')) p).differentiableWithinAt) y hyU

theorem SheetHessPSD.proof : SheetHessPSD.Statement := by
  intro K _ ι _ P e Ψ M y w γ hM hPos hγ
  have hev := hγ.2
  have hγy : γ y ∈ mcPts P := hev.self_of_nhds.2.1
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hγy.1
  have han : AnalyticAt ℂ γ y :=
    analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
  have hUo := SemipositiveTwist.isOpen_noZeroBlock (ι := ι)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (M.h z)) (γ y) :=
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos _ hz).ne'
  have hcomp : (fun y' => Real.log (M.h (γ y'))) = (fun z => Real.log (M.h z)) ∘ γ := rfl
  have hC2 : ContDiffAt ℝ 2 (fun y' => Real.log (M.h (γ y'))) y := by
    rw [hcomp]
    exact hlog.comp y (han.restrictScalars.contDiffAt)
  show (ReciprocityTheory.AnForm.hessC (fun y' => Real.log (M.h (γ y'))) y).PosSemidef
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ y hC2 fun x => ?_
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp x han hlog]
  have hL := SemipositiveTwist.laplacian_line_eq_levi hlog (fderiv ℂ γ y x)
  have hΔ := hPos (γ y) hz (fderiv ℂ γ y x)
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter

namespace pullbackBadImage_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}


omit [Fintype K'] in
theorem pullQ_eq_local (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Ψ z = fun i =>
      Ψ (segre fun p => R.lift x z (v p)) i.succ / Ψ (segre fun p => R.lift x z (v p)) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  have hpt : pullPt R v z = fun p => (c ∘ κ) p.1 * R.lift x z (v p) := by
    funext p
    simp only [pullPt, hzc, Function.comp_apply, hv.2.2.1 p]
  have hpc : ∏ k, (c ∘ κ) k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  funext i
  simp only [pullQ, hpt, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem analyticAt_pullQ (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) (j : Fin R.A.n)
    (hj : x ∈ (R.A.chart j).source) (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  classical
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hl := analyticAt_lift_chart R x j hu
  have hs : AnalyticAt ℂ (fun w => segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  have hH : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p))) u :=
    (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs
  have hH0 : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre fun p => R.lift x ((R.A.chart j).symm u) (v p)) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun w => fun i : Fin n =>
      Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) i.succ /
        Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu]
    with w hw
  exact (pullQ_eq_local hv R Ψ hw.2).symm

theorem det_restrictScalars_eq_zero {m : ℕ} (f : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (h : LinearMap.det (f : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = 0) :
    (f.restrictScalars ℝ).det = 0 := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h)
  show LinearMap.det ((f.restrictScalars ℝ : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) :
    (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ)) = 0
  refine LinearMap.det_eq_zero_iff_ker_ne_bot.mpr ((Submodule.ne_bot_iff _).mpr ⟨w, ?_, hw0⟩)
  simpa using hw

end pullbackBadImage_holds


open pullbackBadImage_holds in
theorem pullbackBadImage_holds.proof : pullbackBadImage_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ hv _ _ _
  classical
  let S₁ : Fin R.A.n → Set (Fin n → ℂ) := fun j => (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹'
    ({x | R.lift x x ∈ mcPts J'} ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0})
  let S₂ : Fin R.A.n → Set (Fin n → ℂ) := fun j => {u | u ∈ (R.A.chart j).target ∧
    Ψ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 ∧
    LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}
  have hsub : pullQ R v Ψ '' (pullBad R v Ψ ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0}) ⊆
      ⋃ j, ((pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₁ j ∪
        (pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₂ j) := by
    rintro _ ⟨x, ⟨hx, h0⟩, rfl⟩
    rcases hx with (hB | hz) | ⟨j, hj, hn⟩
    · obtain ⟨j, hj⟩ := R.A.cover x
      refine Set.mem_iUnion.mpr ⟨j, Or.inl ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩⟩
      · rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact ⟨hB, h0⟩
      · simp [(R.A.chart j).left_inv hj]
    · exact absurd hz h0
    · have hd : LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
        by_contra hd
        exact hn ⟨analyticAt_pullQ hv R Ψ x j hj h0, hd⟩
      refine Set.mem_iUnion.mpr ⟨j, Or.inr ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_, hd⟩, ?_⟩⟩
      · rw [(R.A.chart j).left_inv hj]; exact h0
      · simp [(R.A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => measure_union_null ?_ ?_)
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
        (R.null j))
    intro u hu
    have hx := (R.A.chart j).map_target hu.1
    have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
    have := analyticAt_pullQ hv R Ψ _ j hx hu.2.2
    rw [hcu] at this
    exact (this.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u).restrictScalars ℝ) ?_ ?_
    · intro u hu
      have hx := (R.A.chart j).map_target hu.1
      have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
      have := analyticAt_pullQ hv R Ψ _ j hx hu.2.1
      rw [hcu] at this
      exact (this.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro u hu
      exact det_restrictScalars_eq_zero _ hu.2.2

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityFormula.proof (hN : RegularityFunctionFieldNumber.Statement) (hO : RegularityOrder.Statement)
    (hL : RegularityLocal.Statement) : RegularityFormula.Statement := by
  classical
  intro K _ ι _ P b hP hb hbW
  obtain ⟨hF, hNF⟩ := hN K ι P hP
  let _ := hF.toField
  have := hNF
  obtain ⟨hfree, hfin, hrank⟩ := hO K ι P hP
  let b' : regRing P := ⟨b, hbW⟩
  have hb' : b' ≠ 0 := fun h => hb (congrArg Subtype.val h)
  obtain ⟨hfs, hsum⟩ := hL K ι P b' hP hb'
  refine ⟨hfs, hsum.trans ?_⟩
  have hI := (ReciprocityTheory.ChartRestriction.G.AI.index_thm (funField P) (regRing P) hfree hfin (hrank hF) b' hb').2
  exact hI.trans (finsum_eq_sum_of_fintype _).symm

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem semiLocRing_le_locRing (P : Ideal (MRing ι)) {𝒲 : Set (Ideal (MRing ι))} {W : Ideal (MRing ι)}
    (hW : W ∈ 𝒲) : semiLocRing P 𝒲 ≤ locRing P W := by
  unfold semiLocRing locRing
  refine Subring.closure_mono ?_
  rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
  exact ⟨u, w, a, hw, hwW W hW, hu, hwa, rfl⟩

def semiToLoc (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲) :
    semiLocRing P 𝒲 →+* locRing P W :=
  Subring.inclusion (semiLocRing_le_locRing P hW)

theorem semiToLoc_coe (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    (b : semiLocRing P 𝒲) : ((semiToLoc P 𝒲 W hW b : locRing P W) : FractionRing (MRing ι ⧸ P)) = b := by
  simp [semiToLoc]

def semiMaxIdeal (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    [IsLocalRing (locRing P W)] : Ideal (semiLocRing P 𝒲) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (semiToLoc P 𝒲 W hW)

instance semiMaxIdeal.isPrime (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    [IsLocalRing (locRing P W)] : (semiMaxIdeal P 𝒲 W hW).IsPrime :=
  Ideal.comap_isPrime _ _

end Objects

def SemilocMaxIdeals.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)),
    IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')],
      (semiMaxIdeal P' (fibreOver v P' W) W' hW').IsMaximal ∧
      letI := (semiToLoc P' (fibreOver v P' W) W' hW').toAlgebra
      IsLocalization.AtPrime (locRing P' W') (semiMaxIdeal P' (fibreOver v P' W) W' hW')) ∧
    (∀ (W₁ W₂ : Ideal (MRing ι')) (h₁ : W₁ ∈ fibreOver v P' W) (h₂ : W₂ ∈ fibreOver v P' W)
      [IsLocalRing (locRing P' W₁)] [IsLocalRing (locRing P' W₂)],
      semiMaxIdeal P' (fibreOver v P' W) W₁ h₁ = semiMaxIdeal P' (fibreOver v P' W) W₂ h₂ → W₁ = W₂) ∧
    ∀ M : Ideal (semiLocRing P' (fibreOver v P' W)), M.IsMaximal →
      ∃ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W), ∀ [IsLocalRing (locRing P' W')],
        M = semiMaxIdeal P' (fibreOver v P' W) W' hW'

end GroundTheory.Heights₂.Heights.Inter
end
end
