module

public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetSegreConeSmul
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle066
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.PB.Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev PtsOf (P : Ideal (MRing ι)) : Type := ↥(Pts (pC P))

theorem proj_eq_of_orbit {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) : proj z = proj w := by
  obtain ⟨c, hc, rfl⟩ := h
  exact Top.proj_smul c hc w

theorem orbit_of_proj {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (h : proj z = proj w) : SameOrbit z w := by
  refine orbit_of_cross hz hw fun k i i' => ?_
  obtain ⟨j, hj⟩ := hz k
  have hN : ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos (hz k)).ne'
  have hM : ((∑ l, ‖w ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos (hw k)).ne'
  have hj' : starRingEnd ℂ (z ⟨k, j⟩) ≠ 0 := by simpa using hj
  have h1 := congrFun h ⟨k, (i, j)⟩
  have h2 := congrFun h ⟨k, (i', j)⟩
  simp only [proj] at h1 h2
  rw [div_eq_div_iff hN hM] at h1 h2
  have : (z ⟨k, i⟩ * w ⟨k, i'⟩ - z ⟨k, i'⟩ * w ⟨k, i⟩) *
      (starRingEnd ℂ (z ⟨k, j⟩) * ((∑ l, ‖w ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ)) = 0 := by
    linear_combination (w ⟨k, i'⟩) * h1 - (w ⟨k, i⟩) * h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (mul_ne_zero hj' hM))

variable {P : Ideal (MRing ι)} {e : ℕ}

theorem rep_mem_mcPts (x : PtsOf P) : rep x ∈ mcPts P :=
  (mem_mcPts_iff_conePts_pC P _).2 (rep_mem x)

theorem pts_eq_of_orbit {x y : PtsOf P} (h : SameOrbit (rep x) (rep y)) : x = y := by
  apply Subtype.ext
  rw [← proj_rep x, ← proj_rep y]
  exact proj_eq_of_orbit h

def cls (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) : PtsOf P :=
  ⟨proj z, z, (mem_mcPts_iff_conePts_pC P z).1 hz, rfl⟩

theorem rep_cls_orbit (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) : SameOrbit (rep (cls z hz)) z :=
  orbit_of_proj (rep_mem_mcPts _).1 hz.1 (proj_rep (cls z hz))

theorem mem_mcPts_of_orbit (hP : IsMultiHomogIdeal P) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (h : SameOrbit z' z) : z' ∈ mcPts P := by
  have hz' := (mem_mcPts_iff_conePts_pC P z).1 hz
  refine (mem_mcPts_iff_conePts_pC P z').2 ⟨fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, fun h0 => hi (by
      obtain ⟨c, hc, rfl⟩ := h
      have : c k * z ⟨k, i⟩ = 0 := h0
      exact (mul_eq_zero.1 this).resolve_left (hc k))⟩
  · obtain ⟨c, hc, rfl⟩ := h
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul (isMultiHomogIdeal_pC hP) c z hz'.2

theorem orbit_aff (p : (k : K) → ι k) {x : PtsOf P} (hx : x ∈ src (P := pC P) p) :
    SameOrbit (affCoord p (rep x)) (rep x) := by
  refine ⟨fun k => (rep x ⟨k, p k⟩)⁻¹, fun k => inv_ne_zero (hx k), ?_⟩
  funext q
  simp [affCoord, div_eq_inv_mul]

theorem exists_alt_variant (x : PtsOf P) : ∃ p : (k : K) → ι k, x ∈ src (P := pC P) p := by
  choose p hp using (rep_mem_mcPts x).1
  exact ⟨p, hp⟩

theorem continuousOn_aff (p : (k : K) → ι k) :
    ContinuousOn (fun x : PtsOf P => affCoord p (rep x)) (src (P := pC P) p) := by
  refine continuousOn_pi.2 fun q => ?_
  have hEval (r : Σ k, ι k × ι k) : Continuous (fun x : PtsOf P => x.1 r) :=
    (continuous_apply r).comp continuous_subtype_val
  have hDen (x : PtsOf P) (k : K) : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos ((rep_mem x).1 k)).ne'
  have hDiag (x : PtsOf P) (hx : x ∈ src (P := pC P) p) :
      x.1 ⟨q.1, (p q.1, p q.1)⟩ ≠ 0 := by
    rw [← proj_rep x]
    exact div_ne_zero (mul_ne_zero (hx q.1) (by simpa using hx q.1)) (hDen x q.1)
  refine ((hEval ⟨q.1, (q.2, p q.1)⟩).continuousOn.div₀
    (hEval ⟨q.1, (p q.1, p q.1)⟩).continuousOn hDiag).congr ?_
  intro x hx
  have h : starRingEnd ℂ (rep x ⟨q.1, p q.1⟩) ≠ 0 := by simpa using hx q.1
  dsimp only
  rw [← proj_rep x]
  simp only [proj, affCoord]
  rw [div_div_div_cancel_right₀ (hDen x q.1), mul_div_mul_right _ _ h]

def srcOf (C : OrbitChart P e) : Set (PtsOf P) := {x | rep x ∈ C.O}

theorem mem_O_of_orbit (C : OrbitChart P e) (hP : IsMultiHomogIdeal P) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ C.O)
    (h : SameOrbit z' z) (hzP : z ∈ mcPts P) : z' ∈ C.O :=
  C.O_orbit z hz z' (mem_mcPts_of_orbit hP hzP h) h

theorem isOpen_srcOf (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) : IsOpen (srcOf C) := by
  obtain ⟨O', hO', hO⟩ := C.O_open
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨p, hp⟩ := exists_alt_variant x
  have hOpen : IsOpen (src (P := pC P) p) := by
    have hSrc : src (P := pC P) p = ⋂ k, {y : PtsOf P | y.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
      ext y
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      change (∀ k, rep y ⟨k, p k⟩ ≠ 0) ↔ _
      refine forall_congr' fun k => ?_
      have hDen := Complex.ofReal_ne_zero.2 (Top.normSq_pos ((rep_mem y).1 k)).ne'
      rw [← proj_rep y]
      simp only [proj, ne_eq, div_eq_zero_iff, hDen, or_false, mul_eq_zero, map_eq_zero, or_self]
    rw [hSrc]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const
  have hS := hOpen.mem_nhds hp
  have hc : ContinuousAt (fun y : PtsOf P => affCoord p (rep y)) x := (continuousOn_aff p).continuousAt hS
  have hax : affCoord p (rep x) ∈ C.O :=
    mem_O_of_orbit C hP hx (orbit_aff p hp) (rep_mem_mcPts x)
  have hax' : affCoord p (rep x) ∈ O' := by rw [hO] at hax; exact hax.1
  filter_upwards [hS, hc (hO'.mem_nhds hax')] with y hy hy'
  have h1 : affCoord p (rep y) ∈ mcPts P := mem_mcPts_of_orbit hP (rep_mem_mcPts y) (orbit_aff p hy)
  have h2 : affCoord p (rep y) ∈ C.O := by rw [hO]; exact ⟨hy', h1⟩
  exact mem_O_of_orbit C hP h2 (Proj.orbit_symm (orbit_aff p hy)) h1

theorem continuousOn_rho (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) :
    ContinuousOn (fun x : PtsOf P => C.ρ (rep x)) (srcOf C) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨p, hp⟩ := exists_alt_variant x
  have hOpen : IsOpen (src (P := pC P) p) := by
    have hSrc : src (P := pC P) p = ⋂ k, {y : PtsOf P | y.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
      ext y
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      change (∀ k, rep y ⟨k, p k⟩ ≠ 0) ↔ _
      refine forall_congr' fun k => ?_
      have hDen := Complex.ofReal_ne_zero.2 (Top.normSq_pos ((rep_mem y).1 k)).ne'
      rw [← proj_rep y]
      simp only [proj, ne_eq, div_eq_zero_iff, hDen, or_false, mul_eq_zero, map_eq_zero, or_self]
    rw [hSrc]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const
  have hS := hOpen.mem_nhds hp
  have hO : srcOf C ∈ 𝓝 x := (isOpen_srcOf hP C).mem_nhds hx
  have hc : ContinuousAt (fun y : PtsOf P => affCoord p (rep y)) x := (continuousOn_aff p).continuousAt hS
  have hmem : ∀ y ∈ src (P := pC P) p, y ∈ srcOf C → affCoord p (rep y) ∈ C.O := fun y hy hy' =>
    mem_O_of_orbit C hP hy' (orbit_aff p hy) (rep_mem_mcPts y)
  have ht : Tendsto (fun y : PtsOf P => affCoord p (rep y)) (𝓝 x) (𝓝[C.O] (affCoord p (rep x))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hc, ?_⟩
    filter_upwards [hS, hO] with y hy hy' using hmem y hy hy'
  have h1 := (C.ρ_cont _ (hmem x hp hx)).tendsto.comp ht
  have e1 : C.ρ (affCoord p (rep x)) = C.ρ (rep x) :=
    C.ρ_orbit _ hx _ (hmem x hp hx) (orbit_aff p hp)
  rw [e1] at h1
  refine h1.congr' ?_
  filter_upwards [hS, hO] with y hy hy'
  exact C.ρ_orbit _ hy' _ (hmem y hy hy') (orbit_aff p hy)

def clsT (x₀ : PtsOf P) (z : (Σ k, ι k) → ℂ) : PtsOf P := if h : z ∈ mcPts P then cls z h else x₀

theorem clsT_of_mem (x₀ : PtsOf P) {z : (Σ k, ι k) → ℂ} (h : z ∈ mcPts P) : clsT x₀ z = cls z h := dite_eq_left h

theorem continuousOn_cls (C : OrbitChart P e) (x₀ : PtsOf P) :
    ContinuousOn (fun w => clsT x₀ (C.φ w)) C.D := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  have hφ : ContinuousOn C.φ C.D := continuousOn_pi.2 fun q => (C.holo q).continuousOn
  have h1 : ContinuousOn (fun w => proj (C.φ w)) C.D :=
    Top.continuousOn_proj.comp hφ fun w hw => (C.mem w hw).1
  refine h1.congr fun w hw => ?_
  simp only [Function.comp, clsT_of_mem x₀ (C.mem w hw), cls]

def orbChart (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) (x₀ : PtsOf P) :
    OpenPartialHomeomorph (PtsOf P) (Fin e → ℂ) where
  toFun x := C.ρ (rep x)
  invFun w := clsT x₀ (C.φ w)
  source := srcOf C
  target := C.D
  map_source' _ hx := C.ρ_mem _ hx
  map_target' w hw := by
    rw [clsT_of_mem x₀ (C.mem w hw)]
    exact mem_O_of_orbit C hP (C.φ_mem_O w hw) (rep_cls_orbit _ _) (C.mem w hw)
  left_inv' x hx := by
    have hm := C.mem _ (C.ρ_mem _ hx)
    show clsT x₀ (C.φ (C.ρ (rep x))) = x
    rw [clsT_of_mem x₀ hm]
    exact pts_eq_of_orbit (Proj.orbit_trans (rep_cls_orbit _ hm) (C.φ_ρ _ hx))
  right_inv' w hw := by
    show C.ρ (rep (clsT x₀ (C.φ w))) = w
    rw [clsT_of_mem x₀ (C.mem w hw)]
    have h1 := mem_O_of_orbit C hP (C.φ_mem_O w hw) (rep_cls_orbit _ (C.mem w hw)) (C.mem w hw)
    rw [C.ρ_orbit _ (C.φ_mem_O w hw) _ h1 (rep_cls_orbit _ (C.mem w hw)), C.ρ_φ w hw]
  open_source := isOpen_srcOf hP C
  open_target := C.isOpen_D
  continuousOn_toFun := continuousOn_rho hP C
  continuousOn_invFun := continuousOn_cls C x₀

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open GoodChartModel Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (blkW weight_blkW segMono eval_segMono psiPoly eval_psiPoly
  comp_mul_homog diag_of_homog)

section Rel

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isWeightedHomogeneous_of_isMultiHomog [DecidableEq K] {s : MRingOver ℂ ι} {a : K → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : IsWeightedHomogeneous (blkW ι) s a := by
  intro d hd
  funext k
  rw [weight_blkW]
  exact hs d (mem_support_iff.2 hd) k

theorem cone_homog [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) :
    Q.IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  refine Ideal.homogeneous_span _ _ ?_
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_of_isMultiHomog ha)⟩

theorem cone_segre_rel {e : ℕ} {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    (i : (k : K) → ι k) :
    ∃ r : ℕ, 0 < r ∧ ∃ G : Fin (e + 1) → MvPolynomial ((k : K) → ι k) ℂ,
      (∀ j, (G j).totalDegree ≤ r - 1) ∧
      ∀ z ∈ conePts Q, segre z i ^ r = ∑ j, Ψ (segre z) j * eval (segre z) (G j) := by
  classical
  have hsegMono (a : (k : K) → ι k) : IsWeightedHomogeneous (blkW ι) (segMono ι a) (fun _ => 1) := by
    have hprod := IsWeightedHomogeneous.prod (w := blkW ι) Finset.univ
      (fun k => (X ⟨k, a k⟩ : MvPolynomial (Σ k, ι k) ℂ))
      (fun k => blkW ι ⟨k, a k⟩) (fun k _ => isWeightedHomogeneous_X ℂ _ _)
    unfold segMono
    convert hprod using 1
    funext k
    simp [blkW, Finset.sum_apply, Pi.single_apply]
  have hpsiPoly (j : Fin (e + 1)) : IsWeightedHomogeneous (blkW ι) (psiPoly Ψ j) (fun _ => 1) := by
    unfold psiPoly
    exact IsWeightedHomogeneous.sum _ _ _ fun a _ => (hsegMono a).C_mul _
  set I := Q ⊔ Ideal.span (Set.range (psiPoly Ψ)) with hI
  have hrad : segMono ι i ∈ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p :=
      fun _ => rfl
    rw [hae]
    by_contra h
    rw [eval_segMono, ReciprocityTheory.ChartRestriction.G.Geo.segre, ← ne_eq, Finset.prod_ne_zero_iff] at h
    have hxm : x ∈ conePts Q := ⟨fun k => ⟨i k, h k (Finset.mem_univ _)⟩, fun f hf => by
      have := hx _ (Ideal.mem_sup_left hf : f ∈ I)
      rwa [hae] at this⟩
    refine hΨ x hxm (funext fun j => ?_)
    have := hx _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩) : psiPoly Ψ j ∈ I)
    rwa [hae, eval_psiPoly] at this
  obtain ⟨r0, hr0⟩ := hrad
  have hmem : segMono ι i ^ (r0 + 1) ∈ I := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hr0
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hb
  let D : K → ℕ := fun _ => r0
  let comp := weightedHomogeneousComponent (R := ℂ) (blkW ι) (D + fun _ => 1)
  have hpow : IsWeightedHomogeneous (blkW ι) (segMono ι i ^ (r0 + 1)) (D + fun _ => 1) := by
    have := (hsegMono i).pow (r0 + 1)
    convert this using 1
    funext k; simp [D]
  have hcomp := congrArg comp hab

  rw [map_add (f := _), map_sum, weightedHomogeneousComponent_eq_self hpow] at hcomp
  simp only [comp, comp_mul_homog (hpsiPoly _)] at hcomp
  have hcd : ∀ j, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ r0 ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z (weightedHomogeneousComponent (blkW ι) D (c j)) =
        eval (segre z) G :=
    fun j => diag_of_homog r0 (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose G hG hGz using hcd
  refine ⟨r0 + 1, Nat.succ_pos _, G, fun j => by simpa using hG j, fun z hz => ?_⟩
  have h0 := congrArg (eval z) hcomp

  rw [map_add (f := _), hz.2 _ (weightedHomogeneousComponent_mem_of_mem _ _ (cone_homog hP) ha _),
  zero_add, map_sum, map_pow, eval_segMono] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hGz, eval_psiPoly, mul_comm]

theorem cone_pow_mem {Q : Ideal (MRingOver ℂ ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : setChartIdeal (conePts Q) σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := cone_segre_rel hP Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine hJ ?_
    rw [setChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hz1, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0

    simp only [f, Gx, map_sub, map_add (f := _), map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
    GoodChartModel.eval_linPoly, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by

    simp only [f, map_sub, map_add (f := _), map_sum, hX, h0, zero_add,
    homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

theorem cxChartModel {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} (hQ : CxInt.IsCxVar Q e) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ ∧
      ∀ J ∈ (setChartIdeal (conePts Q) σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) ∧ IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  obtain ⟨hK, ⟨hQp, hQh, -⟩, hdimQ⟩ := hQ
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQh
  refine ⟨chart_zeroSet hR σ Ψ, fun J hJ => ?_⟩
  have hdim := chart_dim hQp hR hdimQ σ Ψ hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := cone_pow_mem hR hΨ hJ.1.2 a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩

end Rel

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  intro K _ ι _ P n M Xo B S hS K' hK' hc
  have hYo : IsOpen S.R.Yo := (GlobalTheory.T.regular_chart_data_properties n M.Xc M.atlas S.R).1
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hc]
  intro u hu x hx
  obtain ⟨j, hj⟩ := M.atlas.cover x
  have hO : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm hYo
  have hy : M.atlas.chart j x ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    ⟨(M.atlas.chart j).map_source hj, by
      simpa [Set.mem_preimage, (M.atlas.chart j).left_inv hj] using hK' hx⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ hy
  have hsub : Metric.closedBall (M.atlas.chart j x) (ε / 2) ⊆
      (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hU := (GlobalTheory.T.regularized_weight_tendsto_C2 K ι P n M Xo B S hS j _ hsub (isCompact_closedBall _ _)).1
  refine ⟨(M.atlas.chart j).source ∩ (M.atlas.chart j) ⁻¹' Metric.ball (M.atlas.chart j x) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (((M.atlas.chart j).isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
      ⟨hj, by simp [hε]⟩), ?_⟩
  filter_upwards [hU u hu] with t ht y hy'
  have h := ht (M.atlas.chart j y) (Metric.ball_subset_closedBall hy'.2)
  simpa [Function.comp, (M.atlas.chart j).left_inv hy'.1] using h

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.arithmetic_variety_generic_fibre_projective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.varieties_over_rat_arith_contract | exact GlobalTheory.CompanionTheory.Ar.PB.varieties_over_rat_arith_contract | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.varieties_over_rat_arith_contract <;> assumption)
end
