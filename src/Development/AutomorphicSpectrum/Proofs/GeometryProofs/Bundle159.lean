module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle148
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerSeriesExpansionInDeltaUnique
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle152
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle151
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDifferenceGenerator
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle145
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_finite_normal_model_of_residue_finite : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℤ), IsProjOver s → ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X), (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom.Finite → ∃ (n : ℕ) (x : Fin n → Ω) (M : PModel ℤ x) (π : M.X ⟶ X), Flat.NormalCpt M.ξ ∧ IsFinite π ∧ M.ξ ≫ π = ξ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite | exact GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.FlatExt

open Filter Topology Set

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem isOpen_blockNz : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem conj_mem_mcPts {P : Ideal (MRing J)} {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) :
    (fun p => starRingEnd ℂ (z p)) ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa using hi⟩
  · have h := hz.2 f hf
    rw [MvPolynomial.eval_map] at h ⊢
    have e := MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (Int.castRingHom ℂ) z f
    rw [h, map_zero, Subsingleton.elim ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)] at e
    exact e.symm

theorem continuousOn_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X}
    {g : X → ℂ} (h : A.HoloOn U g) : ContinuousOn g U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hc := (A.chart j).continuousAt hj
  have hsy : (A.chart j).symm (A.chart j y) = y := (A.chart j).left_inv hj
  have han : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j y) :=
    (h j _ ⟨(A.chart j).map_source hj, by simpa [hsy] using hy⟩).continuousAt
  have hcomp : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) y := ContinuousAt.comp han hc
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with w hw
  simp [(A.chart j).left_inv hw]

theorem analyticAt_lift {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (x : R.X) (j : Fin R.A.n)
    {t : Fin D → ℂ} (ht : t ∈ (R.A.chart j).target) (hx : (R.A.chart j).symm t ∈ R.U x) :
    AnalyticAt ℂ (fun t' => R.lift x ((R.A.chart j).symm t')) t :=
  AnalyticAt.pi fun p => R.holo x p j t ⟨ht, hx⟩

theorem ratio_eq {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (H : HermLine J) (hHa : H.a = a) {x y : R.X} (hy : y ∈ R.U x) :
    φ (R.lift y y) / H.h (R.lift y y) = φ (R.lift x y) / H.h (R.lift x y) := by
  obtain ⟨c, hc, e⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [e, hsm _ (R.mem x y hy) c hc, H.smul c _ hc, hHa, mul_div_mul_left _ _ hne]

theorem smooth_ratio {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖)
    (H : HermLine J) (hHa : H.a = a) (hH : IsSmoothHerm H) :
    R.A.Smooth fun x => Real.log (φ (R.lift x x) / H.h (R.lift x x)) := by
  intro j t ht
  have ht : t ∈ (R.A.chart j).target := ht.1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = (R.A.chart j).symm t := ⟨_, rfl⟩
  have hm₀ : R.lift x₀ x₀ ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hγ : AnalyticAt ℂ (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    analyticAt_lift R x₀ j ht (hx₀ ▸ R.mem_U _)
  have hγt : R.lift x₀ ((R.A.chart j).symm t) = R.lift x₀ x₀ := by rw [hx₀]
  have hsc : ContinuousAt (R.A.chart j).symm t := (R.A.chart j).continuousAt_symm ht
  have hev : ∀ᶠ t' in 𝓝 t, (R.A.chart j).symm t' ∈ R.U x₀ ∧
      R.lift x₀ ((R.A.chart j).symm t') ∈ V := by
    refine (hsc.eventually ((R.isOpen_U x₀).mem_nhds (hx₀ ▸ R.mem_U _))).and
      (hγ.continuousAt.eventually (hV.mem_nhds ?_))
    show R.lift x₀ ((R.A.chart j).symm t) ∈ V
    rw [hγt]
    exact hzV
  have hne : F (R.lift x₀ ((R.A.chart j).symm t)) ≠ 0 := by
    rw [hγt]
    exact (hFφ _ ⟨hzV, hm₀⟩).1
  have hFa : AnalyticAt ℂ (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    AnalyticAt.fun_comp (hF _ (by rw [hγt]; exact hzV)) hγ
  have e1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    hFa.contDiffAt.restrict_scalars ℝ
  have e2 := (e1.norm ℝ hne).log (norm_ne_zero_iff.2 hne)
  have hγr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    hγ.contDiffAt.restrict_scalars ℝ
  have hmem : R.lift x₀ ((R.A.chart j).symm t) ∈ {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    rw [hγt]
    exact hm₀.1
  have e3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => H.h (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    ContDiffAt.comp t (hH.contDiffAt (isOpen_blockNz.mem_nhds hmem)) hγr
  have e4 := e3.log (H.pos _ hmem).ne'
  refine ((e2.sub e4).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hev] with t' ht'
  obtain ⟨h1, h2⟩ := ht'
  have hm := R.mem _ _ h1
  obtain ⟨h0, hφ⟩ := hFφ _ ⟨h2, hm⟩
  show Real.log (φ (R.lift _ _) / H.h (R.lift _ _)) = _
  rw [ratio_eq R hsm H hHa h1, hφ, Real.log_div (norm_ne_zero_iff.2 h0) (H.pos _ hm.1).ne']

theorem isFlatOn_of_local {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (T : HermLine J)
    {φ : ((Σ k, J k) → ℂ) → ℝ} (hT : ∀ z ∈ mcPts P, T.h z = φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) :
    IsFlatOn R T := by
  intro x _
  have hm₀ : R.lift x x ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hcl : ContinuousOn (R.lift x) (R.U x) :=
    continuousOn_pi.2 fun p => continuousOn_of_holoOn R.A (R.holo x p)
  have hW₁ : IsOpen (R.U x ∩ R.lift x ⁻¹' V) := hcl.isOpen_inter_preimage (R.isOpen_U x) hV
  have hf0 : F (R.lift x x) ≠ 0 := (hFφ _ ⟨hzV, hm₀⟩).1
  have hfc : ContinuousOn (fun y => F (R.lift x y) / F (R.lift x x)) (R.U x ∩ R.lift x ⁻¹' V) :=
    (hF.continuousOn.comp (hcl.mono inter_subset_left) fun y hy => hy.2).div_const _
  have hW := hfc.isOpen_inter_preimage hW₁ Complex.isOpen_slitPlane
  refine ⟨_, hW, ⟨⟨R.mem_U x, hzV⟩, by simp [hf0]⟩,
    fun y => Complex.log (F (R.lift x y) / F (R.lift x x)) + (Real.log ‖F (R.lift x x)‖ : ℂ), ?_, ?_⟩
  · intro j t ht
    have hγ := analyticAt_lift R x j ht.1 ht.2.1.1
    have hFa : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t'))) t :=
      AnalyticAt.fun_comp (hF _ ht.2.1.2) hγ
    have hga : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t')) / F (R.lift x x)) t :=
      hFa.div analyticAt_const hf0
    exact (hga.clog ht.2.2).add analyticAt_const
  · intro y hy
    have hm : R.lift x y ∈ V ∩ mcPts P := ⟨hy.1.2, R.mem x y hy.1.1⟩
    obtain ⟨h0, h1⟩ := hFφ _ hm
    show Real.log (T.h (R.lift x y)) - 0 = _
    rw [hT _ hm.2, h1, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 h0) (norm_ne_zero_iff.2 hf0)]
    ring

theorem exists_flat_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  intro K _ J _ P D R a φ hpos hconj hsm hloc
  have hHs : IsSmoothHerm (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a) :=
    GroundTheory.Heights₂.Heights.LowerBoundFree.FsInvPow.isSmoothHerm_fsHerm a
  obtain ⟨H, hHdef⟩ : ∃ H, H = GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a := ⟨_, rfl⟩
  have hHa : H.a = a := by rw [hHdef]; rfl
  rw [← hHdef] at hHs
  obtain ⟨B, hBa, hBs, hB⟩ := GlobalTheory.T.smooth_function_as_degree_zero_metric K J P D R _ (smooth_ratio R hsm hloc H hHa hHs)
  have hT₀s : IsSmoothHerm (H.tensor B) := ContDiffOn.mul hHs hBs
  have hT₀a : (H.tensor B).a = a := by
    show H.a + B.a = a
    rw [hHa, hBa, add_zero]
  have hpt : ∀ x, (H.tensor B).h (R.lift x x) = φ (R.lift x x) := by
    intro x
    have hm := R.mem x x (R.mem_U x)
    have hHp := H.pos _ hm.1
    have hBp := B.pos _ hm.1
    have hq : 0 < φ (R.lift x x) / H.h (R.lift x x) := div_pos (hpos _ hm) hHp
    have e := Real.log_injOn_pos (Set.mem_Ioi.2 hBp) (Set.mem_Ioi.2 hq) (hB x)
    show H.h _ * B.h _ = _
    rw [e]
    field_simp
  have hT₀ : ∀ z ∈ mcPts P, (H.tensor B).h z = φ z := by
    intro z hz
    have hnt : z ∉ mcPts (⊤ : Ideal (MRing J)) := fun h => by
      have h1 := h.2 1 trivial
      simp at h1
    obtain ⟨x, c, hc, e⟩ := R.surj z hz hnt
    have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have h1 := hpt x
    rw [e, (H.tensor B).smul c z hc, hT₀a, hsm z hz c hc] at h1
    exact mul_left_cancel₀ hne h1
  obtain ⟨T, hTa, hTs, hTc, hT⟩ := GlobalTheory.T.conjugation_invariant_hermitian_metric K J (H.tensor B) hT₀s
  have hTφ : ∀ z ∈ mcPts P, T.h z = φ z := by
    intro z hz
    have hc := conj_mem_mcPts hz
    have e := hT z hz.1
    rw [hT₀ z hz, hT₀ _ hc, hconj z hz, add_self_div_two] at e
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (T.pos z hz.1)) (Set.mem_Ioi.2 (hpos z hz)) e
  exact ⟨T, hTa.trans hT₀a, hTs, hTc, hTφ, isFlatOn_of_local R T hTφ hloc⟩

end GlobalTheory.CompanionTheory.Ar.Chg.FlatExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.zero_section_surjective : ∀ (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ), Function.Surjective (secZ G x m).base := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.secZ_surj | exact GlobalTheory.CompanionTheory.Ar.Coc.secZ_surj | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.secZ_surj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.delta_expansion_restriction : ∀ (X0 : Scheme.{0}) (G : Over X0) [GrpObj G] (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (hp : 1 ≤ p) (B : Type) [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B), f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∀ hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W), ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v) → ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.coef_pull | exact GlobalTheory.CompanionTheory.Ar.Coc.coef_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.coef_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc.TestPair

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (y : Tm x p ⟶ t.G), y = homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p → rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left = (homAt x (jq w p m)).left ≫ (lift (jptG t x d g.x (p + m + 1) (0 : Fin 2)) (jptG t x d g.x (p + m + 1) (1 : Fin 2))).left := by
  intro E _ _ _ H _ X0 t k _ p _ _ x d g w m y hy
  subst hy
  obtain ⟨h0, h1⟩ := GlobalTheory.CompanionTheory.Ar.Coc.JetPts.main E H X0 t k p x d g w m
  unfold rQ
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift, lift_fst_assoc, lift_snd, h0, h1]

end GlobalTheory.CompanionTheory.Ar.Coc.TestPair
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.jet_augmentation_one_pth_power : ∀ (B : Type) [CommRing B] (p : ℕ) [Fact p.Prime], (p : B) = 0 → ∀ e : Jet B Unit p, (jetAug : Jet B Unit p →ₐ[B] B) e = 1 → ∃ v : B, e ^ p = 1 + dQ B p ^ p * algebraMap B _ (v ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add | exact GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.power_series_expansion_in_delta_unique : ∀ (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ) (W : (pullback G.hom x).Opens) (f : Γ(Ym G x m, prZ G x m ⁻¹ᵁ W)), ∃! c : Fin (m + 1) → Γ(pullback G.hom x, W), f = ∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Thick.sections_thick | exact GlobalTheory.CompanionTheory.Ar.Coc.Thick.sections_thick | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Thick.sections_thick <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem secZ_lift {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] {k : Type} [Field k] (x : Sp k ⟶ X0) {m : ℕ}
    (y : Tm x m ⟶ G) (hy : homAt x (jetAug : Jet k Unit m →ₐ[k] k) ≫ y = 1) :
    secZ G x m ≫ (lift (fst (Tm x m) G ≫ y) (snd (Tm x m) G)).left =
      pullback.fst G.hom x ≫ (lift (1 : G ⟶ G) (𝟙 G)).left := by
  have hf : (Over.homMk (pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) (by
      dsimp
      rw [Category.assoc, ← Category.assoc (spMap _), spMap_comp_alg]
      simp [spMap]) : FinalForm G x ⟶ Tm x m) ≫ y = 1 := by
    have e : (Over.homMk (pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) (by
        dsimp
        rw [Category.assoc, ← Category.assoc (spMap _), spMap_comp_alg]
        simp [spMap]) : FinalForm G x ⟶ Tm x m) =
        (Over.homMk (pullback.snd G.hom x) (by simp [spMap]) : FinalForm G x ⟶ overAt x k) ≫ homAt x (jetAug : Jet k Unit m →ₐ[k] k) := by
      ext1
      rfl
    rw [e, Category.assoc, hy]
    simp [Hom.one_def]
  have e₂ : pullback.fst G.hom x ≫ (lift (1 : G ⟶ G) (𝟙 G)).left =
      ((Over.homMk (pullback.fst G.hom x) pullback.condition : FinalForm G x ⟶ G) ≫ lift (1 : G ⟶ G) (𝟙 G)).left := rfl
  rw [e₂, secZ, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_snd, hf]
  simp [Hom.one_def]

theorem red_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p) → ∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1 := by
  intro E _ _ _ H X0 t k _ x p y hy κ hκ τ hτ C hC j h
  refine fn_ext fun z hz => ?_
  refine (gs_appLE (secZ t.G x p) _ _ h z hz (C.s fun _ => j).val).trans ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good t.PP.L t.PP.isLB z (K := Unit) (fun _ => pullback.fst t.G.hom x) (fun _ => j)
    (fun _ _ _ => rfl) (fun _ => hz)
  have eJ' : J (pullback.fst t.G.hom x) = j := eJ ()
  have hv := val_of C (secZ t.G x p) z J (fun _ => j) (Fin.forall_fin_two.2
    ⟨(congrArg J (secZ_pa t.G x y hy)).trans eJ', (congrArg J (secZ_snd t.G x p)).trans eJ'⟩)
  have h₁ : val κ (secZ t.G x p ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J = 1 := by
    rw [secZ_lift t.G x y hy, ← val_pull hJ, val_corr hJ hκ, val_one]
  have h₂ : val τ (secZ t.G x p ≫ (fst (Tm x p) t.G).left) z J = 1 := by
    rw [secZ_fst, hτ _ _ z J hJ]
  have hm : (secZ t.G x p) z ∈ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j) := h hz
  have hval : val C (secZ t.G x p) z J = 1 := by
    rw [hC _ _ z J hJ, h₁, h₂]
    simp
  refine (gs_unit _ z _ hm (C.s fun _ => j)).trans ((congrArg Units.val (hv.symm.trans hval)).trans ?_)
  rw [gs_eq (𝟙 _) z _ (show (𝟙 (pullback t.G.hom x)) z ∈ pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j from hz), map_one, map_one,
    Units.val_one]

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem aug_comp_inL (k : Type) [Field k] (B : Type) [CommRing B] [Algebra k B] (p : ℕ) :
    ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B).comp
        ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      (algebraMap k B).comp ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    have h0 : (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.C a) : Jet k Unit p) =
        algebraMap k (Jet k Unit p) a := rfl
    simp only [RingHom.comp_apply, h0, RingHom.coe_coe, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply k B (Jet B Unit p), AlgHom.commutes]
    rfl
  · intro i
    have h1 : (inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = dQ B p := by
      change (MvPolynomial.aeval fun _ => dQ B p) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    have h2 : (jetAug : Jet B Unit p →ₐ[B] B) (dQ B p) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : B)) (MvPolynomial.X () : MvPolynomial Unit B) = _
      simp
    have h3 : (jetAug : Jet k Unit p →ₐ[k] k)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : k)) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    simp only [RingHom.comp_apply, RingHom.coe_coe, h1, h2, h3, map_zero]

theorem red_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G) (B : Type) [CommRing B] [Algebra k B], homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ τ₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) τ₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet B Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val τ (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
  intro E _ _ _ H X0 t k _ x p y B _ _ hy τ hτ j₀ hj₀
  have h1 : ∀ (κ : Fin 2) (q : Sp (Jet B Unit p)),
      (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) ≫
        (![y.left, (1 : Tm x p ⟶ t.G).left] : Fin 2 → _) κ) q ∈ t.PP.L.U j₀ := by
    intro κ q
    rw [Scheme.Hom.comp_apply]
    fin_cases κ
    · exact jet_left_mem t x j₀ hj₀ y hy _
    · exact jet_left_mem t x j₀ hj₀ 1 (by simp [Hom.one_def]) _
  have hc : spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫
        spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      spMap (algebraMap k B) ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [aug_comp_inL]
  obtain ⟨e₀, he, hall⟩ := val_eq_unit_of_red t.G.left (Sp (Jet k Unit p)) t.PP.L t.PP.isLB B p (Fin 2)
    ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1] τ
    (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) j₀ h1
    (fun z' J' hG _ => by rw [hc]; exact hτ _ _ z' J' hG)
  exact ⟨e₀, he, fun z J hG hJ => hall z J hG fun κ => hJ _ (h1 κ z)⟩

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.line_bundle_section_difference_generator : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (k : Type) [Field k] (p : ℕ) (f f' : Sp (Jet k Unit p) ⟶ X), spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f = spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f' → ∃ τ : LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]), τ.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen | exact GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.is_comb_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsCombAt x v cf w → IsCombAt (spMap φ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (Formalism.L2.Pj.dualMap φ) ≫ w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombMap.isCombAt_spMap | exact GlobalTheory.CompanionTheory.Ar.CombMap.isCombAt_spMap | (intros; apply GlobalTheory.CompanionTheory.Ar.CombMap.isCombAt_spMap <;> assumption)
end
