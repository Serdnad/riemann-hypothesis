module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle087
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsTiedRegularSetting
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle112
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle157
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle154
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle161
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedChartComparison
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle005
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle126
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle045
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
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
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Mathlib.Topology.Algebra.MvPolynomial

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → ∀ (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (σ : k →+* ℂ) (y : CxPts p σ), y ∈ offSupp p σ (divOfRatSec ψ.isLB hr) → logNorm ψ r (sheet t τ y) = logNorm (φ σ) r y := by
  intro k _ X _ p t τ B φ ψ h r hr σ y hy
  have hy' : sheet t τ y ∈ offSupp t τ (divOfRatSec ψ.isLB hr) := mem_offSupp.2 (mem_offSupp.1 hy)
  have hi' := mem_pick ψ.isLB (sheet t τ y)
  set i := pick ψ.isLB (sheet t τ y)
  have hi : y ∈ ptsIn p σ (B.U i) := mem_ptsIn.2 (mem_ptsIn.1 hi')
  rw [logNorm_eq ψ hr hy' hi', logNorm_eq (φ σ) hr hy hi, h σ i y hi]
  congr 3
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet

theorem finite_ringHom (k : Type) [CommRing k] [Module.Finite ℤ k] : Finite (k →+* ℂ) := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ k).FG)
  have hroot : ∀ a : k, ∃ S : Set ℂ, S.Finite ∧ ∀ σ : k →+* ℂ, σ a ∈ S := by
    intro a
    obtain ⟨P, hm, hP⟩ := (Algebra.IsIntegral.isIntegral a : IsIntegral ℤ a)
    refine ⟨{z | (P.map (Int.castRingHom ℂ)).IsRoot z}, ?_, fun σ => ?_⟩
    · exact Polynomial.finite_setOf_isRoot (hm.map _).ne_zero
    · have h : Polynomial.eval₂ (σ.comp (algebraMap ℤ k)) (σ a) P = 0 := by
        rw [← Polynomial.hom_eval₂, hP, map_zero]
      rw [Subsingleton.elim (σ.comp (algebraMap ℤ k)) (Int.castRingHom ℂ)] at h
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using h
  choose S hS hm using hroot
  have : ∀ i : s, Finite (S i) := fun i => (hS i).to_subtype
  refine Finite.of_injective (fun (σ : k →+* ℂ) (i : s) => (⟨σ i, hm i σ⟩ : S i)) fun σ₁ σ₂ h => ?_
  have hs' : ∀ i ∈ s, σ₁ i = σ₂ i := fun i hi => congrArg Subtype.val (congrFun h ⟨i, hi⟩)
  have hspan : ∀ x ∈ Submodule.span ℤ (s : Set k), σ₁ x = σ₂ x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => exact hs' x h
    | zero => simp
    | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
    | smul a x _ hx => simp [map_zsmul, hx]
  exact RingHom.ext fun x => hspan x (hs ▸ Submodule.mem_top)

variable {k : Type} [CommRing k] {X : Scheme.{0}}

theorem emb_apply (p : X ⟶ Sp k) {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ} (y : CxPts t τ) (a : k) :
    emb p y a = ev t τ ⊤ (algX p ⊤ a) y :=
  (ev_algX (y := unsheet p y) mem_ptsIn_top a).symm

theorem range_sheet (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact emb_sheet t τ z
  · intro h
    have h' : emb p y = σ := h
    subst h'
    exact ⟨unsheet p y, rfl⟩

theorem isOpen_emb_eq [Finite (k →+* ℂ)] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    IsOpen {y : CxPts t τ | emb p y = σ} := by
  have hc (a : k) : Continuous fun y : CxPts t τ => emb p y a := by
    simp only [emb_apply]
    exact (Points.continuous_valR_top _).comp continuous_subtype_val
  have e : {y : CxPts t τ | emb p y = σ} =
      ⋂ σ' : {s : k →+* ℂ // s ≠ σ}, ⋃ a : k, {y | emb p y a ≠ σ'.1 a} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · rintro rfl σ'
      by_contra h
      push Not at h
      exact σ'.2 (RingHom.ext fun a => (h a).symm)
    · intro h
      by_contra he
      obtain ⟨a, ha⟩ := h ⟨_, he⟩
      exact ha rfl
  rw [e]
  exact isOpen_iInter_of_finite fun σ' => isOpen_iUnion fun a => isOpen_ne_fun (hc a) continuous_const

theorem isOpenEmbedding_and_range : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ), Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) ∧ Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  intro k _ _ X p t τ σ
  have := finite_ringHom k
  have hr := range_sheet p t τ σ
  refine ⟨⟨IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
    IsEmbedding.subtypeVal, ?_⟩, hr⟩
  rw [hr]
  exact isOpen_emb_eq p t τ σ

end GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem WOver.pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ}
    {B : LB X} {φ : ∀ σ : k →+* ℂ, Weight p σ B} {ψ : Weight t τ B} (h : WOver φ ψ) (m : ℕ) :
    WOver (fun σ => (φ σ).pow m) (ψ.pow m) := by
  intro σ j y hy
  refine (ψ.zpow_φ _ j _).trans (Eq.trans ?_ ((φ σ).zpow_φ _ j y).symm)
  exact congrArg _ (h σ _ y (mem_pow_iff.1 hy))

theorem WOver.restr {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ}
    {B : LB X} {φ : ∀ σ : k →+* ℂ, Weight p σ B} {ψ : Weight t τ B} (h : WOver φ ψ) (i : Z ⟶ X) :
    WOver (p := i ≫ p) (t := i ≫ t) (fun σ => (φ σ).pull i rfl) (ψ.pull i rfl) := by
  intro σ j y hy
  have hm : PtsOver.map i rfl _ y ∈ ptsIn p σ (B.U (j PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => PtsOver.map i rfl _ y) (fun _ => rfl) hy PUnit.unit
  refine (ψ.pull_φ i rfl j _).trans (Eq.trans ?_ ((φ σ).pull_φ i rfl j y).symm)
  exact h σ _ _ hm

theorem wOver_restr_pow : ∀ (k : Type) [CommRing k] (X Z : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (i : Z ⟶ X) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (τ : ℤ →+* ℂ), WOver (L.restr i).φ (((toZ L t hL).restr i).φ τ) ∧ ∀ m : ℕ, WOver ((L.restr i).pow m).φ ((((toZ L t hL).restr i).pow m).φ τ) := by
  intro k _ X Z p t i L hL τ
  have h : WOver (L.restr i).φ (((toZ L t hL).restr i).φ τ) := (wOver_wZ L t τ).restr i
  exact ⟨h, fun m => h.pow m⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ZDens

theorem chernDens_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart t τ D), (∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y) → ∀ y ∈ c.e.source, c'.chernDens ψ (sheet t τ y) = c.chernDens (φ σ) y := by
  intro k _ _ _ _ X p t τ σ D B φ ψ hW hφ hψ c c' hm y hy
  obtain ⟨hy', he⟩ := hm y hy
  have hi := GlobalTheory.CxPts.mem_pick (φ σ).isLB y
  set i := GlobalTheory.CxPts.pick (φ σ).isLB y
  have hi' : sheet t τ y ∈ ptsIn t τ (B.U i) := hi
  rw [c'.chernDens_eq hψ hy' hi', c.chernDens_eq (hφ σ) hy hi, AlgChart.hess, AlgChart.hess, he]
  have ho := GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hmem := GlobalTheory.ChartGlue.mem_over c.e hy hi
  have e : (fun v => ((ψ.φ i (c'.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => (((φ σ).φ i (c.e.symm v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hmem] with v hv
    have hw := c.e.map_target hv.1
    obtain ⟨h₁, h₂⟩ := hm _ hw
    have hs : c'.e.symm v = sheet t τ (c.e.symm v) := by
      rw [← c'.e.left_inv h₁, h₂, c.e.right_inv hv.1]
    rw [hs, hW σ i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]

end GlobalTheory.CompanionTheory.Ar.ZDens
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem GlobalTheory.CompanionTheory.Ar.Cusp.breg_margin_tendsto (C : ℝ) :
    Tendsto (fun t : ℝ => max t (C / Real.log t⁻¹ + C * t)) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => C / Real.log t⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have h2 := h0.max (h1.add (h0.const_mul C))
  simpa using h2



theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_regularization_setting : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ), LogHom D Hd.aMu w → ChartPsh D w → ChartCont D w → ChartBdd D w → ConjOff D w → ∃ S' : BoundedRegularisationSetting M D.Xo Hd.aMu w, S'.IsTied ∧ ConjU S' := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w hL hP hC hB hO
  obtain ⟨ref, hra, hrs, hrc⟩ := GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric K J Hd.aMu
  obtain ⟨P, S, κ, hth, had, -, hsym, -⟩ :=
    GlobalTheory.CompanionTheory.Relay.exists_potential_charts_with_radii K J II Ψ Ω W D M ref (fun _ _ => 1) hrs hrc fun _ _ => one_pos
  obtain ⟨B, rfl, hph, hcj⟩ := GlobalTheory.CompanionTheory.Relay.adapted_subsets_for_potential_charts K J II Ψ Ω W D M ref w P S hrs hth had (hra ▸ hL) hP hC hB
  obtain ⟨ρ, hρ⟩ := GlobalTheory.CompanionTheory.Relay.exists_conj_invariant_mollifier D.n
  obtain ⟨cut, Cη, hcut, hcc⟩ := GlobalTheory.CompanionTheory.Relay.exists_cutoff_family_symmetric K J II Ψ Ω W D M _ κ hsym
  obtain ⟨C, t₀, ht₀, hcmp⟩ := GroundTheory.Heights₂.Heights.Regular.BoundedChartComparison.proof
    GroundTheory.Heights₂.Heights.Regular.MollifiedLowerBound.closed
    GroundTheory.Heights₂.Heights.Regular.PolyMaxOscillation.proof_closed M.Xc D.n M.atlas B ρ
  let S' : BoundedRegularisationSetting M D.Xo Hd.aMu w :=
    { ref := ref, ref_deg := hra, ref_smooth := hrs, B := B, th_ref := hth, ph_eq := hph, ρ := ρ, «η» := cut,
      Cη := Cη, cutoff := hcut, e1 := fun t => max t (C / Real.log t⁻¹ + C * t),
      e1_ge := fun _ _ => le_max_left _ _ }
  have hT : S'.IsTied := by
    refine ⟨GlobalTheory.CompanionTheory.Ar.Cusp.breg_margin_tendsto C, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht j k x hx
    exact (hcmp t ht.1 ht.2 j k x hx).trans (le_max_right _ _)
  exact ⟨S', hT, GlobalTheory.CompanionTheory.Relay.symmetric_charts_of_regularization K J II Ψ Ω W D Hd M w S' κ hT hsym hρ hcc hrc (hcj hrc hO)⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_regularization_of_hodge_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D), ChartPsh D (phMu Hd) → ∃ S : LogLogRegularisationSetting M D.Xo (muLine Hd), S.IsTied := by
  first | exact @LevelTowerAlt.exists_tied_regular_setting | exact LevelTowerAlt.exists_tied_regular_setting
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.adjacent_swap_height_polynomial_relation : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d : ℕ) (S : AnSys (d + 1) (Ψ × Fin N)) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → SqSys Re (τ, a) (xiCoef τ a) → ∀ lam : Ψ × Fin N → ℝ, eval lam (toWt (Re.PB II)) + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) (toWt (Re.PB II)) = (tsgPoly (d + 1) kappa (linePoly (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) (xiCoef τ a) S.degPoly)).eval (gap lam (τ, a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.thmA_swap | exact GlobalTheory.CompanionTheory.Ar.PB.thmA_swap | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.thmA_swap <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem stepWeight_exists : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) → ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (B : FinHolAtlas e R.X), (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) → IsPotential R.A (BM.L.pullback pr hp.1) → IsSection R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m (fun k => pr ⁻¹' BM.W k) → IsAdaptedAtlas R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → ∃ (ph : R.X → ℝ) (C₅ : ℝ), (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x → Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) ∧ (∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → ph x = ph x') ∧ IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ιk fun k => M.dy p (κ k))) ph C₅ ∧ IsGradBound B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) ph C₅ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM p Kk _ ιk _ κ v hb hr e R pr hp B h1 hpot hsec hsnc had
  have hyp : IsStepHyp M BM p κ v R pr := ⟨hb, hr, hp, h1⟩
  have hc := GlobalTheory.T.flag_gap_pullback_third K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp
  have hfs : IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) :=
    (GlobalTheory.T.log_resolution_fubini_study_positive Kk ιk _ e R).1 _ (GlobalTheory.T.fubini_study_metric_smooth Kk ιk _)
  have hnorm : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  have hsm := GlobalTheory.T.flag_gap_holomorphic_pullback_first K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hps := GlobalTheory.T.flag_gap_holomorphic_pullback_second K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.flag_gap_holomorphic_pullback_third K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hgr := GlobalTheory.T.flag_gap_holomorphic_pullback_fourth K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.singular_potential_log_growth_psh e R.X R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm _ (stepPh M BM p v R pr) C₁ hfs hsm hps hC₁
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.T.adapted_atlas_smooth_potential_local e R.X R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm had (stepPh M BM p v R pr) hsm hgr
  refine ⟨stepPh M BM p v R pr, max C₂ C₃, ?_, ?_, ?_, hC₃ _ (le_max_right _ _)⟩
  · intro x hx z hz hzv
    have := GlobalTheory.T.flag_gap_pullback_first K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x z (R.mem_U x) hx hz hzv
    rw [this, stepGap]
    ring
  · intro x x' hxx hk
    exact GlobalTheory.T.flag_gap_pullback_second K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x' hxx hk
  · obtain ⟨h1', h2', h3', h4'⟩ := hC₂
    refine ⟨h1', h2', h3', fun x hx => ?_⟩
    have hlog : 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
      apply Real.log_nonneg
      have := hnorm x
      have h2 := Real.add_one_le_exp (1 : ℝ)
      unfold rW
      linarith
    obtain ⟨ha, hb'⟩ := h4' x hx
    refine ⟨?_, hb'.trans (le_max_left _ _)⟩
    have : -max C₂ C₃ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) ≤
        -C₂ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) :=
      mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left _ _)) hlog
    exact this.trans ha

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.local_holomorphic_lift_realisation : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (a : σ) (e : ℕ) (V : Set (Fin e → ℂ)) (ΦY : (Fin e → ℂ) → S.X) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (z : Fin e → ℂ), Re.J = ⊤ → Re.deg = 1 → Re.br = ∅ → IsOpen V → z ∈ V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, ∀ x₀, Re.π x₀ = ΦY u → SameOrbit (Re.R.lift x₀ x₀) (zex u)) → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, (S.th a).φ (ΦY z) (ΦY z') = Real.log ((Re.ref a).h (zex z')) + (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem continuousWithinAt_valAt {x : (Σ k, ι k) → Ω} {b₀ : (Σ k, ι k) → ℂ} (hb : b₀ ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal b₀) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) b₀ := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hx := ValRing.aeval_ne_zero_of_notMem hb hh hn
  have h0 := ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hne : ∀ᶠ b in 𝓝 b₀, eval b (map (Int.castRingHom ℂ) h) ≠ 0 := ch.continuousAt.eventually_ne h0
  have key : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] b₀]
      fun b => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hne] with b hbm hbn
    exact valAt_eq hbm ⟨d, g, h, hg, hh, hx, heq, hbn, rfl⟩
  have hq : ContinuousWithinAt
      (fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h))
      (mcPts (mCoordIdeal x)) b₀ := (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt
  exact hq.congr_of_eventuallyEq key (key.self_of_nhdsWithin hb)

end Values

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem continuousWithinAt_twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {A : Set Z} {z₀ : Z} {bs : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {pt : Z → (Σ k, ι k) → ℂ}
    (hbs : Continuous bs) (hpt : Continuous pt) (hA : Set.MapsTo bs A (mcPts (mCoordIdeal M.x))) (hz₀ : z₀ ∈ A)
    (hG : M.GoodAt F (mCoordIdeal (bs z₀))) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ)
    (J : Finset (Fin N)) : ContinuousWithinAt (fun z => twMinor M F (bs z) i k g (pt z) J) A z₀ := by
  unfold twMinor pluck
  refine tendsto_finsetSum _ fun I _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact (continuousWithinAt_valAt (hA hz₀) (hG.2.1 _ _).2).comp hbs.continuousWithinAt hA
  · exact ((continuous_apply _).comp hpt).continuousWithinAt

theorem isBlockMap_v₀ (k₀ : K) : IsBlockMap (some : K → Option K) (v₀ (ι := ι) k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, m⟩ ⟨k', m'⟩ e
    simp only [v₀] at e
    obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 e
    obtain rfl := Option.some_injective _ e1
    rw [eq_of_heq e2]
  · rintro ⟨_, m⟩ ⟨k, rfl⟩
    exact ⟨⟨k, m⟩, rfl⟩

theorem continuous_fstPt (k₀ : K) : Continuous (fstPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₀ k₀ p)

theorem continuous_sndPt (k₀ : K) : Continuous (sndPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₁ k₀ p)

theorem continuous_baseOf (M : FlagModel y Ψ N j) (k₀ : K) : Continuous (baseOf M k₀) :=
  continuous_pi fun q => continuous_apply (v₀ k₀ ⟨q.1.1, q.2⟩)

theorem fstPt_mem (M : FlagModel y Ψ N j) {d : ℕ} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N}
    (hb : (b : ℕ) = a + 1) (hba : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀)
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hV : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2))
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts (wP M τ a k₀ ca cb)) :
    fstPt k₀ z ∈ mcPts (mCoordIdeal y) := by
  have hI := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk hca hcb hV).2.2.2.1
  exact GlobalTheory.CompanionTheory.Ar.Chg.mem_mcPts_restr (isBlockMap_v₀ k₀) hI.ge hz

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∃ O' : Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen O' ∧ wO M Rb τ a k₀ ca cb F kb V r h = O' ∩ mcPts (wP M τ a k₀ ca cb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, -, hBC, hr, hrc, -⟩ := hc
  have hmaps : Set.MapsTo (baseOf M k₀) (mcPts (wP M τ a k₀ ca cb)) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    CPts.base_mem M (fstPt_mem M hb hba hk₀ hca hcb hAV hz)
  have key : ∀ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h,
      wO M Rb τ a k₀ ca cb F kb V r h ∈ 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀ := by
    rintro z₀ ⟨hz₀, hsrc, hV₀, hm₁, hm₂⟩
    have hbm := hmaps hz₀
    have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z₀)) := by
      obtain ⟨-, -, hgood, horb⟩ := hBC.2.2.2.2 _ hV₀
      rw [(Rb.A.chart kb).left_inv hsrc] at horb
      rwa [CovMap.mCoordIdeal_eq_of_sameOrbit (orbit_trans (orbit_symm (hr _ hbm)) horb)]
    have hrb : ContinuousWithinAt (fun z => r (baseOf M k₀ z)) (mcPts (wP M τ a k₀ ca cb)) z₀ :=
      (hrc _ hbm).comp (continuous_baseOf M k₀).continuousWithinAt hmaps
    have e₁ := hrb.tendsto.eventually_mem ((Rb.A.chart kb).open_source.mem_nhds hsrc)
    have e₂ := (((Rb.A.chart kb).continuousAt hsrc).tendsto.comp hrb.tendsto).eventually_mem (hBC.1.mem_nhds hV₀)
    have tw := fun (pt : _ → (Σ k, ι k) → ℂ) (hpt : Continuous pt) =>
      continuousWithinAt_twMinor M F (continuous_baseOf M k₀) hpt hmaps hz₀ hG
    have e₃ : ∀ᶠ z in 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀, ∀ p k, M.blk p = some k →
        twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := by
      refine eventually_all.2 fun p => eventually_all.2 fun k => ?_
      by_cases hp : M.blk p = some k
      · exact ((tw _ (continuous_fstPt k₀) p.2 k (h p.1)⁻¹ (stepCols N j p.2)).tendsto.eventually_ne
          (hm₁ p k hp)).mono fun _ hz _ => hz
      · exact Eventually.of_forall fun _ hp' => absurd hp' hp
    have e₄ := (tw _ (continuous_sndPt k₀) a k₀ (h τ)⁻¹ (stepCols N j a)).tendsto.eventually_ne hm₂
    filter_upwards [self_mem_nhdsWithin, e₁, e₂, e₃, e₄] with z h₀ h₁ h₂ h₃ h₄
    exact ⟨h₀, h₁, h₂, h₃, h₄⟩
  choose! U hU hmem hsub using fun z₀ (hz : z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h) =>
    mem_nhdsWithin.1 (key z₀ hz)
  refine ⟨⋃ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h, U z₀, isOpen_biUnion hU, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨Set.mem_biUnion hz (hmem z hz), hz.1⟩
  · rintro z ⟨hz, hzA⟩
    obtain ⟨z₀, h₀, hz₀⟩ := Set.mem_iUnion₂.1 hz
    exact hsub z₀ h₀ ⟨hz₀, hzA⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn
end
end
