module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle718
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle347
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Algebra.Order.Chebyshev
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC


open GlobalTheory.EtC.MuTw in
theorem GlobalTheory.EtC.tw_one_mu : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  intro q _
  have hunit : ∀ (C : Type) [CommRing C], IsUnit (q : C) → IsUnit (q : Γ(Spec (CommRingCat.of C), ⊤)) := by
    intro C _ hC
    have := hC.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
    simpa using this
  let e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C) :=
    fun C _ hC =>
      ((AddEquiv.ofBijective ((etaS q).hom.app (op (Spec (CommRingCat.of C)))).hom.toAddMonoidHom
        ⟨GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q _ (hunit C hC), GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective q _ (hunit C hC)⟩).trans AddEquiv.ulift).trans
        (MulEquiv.restrictRootsOfUnity (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.toMulEquiv q).toAdditive
  refine ⟨e, ?_⟩
  intro C D _ _ φ hC hD x
  apply Units.ext
  have h1 := etaS_res q (Spec.map (CommRingCat.ofHom φ)) x
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (muVal q (Sec.map (etaS q) (Sec.res (Spec.map (CommRingCat.ofHom φ)) x))) = φ ((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (muVal q (Sec.map (etaS q) x)))
  rw [h1, muVal_res]
  exact congrArg (fun f => f.hom (muVal q (Sec.map (etaS q) x))) h2
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem nzStein_germ {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    -Real.log (A.nsq Λ τ y) = (A.ph Λ i y + 0) + Real.log (‖(τ i y)⁻¹‖ ^ 2) := by
  rw [A.nsq_eq_chart hs hy]
  have h1 : ‖τ i y‖ ^ 2 ≠ 0 := by positivity
  rw [Real.log_mul h1 (Real.exp_pos _).ne', Real.log_exp, norm_inv, inv_pow, Real.log_inv]
  ring

theorem nzStein_smoothLog {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => Real.log (‖(τ i x)⁻¹‖ ^ 2)) ∘ (A.chart i).symm) (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)
  have hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
    simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 i
  have hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) := by
    have h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
      (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT
    exact h.restrict_scalars ℝ
  have hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simpa [(A.chart i).left_inv hy] using hτ
  have hlog := ((hτc.inv hne).norm_sq ℝ).log (by simpa using hne)
  simpa [Function.comp_def] using hlog

theorem nzStein_smooth {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => (A.ph Λ i x + 0) + Real.log (‖(τ i x)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)
  have hph : ContDiffAt ℝ ∞ (A.ph Λ i ∘ (A.chart i).symm) (A.chart i y) :=
    (A.smooth_ph Λ i).contDiffAt hT
  have hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
    simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 i
  have hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
    by
    have h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
      (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT
    exact h.restrict_scalars ℝ
  have hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simpa [(A.chart i).left_inv hy] using hτ
  have hinv : ContDiffAt ℝ ∞ (fun v => ((τ i ∘ (A.chart i).symm) v)⁻¹) (A.chart i y) :=
    hτc.inv hne
  have hsq : ContDiffAt ℝ ∞ (fun v => ‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2) (A.chart i y) :=
    hinv.norm_sq ℝ
  have hlog : ContDiffAt ℝ ∞ (fun v => Real.log (‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2))
      (A.chart i y) :=
    hsq.log (by simpa using hne)
  exact (hph.add contDiffAt_const).add (by simpa [Function.comp_def] using hlog)

end GlobalTheory

namespace GlobalTheory

theorem nzEtaleStein : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n), A.IsSec Λ τ → A.Pos Λ (fun _ => 0) → Etale A (nz A τ) z → ∃ X : EtaleStein n (nz A τ), X.z = (fun y : nz A τ => z y) ∧ X.e = fun y : nz A τ => -Real.log (A.nsq Λ τ y) := by
  intro n Y _ _ _ _ _ _ ι La _ A Λ τ z hs hpos hE

  have hW : ∀ x ∈ nz A τ, ∀ᶠ y in 𝓝 x, (fun y => -Real.log (A.nsq Λ τ y)) y =
      (fun y => (A.ph Λ (A.pick x) y + 0) + Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) y := by
    intro x hx
    have hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ) :=
      (A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source
        isOpen_compl_singleton
    filter_upwards [hO.mem_nhds ⟨A.mem_pick x, hx⟩] with y hy
    exact nzStein_germ A hs (A.pick x) hy.1 hy.2
  have hT : ∀ x, Tendsto (A.chart (A.pick x)).symm (𝓝 (A.chart (A.pick x) x)) (𝓝 x) := by
    intro x
    have := (A.chart (A.pick x)).continuousAt_symm ((A.chart (A.pick x)).map_source (A.mem_pick x))
    rwa [ContinuousAt, (A.chart (A.pick x)).left_inv (A.mem_pick x)] at this
  have hsm : ∀ x ∈ nz A τ, ContDiffAt ℝ ∞
      ((fun y => -Real.log (A.nsq Λ τ y)) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x) := by
    intro x hx
    refine (nzStein_smooth A hs (A.pick x) (A.mem_pick x) hx).congr_of_eventuallyEq ?_
    filter_upwards [(hT x).eventually (hW x hx)] with v hv
    exact hv
  have hlev : ∀ x ∈ nz A τ, ∀ ξ : Fin n → ℂ,
      0 ≤ A.leviAt (A.pick x) (fun y => -Real.log (A.nsq Λ τ y)) x ξ := by
    intro x hx ξ
    have hxi : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
    rw [leviAt_congr A (A.pick x) _ _ x hxi (hW x hx) ξ]
    have hT' : (A.chart (A.pick x)).target ∈ 𝓝 (A.chart (A.pick x) x) :=
      (A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi)
    have hf : ContDiffAt ℝ 2 ((fun y => A.ph Λ (A.pick x) y + 0) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) := by
      have : ContDiffAt ℝ ∞ (A.ph Λ (A.pick x) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x) :=
        (A.smooth_ph Λ (A.pick x)).contDiffAt hT'
      exact (this.add contDiffAt_const).of_le (WithTop.coe_le_coe.mpr le_top)
    have hg : ContDiffAt ℝ 2
        ((fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      (nzStein_smoothLog A hs (A.pick x) hxi hx).of_le (WithTop.coe_le_coe.mpr le_top)
    have hd : DifferentiableOn ℂ (τ (A.pick x) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x)).target := by
      simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 (A.pick x)
    have hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ) :=
      (A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source
        isOpen_compl_singleton
    have hh : ∀ᶠ v in 𝓝 (A.chart (A.pick x) x),
        DifferentiableAt ℂ ((fun y => (τ (A.pick x) y)⁻¹) ∘ (A.chart (A.pick x)).symm) v := by
      filter_upwards [(A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi),
        (hT x).eventually (hO.mem_nhds ⟨hxi, hx⟩)] with v hv1 hv2
      exact (hd.differentiableAt ((A.chart (A.pick x)).open_target.mem_nhds hv1)).inv hv2.2
    have E1 := leviAt_add A (A.pick x) (fun y => A.ph Λ (A.pick x) y + 0)
      (fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) x hf hg ξ
    have E2 := leviAt_log_normSq A (A.pick x) (fun y => (τ (A.pick x) y)⁻¹) x hxi hh (inv_ne_zero hx) ξ
    have hp := hpos (A.pick x) x hxi ξ
    simp only at E1 E2 hp
    rw [E1, E2]
    linarith
  have hLH : IsLocalHomeomorph (fun y : nz A τ => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A _ z hE
  have hSm : SmoothR n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y)) :=
    (GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts n Y ι La A _ z hE).2 (fun y => -Real.log (A.nsq Λ τ y))
      (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx⟩)
  have hLv : LeviNonneg n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y)) :=
    GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic n Y ι La A _ z hE (fun y => -Real.log (A.nsq Λ τ y))
      (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx, hlev x hx⟩)
  have hC : ∀ a : ℝ, IsCompact {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a} := by
    intro a
    have hK : IsCompact {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} :=
      (isClosed_le continuous_const (A.continuous_nsq hs)).isCompact
    have hsub : {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} ⊆ nz A τ := by
      intro y hy
      show τ (A.pick y) y ≠ 0
      intro h0
      have h1 : Real.exp (-a) ≤ A.nsq Λ τ y := hy
      have h2 : A.nsq Λ τ y = 0 := by simp [WeightedAtlas.nsq, h0]
      have := Real.exp_pos (-a)
      linarith
    have heq : {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a} =
        Subtype.val ⁻¹' {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} := by
      ext ⟨y, hy⟩
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      have hne : τ (A.pick y) y ≠ 0 := hy
      have hp : 0 < A.nsq Λ τ y := by
        unfold WeightedAtlas.nsq
        positivity
      rw [neg_le, Real.le_log_iff_exp_le hp]
    rw [heq, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub)]
    exact hK
  exact ⟨⟨fun y => z y, hLH, fun y => -Real.log (A.nsq Λ τ y), hSm, hLv, hC⟩, rfl, rfl⟩

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CcStep

theorem cc_step : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r ∧ ContCone R F ((bc (sch.map r)).mapCone c)) → ContCone R F ((bc p).mapCone c) := by
  intro R _ F S E p I _ _ G c h
  apply GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise R F I (G ⋙ bc p) ((bc p).mapCone c)
  intro k
  obtain ⟨X, r, e, he, hc⟩ := h k
  obtain ⟨φ⟩ := GlobalTheory.EtC.BcLevel.bc_level S E p k X r e he
  have hiso := (GlobalTheory.EtC.eqv_basic R F).1
  refine (GlobalTheory.EtC.ContCone.iff_of_eqv R F I (G ⋙ bc (sch.map r)) ((G ⋙ bc p) ⋙ (evaluation _ PSh).obj k ⋙ disc)
    ((bc (sch.map r)).mapCone c) (((evaluation _ PSh).obj k ⋙ disc).mapCone ((bc p).mapCone c))
    (Functor.whiskerLeft G φ.hom) (φ.hom.app c.pt) ?_ ?_ ?_).1 hc
  · intro i
    exact φ.hom.naturality (c.π.app i)
  · intro i
    exact hiso _ _ _ inferInstance
  · exact hiso _ _ _ inferInstance

end GlobalTheory.EtC.CcStep
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.holo_iff_differentiableOn_charts_of_etale : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ u : Y → ℂ, (Holo n (fun y : U => z y) (fun y : U => u y) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) := by
  first | exact @GlobalTheory.holo_etale_iff_charts | exact GlobalTheory.holo_etale_iff_charts | (intros; apply GlobalTheory.holo_etale_iff_charts <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.GlueEnergy

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] {A : WeightedAtlas n Y ι La}

theorem exists_bound (C : Cover A) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a b j, ∀ v ∈ ball (C.c b) (C.r b),
    ‖wdb n j (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ)) v‖ ≤ B := by
  have h : ∀ p : Fin C.m × Fin C.m × Fin n, ∃ B : ℝ, ∀ v ∈ closedBall (C.c p.2.1) (C.r p.2.1),
      ‖wdb n p.2.2 (fun x => (C.chi p.1 ((A.chart (C.idx p.2.1)).symm x) : ℂ)) v‖ ≤ B := by
    rintro ⟨a, b, j⟩
    apply (isCompact_closedBall _ _).exists_bound_of_continuousOn
    refine ContinuousOn.mono ?_ (C.sub b)
    have h1 : ContDiffOn ℝ ∞ (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ))
        (A.chart (C.idx b)).target :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (C.smooth a (C.idx b))
    have h2 := h1.continuousOn_fderiv_of_isOpen (A.chart (C.idx b)).open_target (by simp)
    unfold wdb
    exact ((h2.clm_apply continuousOn_const).add
      (continuousOn_const.mul (h2.clm_apply continuousOn_const))).div_const _
  choose B hB using h
  refine ⟨∑ p, |B p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun a b j v hv => ?_⟩
  exact ((hB (a, b, j) v (ball_subset_closedBall hv)).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun p => |B p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem wdb_eq_zero (C : Cover A) (a : Fin C.m) (i : ι) (j : Fin n) (v : V n)
    (hv : v ∈ (A.chart i).target)
    (h : (A.chart i).symm v ∉
      (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :
    wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
  have h1 : (A.chart i).symm v ∉ tsupport (C.chi a) := fun h' => h (C.supp a h')
  have h2 := notMem_tsupport_iff_eventuallyEq.mp h1
  have h3 := ((A.chart i).continuousAt_symm hv).eventually h2
  have h4 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => 0 :=
    h3.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]
  unfold wdb
  rw [h4.fderiv_eq]
  simp

theorem sq_sum_le {m : ℕ} (x d : Fin m → ℂ) (B : ℝ) (e : Fin m → ℝ)
    (h : ∀ a, ‖x a * d a‖ ^ 2 ≤ B ^ 2 * e a) :
    ‖∑ a, x a * d a‖ ^ 2 ≤ m * B ^ 2 * ∑ a, e a := by
  calc ‖∑ a, x a * d a‖ ^ 2 ≤ (∑ a, ‖x a * d a‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ m * ∑ a, ‖x a * d a‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖x a * d a‖)
    _ ≤ m * ∑ a, B ^ 2 * e a := by gcongr with a; exact h a
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem energy_glue_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n1 C la (glue C la u) ≤ ENNReal.ofReal K * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨B, hB0, hB⟩ := exists_bound C
  refine ⟨C.m * (n * (C.m * B ^ 2)), by positivity, fun la F0 u hF hu => ?_⟩
  set D : Fin C.m → ι → Y → ℂ := fun a i y =>
    A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y) - F0 i y with hD
  set U : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hU
  have hUo : ∀ a, IsOpen (U a) := fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hbt : ∀ b, ball (C.c b) (C.r b) ⊆ (A.chart (C.idx b)).target := fun b =>
    ball_subset_closedBall.trans (C.sub b)
  set W : Fin C.m → Fin C.m → Set (V n) := fun b a =>
    ball (C.c b) (C.r b) ∩ ((A.chart (C.idx b)).target ∩ (A.chart (C.idx b)).symm ⁻¹' U a) with hW
  have hWo : ∀ b a, IsOpen (W b a) := fun b a =>
    isOpen_ball.inter ((A.chart (C.idx b)).isOpen_inter_preimage_symm (hUo a))
  have hDc : ∀ b a, ContinuousOn (D a (C.idx b) ∘ (A.chart (C.idx b)).symm) (W b a) := by
    intro b a
    have hov : W b a ⊆ ovl A.chart (C.idx b) (C.idx a) := fun v hv => ⟨hv.2.1, hv.2.2.1⟩
    have h1 := (A.holo_g (A.kap + la) (C.idx b) (C.idx a)).continuousOn.mono hov
    have h2 := (A.holo_trans (C.idx b) (C.idx a)).continuousOn.mono hov
    have h3 := (hu a).continuousOn.comp h2 (fun v hv => hv.2.2.2)
    have h4 := (hF.1 (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact (h1.mul h3).sub h4
  have hcomp : ∀ a i y, y ∈ (A.chart i).source → y ∈ (A.chart (C.idx a)).source →
      D a (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D a i y := by
    intro a i y hi ha
    simp only [hD]
    rw [A.g_cocycle _ (A.pick y) i (C.idx a) y (A.mem_pick y) hi ha,
      hF.2 (A.pick y) i y (A.mem_pick y) hi]
    ring
  set f : Fin C.m → Fin C.m → V n → ℝ≥0∞ := fun b a v => ENNReal.ofReal
    (‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2 *
      Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) with hf
  have hk : ∀ b a, ∫⁻ y in (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' W b a,
      ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu = ∫⁻ v in W b a, f b a v := by
    intro b a
    refine GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx b) (W b a) (D a) (hWo b a).measurableSet
      (fun v hv => hv.2.1) (fun y hy hy' => hcomp a _ y hy ?_)
      ((hDc b a).aemeasurable (hWo b a).measurableSet)
    have := hy'.2.2.1
    rwa [(A.chart (C.idx b)).left_inv hy] at this
  have hWaa : ∀ a, W a a = ball (C.c a) (C.r a) := by
    intro a
    refine Set.inter_eq_left.mpr fun v hv => ⟨hbt a hv, (A.chart _).map_target (hbt a hv), ?_⟩
    show A.chart (C.idx a) ((A.chart (C.idx a)).symm v) ∈ ball (C.c a) (C.r a)
    rwa [(A.chart (C.idx a)).right_inv (hbt a hv)]
  have hE : ∀ b a, ∫⁻ v in W b a, f b a v ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro b a
    calc _ = _ := (hk b a).symm
      _ ≤ ∫⁻ y in (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' W a a,
          ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu := by
        apply lintegral_mono_set
        intro y hy
        rw [hWaa]
        have := hy.2.2.2
        rwa [Set.mem_preimage, (A.chart (C.idx b)).left_inv hy.1] at this
      _ = _ := hk a a
      _ = _ := by
        rw [hWaa]
        refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
        have hs := (A.chart (C.idx a)).map_target (hbt a hv)
        have h1 : A.g (A.kap + la) (C.idx a) (C.idx a) ((A.chart (C.idx a)).symm v) = 1 := by
          have h2 := A.g_cocycle (A.kap + la) _ _ _ _ hs hs hs
          have h3 := A.g_ne (A.kap + la) _ _ _ hs hs
          exact (mul_right_eq_self₀.mp h2.symm).resolve_right h3
        simp only [hf, hD]
        rw [h1, one_mul, (A.chart (C.idx a)).right_inv (hbt a hv), norm_sub_rev]
  have hfm : ∀ b a, AEMeasurable ((W b a).indicator (f b a))
      (volume.restrict (ball (C.c b) (C.r b))) := by
    intro b a
    refine AEMeasurable.restrict ?_
    rw [aemeasurable_indicator_iff (hWo b a).measurableSet]
    refine ContinuousOn.aemeasurable ?_ (hWo b a).measurableSet
    have h4 := (A.smooth_ph la (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (((hDc b a).norm.pow 2).mul (Real.continuous_exp.comp_continuousOn h4.neg))
  have hpt : ∀ b, ∀ v ∈ ball (C.c b) (C.r b), ENNReal.ofReal
      ((∑ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) ≤
      ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a, (W b a).indicator (f b a) v := by
    intro b v hv
    set e : Fin C.m → ℝ := fun a => (W b a).indicator
      (fun v => ‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2) v with he
    have he0 : ∀ a, 0 ≤ e a := fun a => Set.indicator_nonneg (fun _ _ => by positivity) _
    have h1 : ∀ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2 ≤
        C.m * B ^ 2 * ∑ a, e a := by
      intro j
      rw [GlobalTheory.T.dbar_glueSectionByPartition_eq n Y ι La A C la u (C.idx b) v (F0 (C.idx b) ((A.chart (C.idx b)).symm v))
        j hu (hbt b hv)]
      apply sq_sum_le
      intro a
      by_cases hm : v ∈ W b a
      · simp only [he, Set.indicator_of_mem hm, hD]
        rw [norm_mul, mul_pow]
        gcongr
        exact hB a b j v hv
      · rw [wdb_eq_zero C a (C.idx b) j v (hbt b hv) (fun h => hm ⟨hv, hbt b hv, h⟩)]
        simp only [zero_mul, norm_zero]
        have := he0 a
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    have h2 : ∑ a, (W b a).indicator (f b a) v = ENNReal.ofReal ((∑ a, e a) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
        (fun a _ => mul_nonneg (he0 a) (Real.exp_pos _).le)]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hm : v ∈ W b a
      · simp only [he, hf, Set.indicator_of_mem hm]
      · simp [he, Set.indicator_of_notMem hm]
    rw [h2, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    apply ENNReal.ofReal_le_ofReal
    gcongr
    calc _ ≤ ∑ _j : Fin n, C.m * B ^ 2 * ∑ a, e a := Finset.sum_le_sum fun j _ => h1 j
      _ = _ := by simp [mul_assoc]
  unfold n1
  calc _ ≤ ∑ _b : Fin C.m, ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a,
        ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
        refine Finset.sum_le_sum fun b _ => ?_
        refine (setLIntegral_mono' measurableSet_ball (hpt b)).trans ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ (fun a _ => hfm b a)]
        refine mul_le_mul_right (Finset.sum_le_sum fun a _ => ?_) _
        refine le_trans (setLIntegral_le_lintegral _ _) ?_
        rw [lintegral_indicator (hWo b a).measurableSet]
        exact hE b a
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (C.m : ℝ)) (by positivity), ENNReal.ofReal_natCast, mul_assoc]

end GlobalTheory.OTY.GlueEnergy
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  first | exact @GlobalTheory.WpFam.TrAdd.main | exact GlobalTheory.WpFam.TrAdd.main | (intros; apply GlobalTheory.WpFam.TrAdd.main <;> assumption)
end
