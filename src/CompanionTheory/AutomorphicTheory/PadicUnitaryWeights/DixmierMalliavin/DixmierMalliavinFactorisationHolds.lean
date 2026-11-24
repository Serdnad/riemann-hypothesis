module

public import GroundTheory.AutomorphicForms.DixmierMalliavinProducts
public import GroundTheory.AutomorphicForms.HeckeAlgebra
public import GroundTheory.AutomorphicForms.DixmierMalliavinHaar
public import GroundTheory.AutomorphicForms.DixmierMalliavinLine
public import GroundTheory.AutomorphicForms.DixmierMalliavinSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
public import GroundTheory.AutomorphicForms.RealGroupsLie
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupport
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.DixmierMalliavinHaarDensity
import GroundTheory.AutomorphicForms.DixmierMalliavinHaarCoord
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DecompDirection, CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DixmierMalliavinFactorisationHolds

-- ===== clump member: CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DecompDirection =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DecompDirection", "h": "module\n\npublic import GroundTheory.AutomorphicForms.DixmierMalliavinProducts\npublic import GroundTheory.AutomorphicForms.HeckeAlgebra\npublic import GroundTheory.AutomorphicForms.DixmierMalliavinHaar\nimport GroundTheory.AutomorphicForms.DixmierMalliavinHaarCoord\npublic import GroundTheory.AutomorphicForms.DixmierMalliavinLine\npublic import GroundTheory.AutomorphicForms.DixmierMalliavinSeries\nimport GroundTheory.AutomorphicForms.GKModules.SmoothVectors\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace CompanionTheory.DM

open GroundTheory.Automorphic GroundTheory.Automorphic.IsExpLieAlgebra
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory Metric

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem decomp_direction {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f₁ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f₁) ∧
      tsupport f₁ ⊆ tsupport f ∧
      ∃ g k : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ k ∧ tsupport g ⊆ Icc (-ε) ε ∧
        tsupport k ⊆ Icc (-ε) ε ∧
        ∀ x, f x = (∫ t, g t * f₁ (h.expG (t • X) * x)) + ∫ t, k t * f (h.expG (t • X) * x) := by
  obtain ⟨f₁, hf₁, -, hf₁s, g, k, hg, hk, hgs, hks, hstep⟩ :=
    h.exists_decomp_direction_with_tsupport hf hfc X hε
  exact ⟨f₁, hf₁, hf₁s, g, k, hg, hk, hgs, hks, hstep⟩

theorem decomp_iter {ε : ℝ} (hε : 0 < ε) : ∀ {d : ℕ} (X : Fin d → 𝔤) (f : G → ℂ),
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) → HasCompactSupport f →
    ∃ (m : ℕ) (F : Fin m → G → ℂ) (K : Fin m → (Fin d → ℝ) → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (F i)) ∧
        tsupport (F i) ⊆ tsupport f) ∧
      (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ x, f x = ∑ i, ∫ t, K i t * F i (h.revProdExp X t * x) :=
  h.exists_decomp_iter_with_tsupport hε

theorem smooth_density [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ δ ≤ ε, ∀ K : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ K → tsupport K ⊆ closedBall 0 δ →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧ tsupport κ ⊆ h.prodExp (⇑b) '' closedBall 0 δ ∧
        ∀ φ : G → ℂ, Continuous φ → ∫ y, κ y * φ y ∂μ = ∫ t, K t * φ (h.prodExp (⇑b) t) := by
  obtain ⟨ε, hε, hdensity⟩ := h.exists_smooth_density_prodExp_with_tsupport μ b
  refine ⟨ε, hε, fun δ hδε K hK hKs => ?_⟩
  obtain ⟨κ, hκsmooth, hκcompact, hκsup, hκint⟩ :=
    hdensity K hK (hKs.trans (closedBall_subset_closedBall hδε))
  exact ⟨κ, hκsmooth, hκcompact, hκsup.trans (image_mono hKs), hκint⟩

include h in
theorem factor [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {V : Set G} (hV : V ∈ 𝓝 1) (f : G → ℂ)
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (hfc : HasCompactSupport f) :
    ∃ (n : ℕ) (φ ψ : Fin n → G → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (φ i)) ∧
        HasCompactSupport (φ i) ∧
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧ tsupport (φ i) ⊆ V ∧ tsupport (ψ i) ⊆ tsupport f) ∧
      f = ∑ i, groupConv μ (φ i) (ψ i) :=
  GroundTheory.Automorphic.dixmierMalliavin_with_tsupport h μ hV f hf hfc

end CompanionTheory.DM
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DecompDirection =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DixmierMalliavinFactorisationHolds =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DixmierMalliavinFactorisationHolds", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact\npublic import GroundTheory.AutomorphicForms.RealGroupsLie\npublic import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DecompDirection\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem\npublic import Mathlib.Analysis.Calculus.ContDiff.Defs\npublic import Mathlib.Analysis.InnerProductSpace.Basic\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Defs\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupport\nimport GroundTheory.AutomorphicForms.DixmierMalliavinSeries\nimport GroundTheory.AutomorphicForms.GKModules.SmoothVectors\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace CompanionTheory.DM

open GroundTheory.Automorphic GroundTheory.Automorphic.IsExpLieAlgebra GlobalTheory.Orb
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory Filter

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

theorem exists_lie (H : Subgroup 𝔸ˣ) (hH : IsClosed (H : Set 𝔸ˣ)) : ∃ 𝔤 : Submodule ℝ 𝔸, IsExpLieAlgebra H 𝔤 := by
  let M : Submonoid 𝔸 := (H.toSubmonoid.map (Units.coeHom 𝔸)).topologicalClosure
  have hc : IsClosed (M : Set 𝔸) := isClosed_closure
  have hsub : ∀ u ∈ H, (u : 𝔸) ∈ (M : Set 𝔸) := fun u hu => subset_closure ⟨u, hu, rfl⟩
  have hcl : ∀ u : 𝔸ˣ, (u : 𝔸) ∈ (M : Set 𝔸) → u ∈ H := fun u hu => by
    have : u ∈ closure (H : Set 𝔸ˣ) := by
      rw [Units.isOpenEmbedding_val.isInducing.closure_eq_preimage_closure_image]
      exact hu
    rwa [hH.closure_eq] at this
  have hm : ∀ a ∈ (M : Set 𝔸), ∀ b ∈ (M : Set 𝔸), a * b ∈ (M : Set 𝔸) := fun a ha b hb => M.mul_mem ha hb
  have hi : ∀ Z : 𝔸, exp Z ∈ (M : Set 𝔸) → exp (-Z) ∈ (M : Set 𝔸) := fun Z hZ =>
    hsub _ (H.inv_mem (hcl (expUnit ℝ 𝔸 Z) hZ))
  refine ⟨GlobalTheory.ClosedMatGroup.lieSub M hc M.one_mem hm, fun X hX => hcl _ (by simpa using hX 1), ?_⟩
  have hs := (expPartialHomeomorph ℝ 𝔸).open_source.mem_nhds (zero_mem_expPartialHomeomorph_source ℝ 𝔸)
  have h1 := GlobalTheory.ClosedMatGroup.eventually_exists_exp hc M.one_mem hm hi hs
  have h2 : Tendsto (exp : 𝔸 → 𝔸) (𝓝 0) (𝓝 1) := by
    simpa using (contDiff_exp ℝ 𝔸 (n := 0)).continuous.tendsto 0
  obtain ⟨U, hU, hUo, h0⟩ := mem_nhds_iff.1 ((h2.eventually h1).and hs)
  refine ⟨U, hUo, h0, fun X hX => (hU hX).2, fun X hX hG => ?_⟩
  obtain ⟨Y, hY, hY', e⟩ := (hU hX).1 (hsub _ hG)
  obtain rfl : Y = X := (expPartialHomeomorph ℝ 𝔸).injOn hY (hU hX).2 e
  exact hY'

theorem mem_ccSmooth_iff {H : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra H 𝔤) (f : H → ℂ) :
    f ∈ CcSmooth (fun x : H => ((x : 𝔸ˣ) : 𝔸)) ↔
      (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) ∧ HasCompactSupport f := by
  letI := h.chartedSpace
  constructor
  · rintro ⟨hc, Φ, hΦ, e⟩
    refine ⟨?_, hc⟩
    rw [show f = Φ ∘ fun x : H => ((x : 𝔸ˣ) : 𝔸) from funext e]
    exact hΦ.contMDiff.comp (h.contMDiff_val ∞)
  · rintro ⟨hf, hc⟩
    refine ⟨hc, _root_.GlobalTheory.glue_smooth_of_compactSupport H 𝔸 _ f (continuous_val_val H) hc fun a => ?_⟩
    have h1 : ContDiff ℝ ∞ fun Y : 𝔤 => f (a * h.expG Y) := by
      have := (h.contDiff_comp_expG_smul_mul_mul_expG hf 0 a).comp (contDiff_id.prodMk (contDiff_const (c := (0 : ℝ))))
      simpa [Function.comp_def, h.expG_zero] using this
    let L : 𝔸 → 𝔸 := fun y => ((a⁻¹ : H) : 𝔸ˣ) * y
    have hL : ContDiff ℝ ∞ L := contDiff_const.mul contDiff_id
    refine ⟨L ⁻¹' h.nhdOne, h.isOpen_nhdOne.preimage hL.continuous, ?_,
      fun y => f (a * h.expG (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm (L y)))), ?_, fun g hg => ?_⟩
    · simpa [L] using h.one_mem_nhdOne
    · exact (h1.comp (subspaceProj 𝔤).contDiff).comp_contDiffOn
        ((contDiffOn_expPartialHomeomorph_symm ℝ 𝔸).comp hL.contDiffOn fun y hy => h.nhdOne_subset_target hy)
    · exact congrArg f (h.chart_symm_chart (g := a) (x := g) hg).symm

theorem factor_abs {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (ι : G →* 𝔸) (hι : Topology.IsClosedEmbedding (ι.toHomUnits : G → 𝔸ˣ)) (μ : Measure G) [μ.IsHaarMeasure]
    {V : Set G} (hV : V ∈ 𝓝 1) {f : G → ℂ} (hf : f ∈ CcSmooth fun g => ι g) :
    ∃ (N : ℕ) (g k : Fin N → G → ℂ),
      (∀ i, g i ∈ CcSmooth (fun g => ι g) ∧ k i ∈ CcSmooth (fun g => ι g) ∧ tsupport (g i) ⊆ V ∧
        tsupport (k i) ⊆ tsupport f) ∧ f = ∑ i, GlobalTheory.AutomorphicL2Unitary.conv μ (g i) (k i) := by
  let H := ι.toHomUnits.range
  obtain ⟨𝔤, h⟩ := exists_lie H hι.isClosed_range
  let e : G ≃* H := MonoidHom.ofInjective hι.injective
  have he : ∀ g, (((e g : H) : 𝔸ˣ) : 𝔸) = ι g := fun g => rfl
  have c1 : Continuous e := hι.continuous.subtype_mk _
  have c2 : Continuous e.symm := hι.isEmbedding.continuous_iff.2 (continuous_subtype_val.congr fun x =>
    (congrArg Subtype.val (e.apply_symm_apply x)).symm)
  let E : G ≃ₜ H := ⟨e.toEquiv, c1, c2⟩
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  haveI := e.isHaarMeasure_map μ c1 c2
  have hf' : f ∘ E.symm ∈ CcSmooth (fun x : H => ((x : 𝔸ˣ) : 𝔸)) := by
    obtain ⟨hc, Φ, hΦ, e'⟩ := hf
    refine ⟨hc.comp_homeomorph E.symm, Φ, hΦ, fun x => ?_⟩
    rw [Function.comp_apply, e']
    exact congrArg (fun y : H => Φ ((y : 𝔸ˣ) : 𝔸)) (e.apply_symm_apply x)
  have back : ∀ φ : H → ℂ, φ ∈ CcSmooth (fun x : H => ((x : 𝔸ˣ) : 𝔸)) → φ ∘ E ∈ CcSmooth fun g => ι g :=
    fun φ ⟨hc, Φ, hΦ, e'⟩ => ⟨hc.comp_homeomorph E, Φ, hΦ, fun g => e' _⟩
  obtain ⟨hs, hc⟩ := (mem_ccSmooth_iff h _).1 hf'
  obtain ⟨N, φ, ψ, hp, hsum⟩ := factor h (μ.map e) (V := E.symm ⁻¹' V)
    (E.symm.continuous.continuousAt.preimage_mem_nhds (by rwa [show E.symm 1 = 1 from map_one e.symm])) _ hs hc
  refine ⟨N, fun i => φ i ∘ E, fun i => ψ i ∘ E, fun i => ⟨back _ ((mem_ccSmooth_iff h _).2 ⟨(hp i).1, (hp i).2.1⟩),
    back _ ((mem_ccSmooth_iff h _).2 ⟨(hp i).2.2.1, hc.of_isClosed_subset (isClosed_tsupport _) (hp i).2.2.2.2⟩),
    fun x hx => ?_, fun x hx => ?_⟩, funext fun x => ?_⟩
  · simpa using (hp i).2.2.2.1 (tsupport_comp_subset_preimage _ E.continuous hx)
  · simpa using tsupport_comp_subset_preimage _ E.symm.continuous
      ((hp i).2.2.2.2 (tsupport_comp_subset_preimage _ E.continuous hx))
  · have := congrFun hsum (E x)
    rw [Function.comp_apply, E.symm_apply_apply, Finset.sum_apply] at this
    rw [this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (E.measurableEmbedding.integral_map _).trans (integral_congr_ae (.of_forall fun y => ?_))
    show φ i (e y) * ψ i ((e y)⁻¹ * e x) = φ i (e y) * ψ i (e (y⁻¹ * x))
    rw [map_mul, map_inv]

end CompanionTheory.DM

open GlobalTheory.Orb in
theorem CompanionTheory.DM.dixmierMalliavinFactorisation_holds : GlobalTheory.Published.DixmierMalliavinFactorisation := by
  intro G _ _ _ _ _ n _ _ ι hι μ _ V hV f hf
  letI := Matrix.linftyOpNormedRing (n := n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := n) (α := ℂ)
  haveI : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℝ _
  let T : (n → n → ℂ) ≃L[ℝ] Matrix n n ℂ := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  have e : CcMat ι = CcSmooth fun g => ι g :=
    le_antisymm (ccSmooth_le (p := T.symm) T.symm.contDiff fun _ => rfl) (ccSmooth_le (p := T) T.contDiff fun _ => rfl)
  rw [e] at hf ⊢
  exact CompanionTheory.DM.factor_abs ι hι μ hV hf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DixmierMalliavinFactorisationHolds =====
