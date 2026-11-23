module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistDegree
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle143
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LeviNonnegSemipositiveLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle144
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle023
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun


theorem _root_.GlobalTheory.T.hodgeCpt_frame_twist_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (rk (CMType H) D.p D.q (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (n (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ))) = if a = b then 1 else 0) ∧ ∀ l, ((𝔐'.V (.inl τ)).gr (Fl.b (.inl τ)) l).IsGenAt p' (U l l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun


theorem _root_.GlobalTheory.T.hodgeCpt_frame_twist_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (rk (CMType H) D.p D.q (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (n (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ))) = if a = b then 1 else 0) ∧ ∀ l : Fin D.q, ((𝔐'.V (.inr τ)).gr (Fl.b (.inr τ)) l.rev).IsGenAt p' (U l l)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.flag_height : FlagHeight := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flagHeight_holds | exact GlobalTheory.CompanionTheory.Ar.PB.flagHeight_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flagHeight_holds <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.nef_polarization : NefPol := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.nefPol | exact GlobalTheory.CompanionTheory.Ar.PB.nefPol | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.nefPol <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree

section Transfer

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem modelChart_injOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ)) :
    Set.InjOn (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) := by
  intro u hu u' hu' h
  have h1 : χ.symm u = χ.symm u' := φ.injOn hu.2 hu'.2 h
  have h2 := congrArg χ h1
  rwa [χ.right_inv hu.1, χ.right_inv hu'.1] at h2

theorem modelChart_null (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (E : Set X)
    (hE : volume (χ.target ∩ χ.symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' (E ∩ χ.source)) = 0 := by
  have hd : DifferentiableOn ℝ (φ ∘ χ.symm)
      (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) :=
    (hσ.differentiableOn.restrictScalars ℝ).mono Set.inter_subset_left
  have h0 : volume (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) = 0 :=
    measure_mono_null (t := χ.target ∩ χ.symm ⁻¹' E) (fun u hu => ⟨hu.1.1, hu.2⟩) hE
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd h0
  refine measure_mono_null ?_ himg
  rintro y ⟨hy, hyE, hyχ⟩
  refine ⟨χ (φ.symm y), ⟨⟨χ.map_source hyχ, ?_⟩, ?_⟩, ?_⟩
  · show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv hyχ]; exact φ.map_target hy
  · show χ.symm (χ (φ.symm y)) ∈ E
    rw [χ.left_inv hyχ]; exact hyE
  · simp [χ.left_inv hyχ, φ.right_inv hy]

theorem modelChart_integrableOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (v : X → ℝ)
    (hv : ∀ Q ⊆ χ.target, IsCompact Q → IntegrableOn (fun y => v (χ.symm y)) Q)
    {Q : Set (Fin e → ℂ)} (hQ : IsCompact Q) (hQs : Q ⊆ φ.target ∩ φ.symm ⁻¹' χ.source) :
    IntegrableOn (fun y => v (φ.symm y)) Q := by
  have hSo : IsOpen (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    χ.isOpen_inter_preimage_symm φ.open_source
  have hρc : ContinuousOn (χ ∘ φ.symm) Q :=
    χ.continuousOn.comp (φ.continuousOn_symm.mono fun y hy => (hQs hy).1) fun y hy => (hQs hy).2
  have hQ' : IsCompact ((χ ∘ φ.symm) '' Q) := hQ.image_of_continuousOn hρc
  have hQS : (χ ∘ φ.symm) '' Q ⊆ χ.target ∩ χ.symm ⁻¹' φ.source := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨χ.map_source (hQs hy).2, ?_⟩
    show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv (hQs hy).2]; exact φ.map_target (hQs hy).1
  have himg : (φ ∘ χ.symm) '' ((χ ∘ φ.symm) '' Q) = Q := by
    rw [Set.image_image]
    refine Set.ext fun y => ⟨?_, fun hy => ⟨y, hy, ?_⟩⟩
    · rintro ⟨y', hy', rfl⟩
      simpa [χ.left_inv (hQs hy').2, φ.right_inv (hQs hy').1] using hy'
    · simp [χ.left_inv (hQs hy).2, φ.right_inv (hQs hy).1]
  have hσR : AnalyticOnNhd ℝ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    hσ.restrictScalars
  have hder : ∀ u ∈ (χ ∘ φ.symm) '' Q,
      HasFDerivWithinAt (φ ∘ χ.symm) (fderiv ℝ (φ ∘ χ.symm) u) ((χ ∘ φ.symm) '' Q) u :=
    fun u hu => ((hσR u (hQS hu)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hinj : Set.InjOn (φ ∘ χ.symm) ((χ ∘ φ.symm) '' Q) := (modelChart_injOn χ φ).mono hQS
  have hcont : ContinuousOn (fun u => |(fderiv ℝ (φ ∘ χ.symm) u).det|) ((χ ∘ φ.symm) '' Q) := by
    have h1 : ContinuousOn (fderiv ℝ (φ ∘ χ.symm)) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
      (hσR.fderiv).continuousOn
    exact (ContinuousLinearMap.continuous_det.comp_continuousOn (h1.mono hQS)).abs
  have hint := (hv _ (fun u hu => (hQS hu).1) hQ').continuousOn_mul hcont hQ'
  rw [← himg]
  refine (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hQ'.measurableSet hder
    hinj _).2 ?_
  refine hint.congr_fun (fun u hu => ?_) hQ'.measurableSet
  have hu := hQS hu
  simp only [smul_eq_mul, Function.comp_apply, φ.left_inv hu.2]

theorem modelChart_integrableOn_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (v : X → ℝ)
    (hv : ∀ k, ∀ Q ⊆ (χ k).target, IsCompact Q → IntegrableOn (fun y => v ((χ k).symm y)) Q) :
    LocallyIntegrableOn (fun y => v (φ.symm y)) φ.target := by
  intro y hy
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  have hWo : IsOpen (φ.target ∩ φ.symm ⁻¹' (χ k).source) :=
    φ.isOpen_inter_preimage_symm (χ k).open_source
  obtain ⟨Q, hQn, hQs, hQc⟩ := local_compact_nhds (hWo.mem_nhds ⟨hy, hk⟩)
  exact ⟨Q, mem_nhdsWithin_of_mem_nhds hQn, modelChart_integrableOn (χ k) φ (hσ k) v (hv k) hQc hQs⟩

theorem modelChart_null_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (E : Set X)
    (hE : ∀ k, volume ((χ k).target ∩ (χ k).symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' E) = 0 := by
  refine measure_mono_null (t := ⋃ k, φ.target ∩ φ.symm ⁻¹' (E ∩ (χ k).source)) ?_
    (measure_iUnion_null fun k => modelChart_null (χ k) φ (hσ k) E (hE k))
  rintro y ⟨hy, hyE⟩
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  exact Set.mem_iUnion.2 ⟨k, hy, hyE, hk⟩

end Transfer

theorem modelPtsIntegrable : ModelPtsIntegrable.Statement := by
  intro K _ ι _ P e M n ψ L c N E v g hV hL hN hψ hcov hE hv hg Ψ hΨ
  obtain ⟨Φ₀, hΦ₀, hloc⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K ι P e M L hL
  have hΦ : IsPotential M.atlas (Φ₀.rsmul c) := isPotentialRsmul M.atlas c Φ₀ hΦ₀
  have hli : ∀ j, LocallyIntegrableOn (fun y => v ((M.atlas.chart j).symm y))
      (M.atlas.chart j).target := fun j =>
    modelChart_integrableOn_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov v hv
  have hint : ∀ j, ∀ Q ⊆ (M.atlas.chart j).target, IsCompact Q →
      IntegrableOn (fun y => v ((M.atlas.chart j).symm y)) Q := fun j Q hQ hQc =>
    (hli j).integrableOn_compact_subset hQ hQc
  have hnull : ∀ j, volume ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' ((Set.univ : Set M.Xc)ᶜ ∪ E)) = 0 := fun j => by
    simpa using modelChart_null_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov E hE
  have hMI : MIntegrable M.atlas (fun _ : Fin e => Φ₀.rsmul c) v := fun j Q hQ hQc =>
    (hint j Q hQ hQc).mul_continuousOn
      ((locDensCont M.atlas _ (fun _ => hΦ) j).mono hQ) hQc
  refine ((GlobalTheory.T.mixed_integral_model_formula K ι P e M Ψ Set.univ E N (fun _ => c) (fun _ => L)
    (fun _ => Φ₀.rsmul c) g v hV hΨ isOpen_univ hnull hN ?_ ?_ ?_ ?_).2.2 hMI).1
  · exact fun _ x j => (hΦ.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · intro _ x y₀ hy₀
    obtain ⟨U, hUo, hyU, hUs, s, hs, hsh, G, hG, hGe⟩ := hloc x y₀ hy₀
    refine ⟨U, hUo, hyU, hUs, s, hs, hsh, fun z => (c : ℂ) * G z, holoOn_mul M.atlas hG c,
      fun y' hy' => ?_⟩
    have h1 : Φ₀.φ x y' - Real.log (L.h (s y')) = (G y').re := hGe y' hy'
    show c * Φ₀.φ x y' - c * Real.log (L.h (s y')) = ((c : ℂ) * G y').re
    rw [Complex.re_ofReal_mul, ← h1]
    ring
  · exact fun z hz hzN _ hzE => hg z hz hzN hzE
  · exact fun j => (hli j).aestronglyMeasurable

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.uniform_levi_positivity_on_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∃ δ > (0 : ℝ), ∀ a, ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, δ * ‖v‖ ^ 2 ≤ levi (fun t' => Real.log (D.A'.h ((D.chart a).γ t'))) t v := by
  first | exact @GlobalTheory.CompanionTheory.Relay.uniform_levi_positivity_on_charts | exact GlobalTheory.CompanionTheory.Relay.uniform_levi_positivity_on_charts | (intros; apply GlobalTheory.CompanionTheory.Relay.uniform_levi_positivity_on_charts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.semipositive_levi_of_log_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (A : HermLine J), IsSmoothHerm A → (∀ a, ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, 0 ≤ levi (fun t' => Real.log (A.h ((D.chart a).γ t'))) t v) → IsSemipositiveH (mCoordIdeal D.y) A := by
  first | exact @LevelTowerAlt.levi_nonneg_semipositive_line | exact LevelTowerAlt.levi_nonneg_semipositive_line
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.regularized_hodge_metric_smooth : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ), S.IsTied → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg Hd S B t) ∧ (muReg Hd S B t).a = muTwDeg Hd B ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muReg Hd S B t).h z) = Real.log (S.ref.h z) + S.regWeight t (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log | exact GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem continuous_of_atlasSmooth {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    have := (hf j).continuousOn
    simpa [Set.preimage_univ, Set.inter_univ] using this
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    (h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp
      ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem tendsto_ptsIntegral_of_chart_conv : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (Θ : LocPot M.Xc) (Pp : Fin n → LocPot M.Xc) (f : Fin n → M.Xc → ℝ) (fT : Fin n → ℝ → M.Xc → ℝ) (G : M.Xc → ℝ) (GT : ℝ → M.Xc → ℝ) (C : ℝ) (L : ℝ → Fin n → HermLine ι) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (n + 1) → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → (∀ i, IsPotential M.atlas (Pp i)) → (∀ i, M.atlas.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, M.atlas.Smooth (fT i t) ∧ IsPsh M.atlas (Pp i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (M.atlas.chart j).symm) (f i ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (f i ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (GT t) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i x, ∀ y₀ ∈ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G' : M.Xc → ℂ, M.atlas.HoloOn U G' ∧ ∀ y' ∈ U, (Pp i + LocPot.ofFun (fT i t)).φ x y' - Real.log ((L t i).h (s y')) = (G' y').re) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ mcPts P, g t z = GT t (M.proj z)) → ∃ l : ℝ, Tendsto (fun t => ptsIntegral P (pot (L t)) (g t)) (𝓝[>] 0) (𝓝 l) := by
  intro K _ ι _ P n M R Θ Pp f fT G GT C L g hV hΘ hΘp hP hf hfT hconv hGT hGc hrel hg
  classical
  by_cases hQ : ∃ Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj P Q
  · have hYo := (GlobalTheory.T.regular_chart_data_properties n M.Xc M.atlas R).1
    have hmeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable M.Xc ℝ (borel M.Xc) _ (R.Yo.indicator (GT t)) ∧
        ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x) := by
      filter_upwards [hGT] with t ht
      refine ⟨?_, ht.2⟩
      letI : MeasurableSpace M.Xc := borel M.Xc
      haveI : BorelSpace M.Xc := ⟨rfl⟩
      exact (continuous_of_atlasSmooth ht.1).measurable.indicator hYo.measurableSet
    obtain ⟨-, hint, hlim⟩ := GlobalTheory.T.mixed_integral_tendsto_off_divisor n M.Xc M.atlas R Θ hΘ hΘp Pp f fT G GT C hP hf hfT hconv
      hmeas hGc
    refine ⟨_, hlim.congr' ?_⟩
    filter_upwards [hint, hfT, hGT, hrel, hg] with t hit hft hgt hrt hgt'
    have hpush := GlobalTheory.T.mixed_integral_model_formula K ι P n M hQ.choose Set.univ ∅ ∅ (fun _ => 1) (L t)
      (fun i => Pp i + LocPot.ofFun (fT i t)) (g t) (GT t) hV hQ.choose_spec isOpen_univ
      (fun j => by simp)
      (fun Ψ _ => by simp)
      (fun i x => by
        intro j
        have h1 := (hP i).1 x j
        have h2 := (hft i).1 j
        have h3 := h1.add (h2.mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩))
        refine (h3.mono ?_).congr ?_
        · rintro y ⟨hy, hy'⟩
          exact ⟨hy, hy'.1.1⟩
        · intro y _
          rfl)
      (fun i x y₀ hy₀ => by
        obtain ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', hrel'⟩ := hrt i x y₀ hy₀
        exact ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', fun y' hy' => by
          simpa using hrel' y' hy'⟩)
      (fun z hz _ _ _ => hgt' z hz)
      (fun j => ((continuous_of_atlasSmooth hgt.1).comp_continuousOn
        (M.atlas.chart j).continuousOn_symm).aestronglyMeasurable (M.atlas.chart j).open_target.measurableSet)
    have h3 := (hpush.2.2 hit).2
    have hpot : (fun i z => (fun _ : Fin n => (1 : ℝ)) i * Real.log ((L t i).h z)) = pot (L t) := by
      funext i z
      simp [pot]
    rw [hpot] at h3
    rw [ptsIntegral, dite_eq_left hQ, h3]
  · refine ⟨0, ?_⟩
    have : (fun t => ptsIntegral P (pot (L t)) (g t)) = fun _ => (0 : ℝ) := by
      funext t
      rw [ptsIntegral, dite_eq_right hQ]
    rw [this]
    exact tendsto_const_nhds

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem _root_.GlobalTheory.T.big_line_implies_height_positivity : MoriwakiBigStatement → BirationalPullbackPushforwardFormula := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig | exact GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig <;> assumption)
end
