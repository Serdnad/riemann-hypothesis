module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle415
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.OpenOrbit

open Set Filter GlobalTheory.Eis

variable {D : D7} {V : HSp D}

theorem io_one_mul (δ : GA D V) (x : GA D V × GA D V) : io V (δ, 1) * io V x = io V (δ * x.1, x.2) := by
  rw [← map_mul]; congr 1; ext <;> simp

section Terms

variable {μ : (AE D)ˣ →* Circle} {φ : GA D (dblSp V) → ℂ} {f₁ f₂ : GA D V → ℂ}

theorem term_eq (hf₁ : ∀ γ ∈ GQ V, ∀ g, f₁ (γ * g) = f₁ g) (δ : GQ V) (x : GA D V × GA D V) :
    dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ x =
      dblIntegrand V μ φ f₁ f₂ ((δ : GA D V) * x.1, x.2) := by
  simp only [dblIntegrand, io_one_mul, hf₁ _ δ.2]

theorem tsum_open_ne_top (hμ : IsHeckeChar D μ) {a : GL (Fin V.rank) (AE D)} {s : ℂ} (hφ : φ ∈ degPS V a μ s)
    {m : Measure (GA D V)} [SFinite m] {𝓕 : Set (GA D V)}
    (h : ∑' q : SiegelCosets V, ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m ≠ ⊤) :
    ∑' δ : GQ V, ∫⁻ x, ‖dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ x‖ₑ
      ∂(m.restrict 𝓕).prod (m.restrict 𝓕) ≠ ⊤ := by
  rw [Measure.prod_restrict]
  refine ne_top_of_le_ne_top h (le_trans (le_of_eq (tsum_congr fun δ => ?_))
    (ENNReal.tsum_comp_le_tsum_of_injective (injective_mk_io (V := V)) (fun q : SiegelCosets V => ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m)))
  set q : SiegelCosets V := mk _ ⟨io V (δ, 1), io_mem_GQ V δ.2 (one_mem _)⟩ with hq
  have e : (mk _ q.out : SiegelCosets V) = mk _ ⟨io V (δ, 1), io_mem_GQ V δ.2 (one_mem _)⟩ := Quotient.out_eq q
  obtain ⟨p, hp⟩ := mk_eq_iff.1 e
  have hE : (fun y => φ (io V (δ, 1) * y)) = fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x) := by
    funext y
    have h1 : io V (δ, 1) = ((p : GQ (dblSp V)) : GA D (dblSp V)) * ((q.out : GQ (dblSp V)) : GA D (dblSp V)) :=
      (congrArg Subtype.val hp).symm
    rw [h1, mul_assoc]
    exact apply_siegelQ_mul V a hμ hφ ⟨Subgroup.mem_subgroupOf.1 p.2, (p : GQ (dblSp V)).2⟩ _
  beta_reduce
  rw [hE]

theorem leftInv_open (hμ : IsHeckeChar D μ) {a : GL (Fin V.rank) (AE D)} {s : ℂ} (hφ : φ ∈ degPS V a μ s)
    (hf₁ : ∀ γ ∈ GQ V, ∀ g, f₁ (γ * g) = f₁ g) (hf₂ : ∀ γ ∈ GQ V, ∀ g, f₂ (γ * g) = f₂ g) :
    LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂) := by
  rintro ⟨γ₁, γ₂⟩ ⟨h1, h2⟩ ⟨x₁, x₂⟩
  have hs : ∑' δ : GQ V, φ (io V (δ, 1) * io V ((γ₁, γ₂) * (x₁, x₂))) =
      ∑' δ : GQ V, φ (io V (δ, 1) * io V (x₁, x₂)) := by
    let e : GQ V ≃ GQ V := (Equiv.mulLeft (⟨γ₂, h2⟩ : GQ V)⁻¹).trans (Equiv.mulRight ⟨γ₁, h1⟩)
    conv_rhs => rw [← e.tsum_eq]
    refine tsum_congr fun δ => ?_
    simp only [io_one_mul, Prod.mk_mul_mk]
    have := apply_io_mul V a hφ γ₂ ((e δ : GA D V) * x₁) x₂
    rw [apply_detA hμ h2, Circle.coe_one, one_mul] at this
    rw [← this]
    congr 3
    simp [e, mul_assoc]
  simp only [dblIntegrand]
  rw [hs]
  simp only [Prod.mk_mul_mk, hf₁ _ h1, hf₂ _ h2, map_mul, apply_detA hμ h2, one_mul]

end Terms

theorem open_orbit : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ZetaConvH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) ∧ ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = zetaH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  haveI := hm
  have hF : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  set 𝓕 := stdDom (GQ V) with h𝓕
  have hφc : Continuous φ := hφ.2.1
  set E : GA D (dblSp V) → ℂ := fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y) with hEdef
  set H : GA D V × GA D V → ℂ := dblIntegrand V μ φ f₁ f₂ with hHdef
  set T : GQ V → GA D V × GA D V → ℂ := fun δ => dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ with hTdef
  set K : GA D V × GA D V → ℂ := fun p => H (p.1 * p.2, p.1) with hKdef
  have hHc : Continuous H := continuous_dblIntegrand hμ hφc h₁.continuous h₂.continuous
  have hT : ∀ (δ : GQ V) (x : GA D V × GA D V), T δ x = H ((δ : GA D V) * x.1, x.2) := fun δ x => term_eq h₁.1 δ x
  have hTc : ∀ δ : GQ V, Continuous (T δ) := fun δ => by
    rw [show T δ = fun x => H ((δ : GA D V) * x.1, x.2) from funext (hT δ)]
    exact hHc.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hTm : ∀ δ : GQ V, Measurable fun x => ‖T δ x‖ₑ := fun δ => (hTc δ).measurable.enorm
  have hKc : Continuous K := hHc.comp ((continuous_fst.mul continuous_snd).prodMk continuous_fst)

  have hbd : ∑' δ : GQ V, ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕) ≠ ⊤ :=
    tsum_open_ne_top hμ hφ ((GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂).1 𝓕 hF)
  have hTint : ∀ δ : GQ V, Integrable (T δ) ((m.restrict 𝓕).prod (m.restrict 𝓕)) := fun δ =>
    ⟨(hTc δ).aestronglyMeasurable, lt_of_le_of_lt
      (ENNReal.le_tsum (f := fun δ : GQ V => ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕)) δ)
      (lt_top_iff_ne_top.2 hbd)⟩

  have hlin : ∀ x₂, ∫⁻ x₁, ‖H (x₁, x₂)‖ₑ ∂m = ∑' δ : GQ V, ∫⁻ x₁ in 𝓕, ‖T δ (x₁, x₂)‖ₑ ∂m := fun x₂ => by
    rw [hF.lintegral_eq_tsum'' (fun x₁ => ‖H (x₁, x₂)‖ₑ)]
    refine tsum_congr fun δ => ?_
    simp only [hT, Subgroup.smul_def, smul_eq_mul]
  have hlK : ∫⁻ p, ‖K p‖ₑ ∂(m.restrict 𝓕).prod m =
      ∑' δ : GQ V, ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [lintegral_prod _ hKc.measurable.enorm.aemeasurable]
    have h1 : ∀ x₂, ∫⁻ g, ‖K (x₂, g)‖ₑ ∂m = ∫⁻ x₁, ‖H (x₁, x₂)‖ₑ ∂m := fun x₂ =>
      lintegral_mul_left_eq_self (fun x₁ => ‖H (x₁, x₂)‖ₑ) x₂
    simp_rw [h1, hlin]
    rw [lintegral_tsum (fun δ => ((hTm δ).lintegral_prod_left').aemeasurable)]
    refine tsum_congr fun δ => ?_
    rw [lintegral_prod_symm _ (hTm δ).aemeasurable]
  have hKint : Integrable K ((m.restrict 𝓕).prod m) :=
    ⟨hKc.aestronglyMeasurable, show ∫⁻ p, ‖K p‖ₑ ∂(m.restrict 𝓕).prod m < ⊤ by rw [hlK]; exact lt_top_iff_ne_top.2 hbd⟩
  have hHint : ∀ᵐ x₂ ∂(m.restrict 𝓕), Integrable (fun x₁ => H (x₁, x₂)) m := by
    filter_upwards [hKint.prod_right_ae] with x₂ hx
    have := hx.comp_mul_left x₂⁻¹
    simpa [hKdef, mul_inv_cancel_left] using this

  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_open hμ hφ h₁.1 h₂.1
  have hQ : dblIntegrandQ V μ E f₁ f₂ = dblIntegrand V μ E f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
    funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk hli _ _)
  have hmp : MeasurePreserving (Prod.map (sec (GQ V)) (sec (GQ V))) ((autMeasure V m).prod (autMeasure V m))
      ((m.restrict 𝓕).prod (m.restrict 𝓕)) := measurePreserving_sec.prod measurePreserving_sec
  have S3 : ∫ q, dblIntegrandQ V μ E f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m) =
      ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [hQ]; exact hmp.integral_comp (measurableEmbedding_sec.prodMap measurableEmbedding_sec) _
  have S4 : ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) =
      ∑' δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [← integral_tsum (fun δ => (hTc δ).aestronglyMeasurable) hbd]
    congr 1; funext x
    simp only [hTdef, hEdef, dblIntegrand, mul_assoc]
    exact tsum_mul_right.symm
  have S5 : ∀ δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) =
      ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := fun δ => integral_prod_symm _ (hTint δ)
  have S6 : ∑' δ : GQ V, ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m =
      ∫ x₂ in 𝓕, ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := by
    refine (integral_tsum (fun δ => ?_) ?_).symm
    · exact (((hTc δ).comp continuous_swap).aestronglyMeasurable
        (μ := (m.restrict 𝓕).prod (m.restrict 𝓕))).integral_prod_right'
    · refine ne_top_of_le_ne_top hbd (ENNReal.tsum_le_tsum fun δ => ?_)
      rw [lintegral_prod_symm _ (hTm δ).aemeasurable]
      exact lintegral_mono fun x₂ => enorm_integral_le_lintegral_enorm _
  have S7 : ∀ᵐ x₂ ∂(m.restrict 𝓕), ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m = ∫ x₁, H (x₁, x₂) ∂m := by
    filter_upwards [hHint] with x₂ hx
    rw [hF.integral_eq_tsum'' _ hx]
    refine tsum_congr fun δ => ?_
    simp only [hT, Subgroup.smul_def, smul_eq_mul]
  have S8 : ∀ x₂, ∫ x₁, H (x₁, x₂) ∂m = ∫ g, K (x₂, g) ∂m := fun x₂ =>
    (integral_mul_left_eq_self (fun x₁ => H (x₁, x₂)) x₂).symm
  have S9 : ∫ x₂ in 𝓕, ∫ g, K (x₂, g) ∂m ∂m = ∫ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m ∂m := by
    rw [← integral_prod _ hKint, integral_prod_symm _ hKint]
  have MirabolicColumnBlock : ∀ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m = φ (io V (g, 1)) * conj (petCoef V m f₁ f₂ g) := fun g => by
    have hl1 : LeftInv (GQ V) (rTr V g f₁) := fun γ hγ x => (h₁.mul_right g).1 γ hγ x
    have hl2 : LeftInv (GQ V) f₂ := h₂.1
    simp only [petCoef]
    rw [petersson_eq hF hl1 hl2, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x₂ => ?_)
    simp only [hKdef, hHdef, dblIntegrand_mul hφ, rTr, map_mul, Complex.conj_conj]
    ring
  refine ⟨?_, ?_⟩
  · rw [zetaConvH_iff]
    exact hKint.integral_prod_right.congr (Eventually.of_forall fun g => MirabolicColumnBlock g)
  · calc ∫ q, dblIntegrandQ V μ E f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m)
        = ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := S3
      _ = ∑' δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := S4
      _ = ∑' δ : GQ V, ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := tsum_congr S5
      _ = ∫ x₂ in 𝓕, ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := S6
      _ = ∫ x₂ in 𝓕, ∫ x₁, H (x₁, x₂) ∂m ∂m := integral_congr_ae S7
      _ = ∫ x₂ in 𝓕, ∫ g, K (x₂, g) ∂m ∂m := integral_congr_ae (Eventually.of_forall S8)
      _ = ∫ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m ∂m := S9
      _ = ∫ g, φ (io V (g, 1)) * conj (petCoef V m f₁ f₂ g) ∂m := integral_congr_ae (Eventually.of_forall MirabolicColumnBlock)
      _ = zetaH D.sp.cm.sig (gram_hdbl V) m φ (petCoef V m f₁ f₂) := (zetaH_eq _ _ _ _).symm

end GlobalTheory.Core.Rk.OpenOrbit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitFormUnitary_integralEntries_of_levelLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J = 1 → ∀ (t : 𝓞 E), (t : E) ≠ 0 → ∀ (Λ : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ Formalism.UG.levelVL σ J v Λ → ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring := by
  first | exact @GlobalTheory.UnitLevelInt.entry_mem_of_levelVL | exact GlobalTheory.UnitLevelInt.entry_mem_of_levelVL | (intros; apply GlobalTheory.UnitLevelInt.entry_mem_of_levelVL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

theorem lattice_exists_scalar_bound_attained : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → Nonempty n → ∃ c : k, c ≠ 0 ∧ (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ x ∈ L, ∃ j, x j = c := by
  intro k _ _ _ _ n _ L hL hn
  obtain ⟨s, hs⟩ := hL.fg

  have hex : ∃ x ∈ s, ∃ j, x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : L = ⊥ := by
      rw [← hs, Submodule.span_eq_bot]
      intro x hx
      funext j
      exact hcon x hx j
    have htop := hL.span_eq_top
    rw [hbot] at htop
    simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at htop
    obtain ⟨j⟩ := hn
    have h1 : (Pi.single j (1 : k) : n → k) ∈ (⊤ : Submodule k (n → k)) := Submodule.mem_top
    rw [← htop, Submodule.mem_bot] at h1
    have := congrFun h1 j
    simp at this
  obtain ⟨x0, hx0, j0, hx0j⟩ := hex
  have hne : (s ×ˢ (Finset.univ : Finset n)).Nonempty := ⟨(x0, j0), by simp [hx0]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (s ×ˢ (Finset.univ : Finset n))
    (fun q : (n → k) × n => valuation k (q.1 q.2)) hne
  have hc : p.1 p.2 ≠ 0 := by
    intro h0
    have := hmax (x0, j0) (by simp [hx0])
    simp only [h0, map_zero] at this
    have h' : valuation k (x0 j0) = 0 := le_antisymm this zero_le'
    exact hx0j ((Valuation.zero_iff _).mp h')
  refine ⟨p.1 p.2, hc, ?_, p.1, ?_, p.2, rfl⟩
  · intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro j
      show valuation k ((p.1 p.2)⁻¹ * y j) ≤ 1
      have hle := hmax (y, j) (by simpa using hy)
      simp only at hle
      have hvc : valuation k (p.1 p.2) ≠ 0 := by simpa using hc
      rw [map_mul, map_inv₀]
      calc (valuation k (p.1 p.2))⁻¹ * valuation k (y j)
          ≤ (valuation k (p.1 p.2))⁻¹ * valuation k (p.1 p.2) := by gcongr
        _ = 1 := inv_mul_cancel₀ hvc
    | zero => intro j; simp
    | add y z _ _ hy hz =>
      intro j
      simpa [mul_add] using add_mem (hy j) (hz j)
    | smul a y _ hy =>
      intro j
      have := mul_mem a.2 (hy j)
      convert this using 1
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
  · rw [← hs]
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_product.mp hp).1)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

theorem sum_fin_two_mul_add_one {M : Type*} [AddCommMonoid M] {ρ n : ℕ} (hn : n = 2 * ρ + 1) (f : Fin n → M)
    (a b : Fin ρ → M) (m : M) (ha : ∀ (i : Fin ρ) (j : Fin n), j.1 = i.1 → f j = a i) (hm : ∀ j : Fin n, j.1 = ρ → f j = m)
    (hb : ∀ (i : Fin ρ) (j : Fin n), j.1 + i.1 = 2 * ρ → f j = b i) :
    ∑ j, f j = ∑ i, a i + m + ∑ i, b i := by
  subst hn
  have e : ρ + (1 + ρ) = 2 * ρ + 1 := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one, add_assoc]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => ha i _ (by simp)
  · congr 1
    · exact hm _ (by simp)
    · rw [← Equiv.sum_comp Fin.revPerm b]
      refine Finset.sum_congr rfl fun i _ => hb _ _ ?_
      simp [Fin.val_rev]
      omega

theorem mul_div_mem_integer_iff {k : Type} [Field k] [ValuativeRel k] {c : k} (hc : valuation k c = 1) (w z : k) :
    w * (z / c) ∈ 𝒪[k] ↔ w * z ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul, map_mul, map_div₀, hc, div_one]

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem mul_mul_div_cancel_left' {k : Type} [Field k] {c : k} (hc : c ≠ 0) (P X : k) : c * P * (X / c) = P * X := by
  field_simp

end GlobalTheory.Core.Mi.LatMatch

end
end
