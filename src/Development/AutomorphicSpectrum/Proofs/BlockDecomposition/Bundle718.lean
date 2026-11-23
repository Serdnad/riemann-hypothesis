module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle675
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle329
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle716
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle655
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle375
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle365
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle661
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle672
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle715
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle697
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle564
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle612
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle435
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCosetsParamRational
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle714
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Mathlib.Topology.Compactness.Paracompact

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegExists

theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem exists_isLSeg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  intro k _ _ _ _ hA Δ
  have hd : ∑ a, (Δ.term a).1 = Δ.deg := Δ.sum_term_fst
  obtain ⟨hd', ⟨φ⟩⟩ := GlobalTheory.T.contragredient_segment_product_equiv hA Δ hd
  obtain ⟨τ', hτ'⟩ := GlobalTheory.T.exists_socle_segment_product hA (segDual Δ) hd'
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr Δ.term hd)
    (isSmooth_prodIrr _ _) (hasFiniteLength_prodIrr hA _ _) τ' (hτ'.of_equiv (.refl _) φ.symm)
  exact ⟨τ, hd, hτ⟩

end GlobalTheory.CompanionTheory.SegExists

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LangSumSub

theorem isL_of_exhaust {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hEx : ∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) {N : ℕ} (τ : IrrRep (GL (Fin N) k)) :
    ∃ 𝔭 : Multiset (Segment k), IsL 𝔭 τ.ρ := by
  obtain ⟨𝔭, h𝔭⟩ := hEx (IrrGL.of τ.ρ τ.smooth τ.irr)
  exact ⟨𝔭, h𝔭.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irr).symm⟩



theorem isSubquotient_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k)
    (hSeg : LSegJacquet k) (hFree : LOrderFree k) (hEx : ∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep)
    (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1)
    (h0 : IsL 𝔪 (x 0).rep) (h1 : IsL 𝔫 (x 1).rep) (hy : IsL (𝔪 + 𝔫) y.rep) : IsSubquotient y.rep (prodIrr x hd) := by
  obtain ⟨n, c⟩ := y
  obtain rfl : (x 0).1 + (x 1).1 = n := (Fin.sum_univ_two _).symm.trans hd
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr_rep x hd
  have hPs : IsSmooth (prodIrr x hd) := isSmooth_prodIrr x hd
  have hPf := GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  obtain ⟨h₁, h₂, h, Δ₁, Δ₂, Δ, hΔ₁, hΔ₂, hΔ, hI⟩ := GlobalTheory.T.ordered_forms_interleave_sum hA 𝔪 𝔫
  have w0 : Wd (x 0).rep (wtW Δ₁) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔪 (x 0).rep h0 h₁ Δ₁ hΔ₁
  have w1 : Wd (x 1).rep (wtW Δ₂) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔫 (x 1).rep h1 h₂ Δ₂ hΔ₂
  have wp : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Δ) :=
    GlobalTheory.T.word_occurs_product_interleave hA (x 0) (x 1) _ _ _ (GlobalTheory.T.ordered_word_letters_cuspidal Δ₁) (GlobalTheory.T.ordered_word_letters_cuspidal Δ₂) w0 w1 hI
  have wP : Wd (prodIrr x hd) (wtW Δ) := GlobalTheory.T.word_occurs_of_subquotient (prodIrr x hd) (prod₂ (x 0).rep (x 1).rep) hPs
    (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) _ wp
  have hτ := GlobalTheory.T.word_occurs_irreducible_subquotient hA (prodIrr x hd) hPs hPf (wtW Δ) wP
  obtain ⟨τ, hτP, hτW⟩ := hτ
  obtain ⟨𝔭, hτL⟩ := isL_of_exhaust hEx τ
  obtain ⟨h', z, hz, ⟨Γ, hΓ, hzL⟩, hcos⟩ := id hτL
  have s1 : InShW 𝔭 (wtW Δ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z hz Γ hzL (wtW Δ) (GlobalTheory.T.ordered_word_letters_cuspidal Δ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z hz) hcos.isSubquotient _ hτW)
    rwa [hΓ.1] at this
  have wΓ : Wd τ.ρ (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔭 τ.ρ hτL h' Γ hΓ
  have wΓP : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ hPs hτP _ wΓ
  have wΓ2 : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prod₂ _ _)
    (.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective) _ wΓP
  obtain ⟨h'', z', Δ', hz', hz'L, hmap, hsub⟩ := GlobalTheory.T.product_langlands_subquotient_segments hA 𝔪 𝔫 (x 0) (x 1) h0 h1
  have s2 : InShW (𝔪 + 𝔫) (wtW Γ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z' hz' Δ' hz'L (wtW Γ) (GlobalTheory.T.ordered_word_letters_cuspidal Γ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z' hz') hsub _ wΓ2)
    rwa [hmap] at this
  have he : 𝔪 + 𝔫 = 𝔭 := GlobalTheory.T.ordered_forms_mutual_shuffle_eq hA (𝔪 + 𝔫) 𝔭 h h' Δ Γ hΔ hΓ s1 s2
  obtain ⟨ψ⟩ := GlobalTheory.T.langlands_classification_order_free_equiv hFree (𝔪 + 𝔫) τ.ρ (IrrGL.rep ⟨_, c⟩) (he ▸ hτL) hy
  exact (IsSubquotient.of_surjective ψ.toIntertwiningMap ψ.toLinearEquiv.surjective).trans hτP

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k →
    (∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) →
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) :=
  fun hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy =>
    isSubquotient_prodIrr hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy

end GlobalTheory.CompanionTheory.LangSumSub

end
end

section

open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)


theorem _root_.GlobalTheory.T.siegel_eisenstein_convergent : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  first | exact @GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | exact GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | (intros; apply GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_ring {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : AddChar A ℂ) (hψc : Continuous ψ) (hψn : ∀ x, ‖ψ x‖ = 1) (κ : Type) [Fintype κ]
    [FirstCountableTopology (κ → A)] [MeasurableSpace (κ → A)] [OpensMeasurableSpace (κ → A)]
    (μ : Measure (κ → A)) [μ.IsOpenPosMeasure]
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (φ : Y → ℂ) (g : Y → κ → A)
    (hg : Measurable g) (N : Set (κ → A)) (hN : IsOpen N)
    (hb : Integrable φ ν → Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ →
      ∀ N' : Set (κ → A), IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : (κ → A) → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0)
    (z₀ : κ → A) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → A) × (κ → A) => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    fun_prop
  have hd1 : ∀ w, Continuous fun v : κ → A => ψ (-(v ⬝ᵥ w)) := fun w =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_id continuous_const)).neg
  have hd2 : ∀ v, Continuous fun w : κ → A => ψ (-(v ⬝ᵥ w)) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id)).neg
  have hd3 : ∀ v, Continuous fun w : κ → A => ψ (v ⬝ᵥ w) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id))
  by_cases hφ : Integrable φ ν
  swap
  · have h0 : ∀ v : κ → A, ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν = 0 := fun v =>
      integral_undef fun hi => hφ (integrable_of_mul_unimodular ν φ (fun y => ψ (v ⬝ᵥ g y)) hi
        ((hd3 v).measurable.comp hg).aestronglyMeasurable fun y => hψn _)
    refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
    show (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) = 0
    rw [h0 v, zero_mul]
  by_cases hJ : Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ
  swap
  · exact integral_undef fun hi => hJ (integrable_of_mul_unimodular μ _ (fun v => ψ (-(v ⬝ᵥ z₀))) hi
      (hd1 z₀).aestronglyMeasurable fun y => hψn _)
  exact vanish_abs μ (fun v z => ψ (-(v ⬝ᵥ z))) hd1 hd2 (fun _ _ => hψn _) _ hJ N hN (hb hφ hJ) z₀ hz

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_generic (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F)
    (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)]
    [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) (hμ : GlobalTheory.SWLit.IsTamagawa F κ μ)
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F)
    (hg : Measurable g) (N : Set (κ → AF F)) (hN : IsOpen N) (hgN : ∀ y, g y ∉ N)
    (z₀ : κ → AF F) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ.1
  refine vanish_ring ψ hψ.1 hψ.2.1 κ μ Y ν φ g hg N hN ?_ z₀ hz
  intro hφ hJ N' hN' hsub z₁ hz₁
  obtain ⟨Φ, hΦ, hΦ0, hΦN, hΦ1⟩ := GlobalTheory.T.exists_nonnegative_schwartz_bump F κ N' hN' z₁ hz₁
  obtain ⟨hΦc, -, hΦi⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  exact ⟨Φ, hΦc, hΦi μ hμ.1, hΦ0, hΦN, hΦ1,
    GlobalTheory.T.tamagawa_fourier_integrable F hF ψ hψ κ μ hμ Y ν φ g hφ hg hJ Φ hΦ (fun y => hΦN _ fun h' => hgN y (hsub h'))⟩

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

variable {D : D7}

theorem posOn_add_smul_one {n : ℕ} {ε δ : ℝ} {Z : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)}
    (hS : NonnegOn ε Z S) (hε : ε = 1 ∨ ε = -1) (hδ : 0 < δ) :
    PosOn ε (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) S := by
  intro w hw hne
  have h0 := hS w hw
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hB : 0 < (star w ⬝ᵥ w).re := by
    have e : (star w ⬝ᵥ w).re = ∑ j, Complex.normSq (w j) := by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    rw [e]
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e2 : (star w ⬝ᵥ (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).mulVec w).re =
      (star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  rw [e2]
  have : ε * ((star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re) =
      ε * (star w ⬝ᵥ Z.mulVec w).re + (ε * ε) * δ * (star w ⬝ᵥ w).re := by ring
  rw [this, hεε, one_mul]
  exact add_pos_of_nonneg_of_pos h0 (mul_pos hδ hB)

theorem compAt_add' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a b : Mx D m n) :
    compAt θ ρ (a + b) = compAt θ ρ a + compAt θ ρ b := by
  exact Matrix.map_add (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_add a b

theorem compAt_neg' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a : Mx D m n) :
    compAt θ ρ (-a) = -compAt θ ρ a := by
  exact Matrix.map_neg (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_neg a

theorem W_eq_zero_of_obstruction (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (h : Hyp D r V ψ θ μ lam ν φ) (β : HermE D r) (ρ : D.what₂.Tau) (ε : ℝ)
    (S : Submodule ℂ (Fin r → ℂ)) (hε : ε = 1 ∨ ε = -1) (hS : NonnegOn ε (β.1.map (tauE D ρ)) S)
    (hT : ∀ T : Submodule ℂ (Fin V.rank → ℂ), PosOn ε (gramAt D V ρ) T →
      Module.finrank ℂ T < Module.finrank ℂ S) :
    W ψ V μ lam φ β = 0 := by
  obtain ⟨hr, hψ, hθ, ⟨𝓕, hF⟩, ⟨𝓖, hG⟩, -, -, -⟩ := h
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele D.host.F
  haveI : BorelSpace (AF D.host.F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D V.rank r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hF.1
  obtain ⟨n, c, u, R, hu, hR, hRu, hcu, hTam⟩ := GlobalTheory.T.hermitian_coordinates_trace_pairing D r lam 𝓖 hG
  have hin := GlobalTheory.T.gram_map_continuous_hermitian D θ hθ V r ρ
  let g : Mx D V.rank r → Fin n → AF D.host.F := fun y => u (inner V y y)
  have hgc : Continuous g := hu.comp hin.1
  let N : Set (Fin n → AF D.host.F) := {w | PosOn ε (compAt θ ρ (R w)) S}
  have hN : IsOpen N :=
    (GlobalTheory.T.positive_on_subspace_open r ε S).preimage ((GlobalTheory.RealWeil.continuous_compAt hθ ρ r r).comp hR)
  have hgN : ∀ y, g y ∉ N := by
    intro y hy
    have h1 : PosOn ε (compAt θ ρ (R (u (inner V y y)))) S := hy
    rw [hRu _ (hin.2 y).1, (hin.2 y).2] at h1
    obtain ⟨T, hT1, hT2⟩ := GlobalTheory.T.positivity_pulls_back_to_subspace _ _ _ _ ε S h1
    have := hT T hT1
    omega
  let z₀ : Fin n → AF D.host.F := u (rat β.1)
  have hcl : ∀ e' : ℕ → Mx D r r, (∀ k, e' k ∈ hermA D r) → Filter.Tendsto e' Filter.atTop (nhds 0) →
      (∀ k : ℕ, compAt θ ρ (e' k) = ((ε * ((1 : ℝ) / ((k : ℝ) + 1)) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) →
      z₀ ∈ closure N := by
    intro e' he' het hec
    have hlim : Filter.Tendsto (fun k => u (rat β.1 + e' k)) Filter.atTop (nhds z₀) := by
      have h2 : Filter.Tendsto (fun k => rat β.1 + e' k) Filter.atTop (nhds (rat β.1 + 0)) :=
        tendsto_const_nhds.add het
      rw [add_zero] at h2
      exact (hu.tendsto _).comp h2
    refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
    show PosOn ε (compAt θ ρ (R (u (rat β.1 + e' k)))) S
    have hrat : compAt θ ρ (rat β.1) = β.1.map (tauE D ρ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ ρ β.1
    rw [hRu _ ((hermA D r).add_mem (GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA β) (he' k)), compAt_add', hec k, hrat]
    exact posOn_add_smul_one hS hε (by positivity)
  obtain ⟨e, he, het, hec⟩ := GlobalTheory.T.hermitian_scalar_sequence_tends_zero D θ hθ r
  have hz : z₀ ∈ closure N := by
    rcases hε with rfl | rfl
    · refine hcl e he het fun k => ?_
      rw [hec k, one_mul]
    · refine hcl (fun k => -e k) (fun k => (hermA D r).neg_mem (he k)) ?_ fun k => ?_
      · have h3 := het.neg
        rw [neg_zero] at h3
        exact h3
      · rw [compAt_neg', hec k]
        simp
  have key := vanish_generic D.host.F D.sp.cm.totReal ψ hψ (Fin n) (lam.map c.symm) hTam _ μ φ g
    hgc.measurable N hN hgN z₀ hz
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  have hemb : MeasurableEmbedding (c.symm) := c.symm.toHomeomorph.measurableEmbedding
  rw [hemb.integral_map] at key
  refine Eq.trans ?_ key
  unfold W
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have h1 : ∀ x : Mx D r r, c.symm b ⬝ᵥ u x = halfTr (Matrix.trace (HMul.hMul b.1 x : Mx D r r)) := fun x => by
    rw [← hcu]; simp
  show Jt ψ V μ φ b * _ = (∫ y, φ y * ψ (c.symm b ⬝ᵥ u (inner V y y)) ∂μ) * ψ (-(c.symm b ⬝ᵥ u (rat β.1)))
  simp only [h1]
  rw [Matrix.trace_mul_comm]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem noFrame : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  intro D r V ψ θ μ lam ν φ h t β hβ hno
  obtain ⟨ρ, ε, S, hε, hS, hT⟩ := GlobalTheory.T.nonrepresented_signature_obstruction D r V h.1 t β hβ hno
  rw [W_eq_zero_of_obstruction r V ψ θ μ lam ν φ h β ρ ε S hε hS hT]
  haveI hemp : IsEmpty {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} :=
    ⟨fun x => hno ⟨x.1, x.2⟩⟩
  unfold IfrB
  have h0 : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) q) = fun _ => (0 : ℂ) := by
    funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, tsum_empty]
  rw [h0]
  simp [MeasureTheory.average]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis


theorem _root_.GlobalTheory.T.heisenberg_cosets_param_rational : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn),
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧
      (∀ q, zKer hn (ratOf q.out) = ⊥ ↔ q ∈ Set.range e) ∧
      (∀ (l l' : ratHerm D ρ) u (h : M.nzx l'.1 0 ∈ GF D n),
        rmulEquiv (P D n) (GF D n) ⟨M.nzx l'.1 0, h⟩ (e (l, u)) = e (l' + l, u)) ∧
      ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D ρ) u (y : G D n),
        term (P D n) (GF D n) f y (e (l, u)) =
          f (M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * y) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell | exact GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell | (intros; apply GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell <;> assumption)
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coefficient_heisenberg_equivariance : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (η : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p) (h : G D n), Wz M m ψ b₀ f (M.sh η * (M.nzx z x * h)) = chz ψ b₀ z * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x η * Wz M m ψ b₀ f (M.sh η * h) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx | exact GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx | (intros; apply GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem block_unipotent_map {A B : Type} {m : ℕ} [Zero A] [One A] [Zero B] [One B] [DecidableEq (Fin m)] (f : A → B) (f0 : f 0 = 0)
    (f1 : f 1 = 1) (x : Matrix (Fin m) (Fin m) A) :
    (blk4 (1 : Matrix (Fin m) (Fin m) A) x 0 1).map f = blk4 1 (x.map f) 0 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite f, f0, f1]

theorem splitHom_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      blk4 1 (tauC τ x.1) 0 1 := by
  have e1 := GlobalTheory.LocIntw.matR_mapH (evFin D.host.F v) (nb x)
  rw [GlobalTheory.LocIntw.matR_adele, h x] at e1
  have e2 : (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
        (proj D.sp.cm.sig (Jst D n) v (nb x))).map (splitProj τ) := rfl
  have e3 : (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
      (proj D.sp.cm.sig (Jst D n) v (nb x))) = (blk4 1 x.1 0 1).map (cv D v) := e1
  rw [e2, e3, block_unipotent_map _ (map_zero _) (map_one _), block_unipotent_map _ (map_zero _) (map_one _)]
  rfl

theorem thU_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = nU (tauC τ x.1) := by
  have e := splitHom_proj_nMap D n nb h v τ x
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e' : (thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 i j =
      (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1
        (finSumFinEquiv i) (finSumFinEquiv j) := rfl
  rw [e', e]
  change (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _)
    (finSumFinEquiv.symm (finSumFinEquiv i)) (finSumFinEquiv.symm (finSumFinEquiv j)) =
      (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _) i j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.Jp

end
end
