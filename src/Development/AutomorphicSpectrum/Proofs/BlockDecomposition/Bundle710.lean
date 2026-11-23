module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.Adele.Topology
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeExtendByScalarBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle705
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreserved
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle707
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle706
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Compactness.Paracompact
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem pair_abs {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) [SFinite μ]
    (ν : Measure Y) [SFinite ν] (k : X → Y → ℂ) (e : X → X → ℂ)
    (hk : Measurable (Function.uncurry k)) (he : Measurable (Function.uncurry e))
    (hkn : ∀ v y, ‖k v y‖ = 1) (hen : ∀ v z, ‖e v z‖ = 1)
    (φ : Y → ℂ) (hφ : Integrable φ ν) (hJ : Integrable (fun v => ∫ y, φ y * k v y ∂ν) μ)
    (Φ : X → ℂ) (hΦ : Integrable Φ μ) (H : X → ℂ) (hHi : Integrable H μ)
    (hH : ∀ v, H v = ∫ z, Φ z * e v z ∂μ) (hinv : ∀ y, ∫ v, H v * k v y ∂μ = 0) :
    ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ = 0 := by
  have h1 : Integrable (Function.uncurry fun (z v : X) =>
      (∫ y, φ y * k v y ∂ν) * e v z * Φ z) (μ.prod μ) := by
    refine Integrable.mono (hΦ.mul_prod hJ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × X => ∫ y, φ y * k p.2 y ∂ν) (μ.prod μ) :=
        hJ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × X => e p.2 p.1) (μ.prod μ) :=
        (he.comp measurable_swap).aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × X => Φ p.1) (μ.prod μ) :=
        hΦ.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨z, v⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hen, mul_one]
      exact le_of_eq (mul_comm _ _)
  have h2 : Integrable (Function.uncurry fun (v : X) (y : Y) => φ y * k v y * H v) (μ.prod ν) := by
    refine Integrable.mono (hHi.mul_prod hφ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × Y => φ p.2) (μ.prod ν) :=
        hφ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × Y => k p.1 p.2) (μ.prod ν) :=
        hk.aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × Y => H p.1) (μ.prod ν) :=
        hHi.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨v, y⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hkn, mul_one]
      exact le_of_eq (mul_comm _ _)
  calc ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ
      = ∫ z, ∫ v, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := by
        congr 1; funext z
        exact (integral_mul_const (Φ z) _).symm
    _ = ∫ v, ∫ z, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := integral_integral_swap h1
    _ = ∫ v, (∫ y, φ y * k v y ∂ν) * H v ∂μ := by
        congr 1; funext v
        rw [hH v, ← integral_const_mul]
        congr 1; funext z; ring
    _ = ∫ v, ∫ y, φ y * k v y * H v ∂ν ∂μ := by
        congr 1; funext v
        exact (integral_mul_const (H v) _).symm
    _ = ∫ y, ∫ v, φ y * k v y * H v ∂μ ∂ν := integral_integral_swap h2
    _ = ∫ y, φ y * ∫ v, H v * k v y ∂μ ∂ν := by
        congr 1; funext y
        rw [← integral_const_mul]
        congr 1; funext v; ring
    _ = 0 := by simp [hinv]

theorem haar_facts {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] :
    SFinite μ ∧ μ.IsNegInvariant :=
  ⟨inferInstance, inferInstance⟩

theorem pair_ring {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (μ : Measure (κ → R)) [SFinite μ]
    [μ.IsNegInvariant] (ψ : AddChar R ℂ) (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → R)
    (hφ : Integrable φ ν) (hg : Measurable g)
    (hJ : Integrable (fun v : κ → R => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ)
    (Φ : (κ → R) → ℂ) (hΦi : Integrable Φ μ)
    (hHi : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ)
    (hinv : ∀ x, ∫ y, (∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ x) ∂μ = Φ (-x))
    (h0 : ∀ y, Φ (g y) = 0) :
    ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → R) × (κ → R) => p.1 ⬝ᵥ p.2) :=
    continuous_fst.dotProduct continuous_snd
  have hk : Measurable (Function.uncurry fun (v : κ → R) (y : Y) => ψ (v ⬝ᵥ g y)) := by
    have hm : Measurable (fun p : (κ → R) × (κ → R) => ψ (p.1 ⬝ᵥ p.2)) :=
      (hc.comp hdot).measurable
    exact hm.comp (measurable_fst.prodMk (hg.comp measurable_snd))
  have he : Measurable (Function.uncurry fun (v z : κ → R) => ψ (-(v ⬝ᵥ z))) :=
    (hc.comp hdot.neg).measurable
  have hHi' : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (-(w ⬝ᵥ z)) ∂μ) μ := by
    refine hHi.comp_neg.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [dotProduct_neg]
    congr 1; funext z
    rw [dotProduct_comm]
  have hinv' : ∀ y, ∫ v, (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y) ∂μ = 0 := by
    intro y
    have h1 := hinv (-(g y))
    rw [neg_neg, h0 y] at h1
    refine (integral_neg_eq_self
      (fun v => (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y)) μ).symm.trans (Eq.trans ?_ h1)
    congr 1; funext v
    simp only [neg_dotProduct, neg_neg, dotProduct_neg]
    congr 1; congr 1; funext z
    rw [dotProduct_comm]
  exact pair_abs μ ν (fun v y => ψ (v ⬝ᵥ g y)) (fun v z => ψ (-(v ⬝ᵥ z))) hk he
    (fun v y => hn _) (fun v z => hn _) φ hφ hJ Φ hΦi _ hHi' (fun v => rfl) hinv'

theorem pair_vanish : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), GlobalTheory.SWLit.IsTamagawa F κ μ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F), Integrable φ ν → Measurable g → Integrable (fun v : κ → AF F => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ y, Φ (g y) = 0) → ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  intro F _ _ hF ψ hψ κ _ _ _ μ hμ Y _ ν _ φ g hφ hg hJ Φ hΦ h0
  have hH : μ.IsAddHaarMeasure := hμ.1
  obtain ⟨hS, hN⟩ := haar_facts μ
  have hc : Continuous ψ := hψ.1
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  obtain ⟨-, -, hint⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  have hinv := GlobalTheory.TamFourier.fourier_inversion_tamagawa F hF ψ hψ κ μ hμ Φ hΦ
  have hHi : Integrable (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ := by
    by_contra hni
    have hzero : ∀ x, Φ x = 0 := by
      intro x
      have h1 := hinv (-x)
      rw [neg_neg] at h1
      rw [← h1]
      apply integral_undef
      intro hi
      apply hni
      exact integrable_of_mul_unimodular μ (fun y => ∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ)
        (fun y => ψ (y ⬝ᵥ -x)) hi
        ((hc.comp (continuous_id.dotProduct continuous_const)).aestronglyMeasurable) (fun y => hn _)
    apply hni
    have hfun : (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) = fun _ => (0 : ℂ) := by
      funext w; simp [hzero]
    rw [hfun]
    exact integrable_zero _ _ _
  exact pair_ring μ ψ hc hn ν φ g hφ hg hJ Φ (hint μ hH) hHi hinv h0

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HtEx

theorem continuous_of_decomp {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace X]
    {Q : Subgroup Γ} (hQ : IsClosed (Q : Set Γ)) {C : Set Γ} (hC : IsCompact C) (H : Γ → X) (δ : Q → X)
    (hδ : Continuous δ) (hI : ∀ g, ∃ p ∈ Q, ∃ k ∈ C, g = p * k)
    (hH : ∀ (p : Q), ∀ k ∈ C, H ((p : Γ) * k) = δ p) : Continuous H := by
  rw [continuous_iff_isClosed]
  intro F hF
  have hQF : IsClosed ((Subtype.val : Q → Γ) '' (δ ⁻¹' F)) :=
    hQ.isClosedMap_subtype_val _ (hF.preimage hδ)
  have heq : H ⁻¹' F = Set.image2 (· * ·) ((Subtype.val : Q → Γ) '' (δ ⁻¹' F)) C := by
    ext g
    constructor
    · intro hg
      obtain ⟨p, hp, k, hk, rfl⟩ := hI g
      refine Set.mem_image2.mpr ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩
      have h1 := hH ⟨p, hp⟩ k hk
      simp only [Set.mem_preimage] at hg ⊢
      rw [← h1]
      exact hg
    · intro hg
      obtain ⟨x, ⟨q, hq, rfl⟩, k, hk, rfl⟩ := Set.mem_image2.mp hg
      simp only [Set.mem_preimage] at hq ⊢
      rw [hH q k hk]
      exact hq
  rw [heq]
  exact hQF.mul_right_of_isCompact hC

variable {D : D7} {n : ℕ}

def delta : P D n →* ℝ≥0 :=
  (absA D).comp (Matrix.GeneralLinearGroup.det.comp HeightExists.leviBlock)

theorem continuous_delta : Continuous (delta (D := D) (n := n)) := by
  have hA : Continuous (absA D) := GlobalTheory.Doubling.continuous_absE
  exact hA.comp (HeightExists.continuous_detGL.comp HeightExists.continuous_leviBlock)

theorem absA_pos (u : (AE D)ˣ) : 0 < absA D u := by
  have h : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h)

theorem delta_eq {p : G D n} (hp : p ∈ P D n) {a : GL (Fin n) (AE D)} (ha : blkA (mat p) = a.1) :
    delta (⟨p, hp⟩ : P D n) = absA D (Matrix.GeneralLinearGroup.det a) := by
  have hl : HeightExists.leviBlock (D := D) (n := n) (⟨p, hp⟩ : P D n) = a := by
    ext1
    exact ha
  show absA D (Matrix.GeneralLinearGroup.det (HeightExists.leviBlock (D := D) (n := n) (⟨p, hp⟩ : P D n))) = _
  rw [hl]

theorem height_eq {H : G D n → ℝ≥0} (hH : IsHeight H) (p : P D n) {k : G D n} (hk : k ∈ K D n) :
    H ((p : G D n) * k) = delta p := by
  obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA p.2
  rw [hH p p.2 a ha k hk, ← delta_eq p.2 ha]

theorem isHt_of_isHeight {H : G D n → ℝ≥0} (hH : IsHeight H) : PositivityTheory.Rg.Rsw.IsHt H := by
  refine ⟨continuous_of_decomp HeightExists.isClosed_P HeightExists.isCompact_K H delta continuous_delta
    (Iwasawa.exists_mul D n) (fun p k hk => height_eq hH p hk), ?_, ?_⟩
  · intro g
    obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    rw [height_eq hH ⟨p, hp⟩ hk]
    obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp
    rw [delta_eq hp ha]
    exact absA_pos _
  · intro q hq a ha g
    obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    rw [← mul_assoc, height_eq hH ⟨q * p, (P D n).mul_mem hq hp⟩ hk, height_eq hH ⟨p, hp⟩ hk,
      ← delta_eq hq ha]
    exact map_mul delta (⟨q, hq⟩ : P D n) ⟨p, hp⟩

theorem htExist : PositivityTheory.Rg.Rsw.HtExist := by
  intro D n
  refine ⟨?_, (K D n : Set (G D n)), HeightExists.isCompact_K, fun g => ?_⟩
  · obtain ⟨H, hH⟩ := exists_height D n
    exact ⟨H, isHt_of_isHeight hH⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    exact ⟨p, hp, k, hk, rfl⟩

end GlobalTheory.CompanionTheory.HtEx

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.siegelWeilFree_extend_by_scalar_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, 2 * n + 1 < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), (framesE σ J T).Nonempty → SWFree σ J T hT → SWFree σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso.aniso_step | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso.aniso_step | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso.aniso_step <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc

theorem _root_.GlobalTheory.T.continuous_partial_fourier_mean : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (Φ : hermA D n → ℂ), Continuous Φ → IsPer Φ → Continuous (pm hn m ψ b₀ Φ) := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.continuous_pm | exact GlobalTheory.CompanionTheory.PcFc.continuous_pm | (intros; apply GlobalTheory.CompanionTheory.PcFc.continuous_pm <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc

theorem _root_.GlobalTheory.T.partial_coefficient_unipotent_mean : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (F : G D n → ℂ) {nb : hermA D n → G D n}, IsNMap nb → ∀ (g : G D n) (y : hermA D p), pc M m ψ b₀ F (nb (bT hn 0 0 y) * g) = pm hn m ψ b₀ (fun b => F (nb b * g)) y := by
  first | exact @GlobalTheory.CompanionTheory.PcNb.pc_nb | exact GlobalTheory.CompanionTheory.PcNb.pc_nb | (intros; apply GlobalTheory.CompanionTheory.PcNb.pc_nb <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_points_heisenberg_group : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn), (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧ (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.nzx 0 (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧ ∀ z ∈ ratHerm D ρ, M.nzx z 0 ∈ GF D n := by
  first | exact @GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF | exact GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF | (intros; apply GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_translation_preserved : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (γ : G D p), γ ∈ GF D p → ∃ T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p), (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧ (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧ ∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Transport.transport | exact GlobalTheory.CompanionTheory.FJE.Transport.transport | (intros; apply GlobalTheory.CompanionTheory.FJE.Transport.transport <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.LeftInvSect
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem iwaCpt : IwaCpt := by
  intro D n C hC
  have hCK : IsCompact (C * (K D n : Set (G D n))⁻¹) := hC.mul isCompact_K.inv
  have hQ : IsCompact ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) :=
    (isClosed_P (D := D) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hCK
  have hL := hQ.image (continuous_leviBlock (D := D) (n := n))
  set L := leviBlock (D := D) (n := n) '' ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) with hLdef
  have hR : Continuous fun a : GL (Fin n) (AE D) => (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_absE.comp continuous_detGL)
  obtain ⟨R, hRb⟩ := (hL.image hR).bddAbove
  refine ⟨Units.val '' L, (fun a : GL (Fin n) (AE D) => (a⁻¹).1) '' L, R, hL.image Units.continuous_val,
    hL.image Units.continuous_coe_inv, fun h hh => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := Iwasawa.exists_mul D n h
  have hmem : leviBlock (D := D) (n := n) ⟨q, hq⟩ ∈ L :=
    ⟨⟨q, hq⟩, ⟨q * k, hh, k⁻¹, Set.inv_mem_inv.2 hk, by simp⟩, rfl⟩
  obtain ⟨m, t, b, e, hm, ht⟩ := exists_levi_unip hq (leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  exact ⟨m, t, k, _, b, hk, by rw [e], hm, ht, ⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩, hRb ⟨_, hmem, rfl⟩⟩

end GlobalTheory.CompanionTheory.ThTot

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.induced_section_local_integrability : IkLint := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.ikLint | exact GlobalTheory.CompanionTheory.ColumnSplitting.ikLint | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.ikLint <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

theorem _root_.GlobalTheory.T.reducible_cuspidal_pair_nongeneric_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp →
      ¬ (prodIrr ![x, y] hd).IsIrreducible →
      ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ (prodIrr ![x, y] hd) ∧ ¬ IsGenericFor ψ τ.ρ := by
  first | exact @GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | exact GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | (intros; apply GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_vanishing : PositivityTheory.GramSchwartzFunctions.EC.Zero := by
  first | exact @GlobalTheory.CompanionTheory.EisZero.zero | exact GlobalTheory.CompanionTheory.EisZero.zero | (intros; apply GlobalTheory.CompanionTheory.EisZero.zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.epi_of_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.epiOfFF | exact GlobalTheory.CompanionTheory.Dblock.epiOfFF | (intros; apply GlobalTheory.CompanionTheory.Dblock.epiOfFF <;> assumption)
end
