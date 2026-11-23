module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle590
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderVolumeAlmostAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BadProjectionLocusNull
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle588
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle517
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle560
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle547
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle482
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeUnramified
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.norm_mem_norm_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r) (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k → Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  first | exact @GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | exact GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | (intros; apply GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.local_volume_rank_one_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e → ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.local_order_volume_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), IsHermND σ J → 3 ≤ N → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (c : O), ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) → ∀ B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), MeasurableSet B → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * X a i) '' B) ≤ ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) B := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

theorem _root_.GlobalTheory.T.bad_projection_locus_null : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ),
    GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D → ∀ Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D,
      IsGoodProj (ptIdeal (i (genericPoint X))) Ψ → ∀ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D,
        volume (c.e.target ∩ c.e.symm ⁻¹' {y | (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 = 0) ∨
          ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.Crit.volume_chart_crit | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.Crit.volume_chart_crit | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.Crit.volume_chart_crit <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem fold_parseval : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ (Φ φ : Mx D ρ p → ℂ) (B₁ B₂ : ℝ), StronglyMeasurable Φ → StronglyMeasurable φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₁) → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₂) → ∫ v in m.𝓕 ×ˢ m.𝓕, GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ v ∂(m.μ.prod m.μ) = ∫ y, Φ y * conj (φ y) ∂m.μ := by
  intro D ρ p m ψ hψ b₀ hb Φ φ B₁ B₂ hΦ hφ h1 h2
  haveI := m.hμ.1
  have hfd : IsAddFundamentalDomain (ratMx D ρ p) m.𝓕 m.μ := m.hμ.2.1
  have hfin : m.μ m.𝓕 = 1 := m.hμ.2.2
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  haveI : Countable (ratMx D ρ p) := by
    unfold GlobalTheory.MixModel.ratMx
    exact (AddMonoidHom.rangeRestrict_surjective _).countable
  haveI : MeasurableConstVAdd (ratMx D ρ p) (Mx D ρ p) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  haveI : SFinite m.μ := by
    have hs := hfd.sum_restrict
    open scoped Pointwise in
    haveI : ∀ g : ratMx D ρ p, IsFiniteMeasure (m.μ.restrict (g +ᵥ m.𝓕)) := fun g =>
      ⟨by rw [Measure.restrict_apply_univ, measure_vadd, hfin]; exact ENNReal.one_lt_top⟩
    rw [← hs]
    infer_instance
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hfin]; exact ENNReal.one_lt_top⟩
  have hds : ∀ (Ψ : Mx D ρ p → ℂ) (B : ℝ),
      (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Ψ (rt ξ + y)‖) ∧
        ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Ψ (rt ξ + y)‖ ≤ B) →
      ∀ x y, ‖dsum ψ b₀ Ψ x y‖ ≤ B := by
    intro Ψ B hB x y
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · simpa [norm_mul, chv_norm ψ hψ] using (hB y).1
    · simpa [norm_mul, chv_norm ψ hψ] using (hB y).2
  have hB₁ : 0 ≤ B₁ := (tsum_nonneg (fun _ => norm_nonneg _)).trans (h1 0).2
  have hB₂ : 0 ≤ B₂ := (tsum_nonneg (fun _ => norm_nonneg _)).trans (h2 0).2
  have hm : StronglyMeasurable (Ap ψ b₀ Φ φ) :=
    (dsum_stronglyMeasurable ψ hψ b₀ Φ hΦ (fun y => (h1 y).1)).mul
      (Complex.continuous_conj.comp_stronglyMeasurable
        (dsum_stronglyMeasurable ψ hψ b₀ φ hφ (fun y => (h2 y).1)))
  have hint : Integrable (Ap ψ b₀ Φ φ) ((m.μ.restrict m.𝓕).prod (m.μ.restrict m.𝓕)) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (B₁ * B₂) (ae_of_all _ (fun v => ?_))
    rw [Ap, norm_mul, Complex.norm_conj]
    exact mul_le_mul (hds Φ B₁ h1 _ _) (hds φ B₂ h2 _ _) (norm_nonneg _) hB₁
  have hP : StronglyMeasurable (fun y => Φ y * conj (φ y)) :=
    hΦ.mul (Complex.continuous_conj.comp_stronglyMeasurable hφ)
  have hsum : ∀ y, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y) * conj (φ (rt ξ + y))‖ₑ
      ≤ ENNReal.ofReal (B₁ * B₂) := by
    intro y
    calc ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y) * conj (φ (rt ξ + y))‖ₑ
        ≤ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E,
            ‖Φ (rt ξ + y)‖ₑ * ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (rt η + y)‖ₑ := by
          refine ENNReal.tsum_le_tsum (fun ξ => ?_)
          rw [enorm_mul, ← ofReal_norm (conj _), Complex.norm_conj, ofReal_norm]
          gcongr
          exact ENNReal.le_tsum (f := fun η => ‖φ (rt η + y)‖ₑ) ξ
      _ = (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y)‖ₑ) *
            ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (rt η + y)‖ₑ := ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal B₁ * ENNReal.ofReal B₂ := by
          gcongr
          · simp only [← ofReal_norm]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (h1 y).1]
            exact ENNReal.ofReal_le_ofReal (h1 y).2
          · simp only [← ofReal_norm]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (h2 y).1]
            exact ENNReal.ofReal_le_ofReal (h2 y).2
      _ = ENNReal.ofReal (B₁ * B₂) := (ENNReal.ofReal_mul hB₁).symm
  have hPint : Integrable (fun y => Φ y * conj (φ y)) m.μ := by
    refine ⟨hP.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [hfd.lintegral_eq_tsum'']
    beta_reduce
    rw [← lintegral_tsum (f := fun (g : ratMx D ρ p) (x : Mx D ρ p) => ‖Φ (g +ᵥ x) * conj (φ (g +ᵥ x))‖ₑ)
      (fun g => ((hP.measurable.comp (measurable_const_vadd g)).enorm).aemeasurable)]
    calc ∫⁻ x in m.𝓕, ∑' g : ratMx D ρ p, ‖Φ (g +ᵥ x) * conj (φ (g +ᵥ x))‖ₑ ∂m.μ
        ≤ ∫⁻ _ in m.𝓕, ENNReal.ofReal (B₁ * B₂) ∂m.μ := by
          refine lintegral_mono (fun x => ?_)
          refine (ENNReal.tsum_le_tsum_comp_of_surjective
            (AddMonoidHom.rangeRestrict_surjective
              (Formalism.L2.Theta.incA D).toAddMonoidHom.mapMatrix) _).trans ?_
          exact hsum x
      _ < ⊤ := by
          rw [lintegral_const, Measure.restrict_apply_univ, hfin, mul_one]
          exact ENNReal.ofReal_lt_top
  rw [← Measure.prod_restrict, integral_prod _ hint, integral_fold m _ hPint]
  refine integral_congr_ae (ae_of_all _ (fun y => ?_))
  exact GlobalTheory.T.heisenberg_character_orthogonality m ψ hψ b₀ hb (fun η => Φ (rt η + y)) (fun η => φ (rt η + y)) (h1 y).1 (h2 y).1

end GlobalTheory.CompanionTheory.FJE
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

theorem _root_.GlobalTheory.T.node_function_levi_decomposition : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply | exact GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem blk_val_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul
      ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)
  unfold blk
  simp only
  rw [dite_eq_left hU]
  rfl

theorem isInt_blk_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (blk h w m X).val ↔ IsInt w m.1.val ∧ IsInt w m.2.val ∧ IsInt w (m.1.val * X) := by
  intro E _ _ _ n a b h w m X
  rw [blk_val_eq]
  set e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he
  constructor
  · intro H
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using H (e (Sum.inl i)) (e (Sum.inl j))
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using H (e (Sum.inr i)) (e (Sum.inr j))
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using H (e (Sum.inl i)) (e (Sum.inr j))
  · rintro ⟨h1, h2, h3⟩ i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h1 i j
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h3 i j
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using (Ov E w).zero_mem
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h2 i j

end GlobalTheory.CompanionTheory.CtS
end
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem blk_inv_val {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    ((blk h w m X)⁻¹).val =
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) := by
  have a1 : m.1.val * (m.1⁻¹).val = 1 := Units.mul_inv m.1
  have a2 : (m.1⁻¹).val * m.1.val = 1 := Units.inv_mul m.1
  have b1 : m.2.val * (m.2⁻¹).val = 1 := Units.mul_inv m.2
  have b2 : (m.2⁻¹).val * m.2.val = 1 := Units.inv_mul m.2
  have h1 : fromBlocks m.1.val (m.1.val * X) 0 m.2.val *
      fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [a1]
    · simp [Matrix.mul_assoc]
    · simp
    · simp [b1]
  have h2 : fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val *
      fromBlocks m.1.val (m.1.val * X) 0 m.2.val = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [a2]
    · simp [← Matrix.mul_assoc, a2, Matrix.mul_assoc, b2]
    · simp
    · simp [b2]
  have r1 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) *
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) = 1 := by
    simp only [reindex_apply, submatrix_mul_equiv, h1, submatrix_one_equiv]
  have r2 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) *
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) = 1 := by
    simp only [reindex_apply, submatrix_mul_equiv, h2, submatrix_one_equiv]
  have hU : IsUnit (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := ⟨⟨_, _, r1, r2⟩, rfl⟩
  have hb : (blk h w m X).val = reindex (finSumFinEquiv.trans (finCongr h))
      (finSumFinEquiv.trans (finCongr h)) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
    unfold blk
    simp only []
    rw [dite_eq_left hU]
    rfl
  exact Units.inv_eq_of_mul_eq_one_right (by rw [hb]; exact r1)

theorem isInt_smul_blk_inv_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (ϖ • ((blk h w m X)⁻¹).val) ↔ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val)) := by
  intro E _ _ _ n a b h w ϖ m X
  rw [blk_inv_val h w m X]
  constructor
  · intro H
    have key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w := by
      intro i j
      have := H (finSumFinEquiv.trans (finCongr h) i) (finSumFinEquiv.trans (finCongr h) j)
      simpa [reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using this
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.smul_apply, smul_eq_mul] using key (Sum.inl i) (Sum.inl j)
    · simpa [Matrix.smul_apply, smul_eq_mul] using key (Sum.inr i) (Sum.inr j)
    · have := (Ov E w).neg_mem (key (Sum.inl i) (Sum.inr j))
      simpa [Matrix.smul_apply, smul_eq_mul] using this
  · rintro ⟨H1, H2, H3⟩ i j
    have key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w := by
      rintro (i | i) (j | j)
      · simpa [Matrix.smul_apply, smul_eq_mul] using H1 i j
      · have := (Ov E w).neg_mem (H3 i j)
        simpa [Matrix.smul_apply, smul_eq_mul] using this
      · simpa using (Ov E w).zero_mem
      · simpa [Matrix.smul_apply, smul_eq_mul] using H2 i j
    simpa [reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using
      key ((finSumFinEquiv.trans (finCongr h)).symm i) ((finSumFinEquiv.trans (finCongr h)).symm j)

end GlobalTheory.CompanionTheory.CtS
end
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintInd

theorem finsum_out_indicator {A : Type} [AddCommGroup A] (S Λ : AddSubgroup A) (hSΛ : S ≤ Λ)
    (K : Subgroup (Multiplicative A)) (hK : ∀ X, X ∈ K ↔ Multiplicative.toAdd X ∈ S) :
    ∑ᶠ q : Multiplicative A ⧸ K, (if Multiplicative.toAdd q.out ∈ Λ then (1 : ℂ) else 0) =
      ((S.relIndex Λ : ℕ) : ℂ) := by
  have hrep : ∀ x : Multiplicative A,
      Multiplicative.toAdd ((x : Multiplicative A ⧸ K).out) ∈ Λ ↔ Multiplicative.toAdd x ∈ Λ := by
    intro x
    have h1 : ((x : Multiplicative A ⧸ K).out)⁻¹ * x ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (x : Multiplicative A ⧸ K))
    have h2 : -Multiplicative.toAdd ((x : Multiplicative A ⧸ K).out) + Multiplicative.toAdd x ∈ Λ :=
      hSΛ ((hK _).1 h1)
    constructor
    · intro h
      have := Λ.add_mem h h2
      simpa using this
    · intro h
      have := Λ.add_mem h (Λ.neg_mem h2)
      simpa using this
  let T : Set (Multiplicative A ⧸ K) := {q | Multiplicative.toAdd q.out ∈ Λ}
  have hsame : ∀ x y : Multiplicative A, (x : Multiplicative A ⧸ K) = y ↔
      -Multiplicative.toAdd x + Multiplicative.toAdd y ∈ S := by
    intro x y
    rw [QuotientGroup.eq, hK]
    rfl
  let f : Λ → T := fun x => ⟨((Multiplicative.ofAdd (x : A) : Multiplicative A) : Multiplicative A ⧸ K),
    (hrep _).2 x.2⟩
  let g : Λ ⧸ S.addSubgroupOf Λ → T := fun y => Quotient.liftOn' y f (by
    intro x y hxy
    have h : -(x : A) + (y : A) ∈ S := by
      have := QuotientAddGroup.leftRel_apply.1 hxy
      simpa [AddSubgroup.mem_addSubgroupOf] using this
    exact Subtype.ext ((hsame _ _).2 h))
  have hg : Function.Bijective g := by
    constructor
    · intro y₁ y₂
      induction y₁ using QuotientAddGroup.induction_on with | H x =>
      induction y₂ using QuotientAddGroup.induction_on with | H y =>
      intro h
      have h' : ((Multiplicative.ofAdd (x : A) : Multiplicative A) : Multiplicative A ⧸ K) =
          ((Multiplicative.ofAdd (y : A) : Multiplicative A) : Multiplicative A ⧸ K) :=
        congrArg Subtype.val h
      refine QuotientAddGroup.eq.2 ?_
      rw [AddSubgroup.mem_addSubgroupOf]
      simpa using (hsame _ _).1 h'
    · rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨((⟨Multiplicative.toAdd x, (hrep x).1 hq⟩ : Λ) : Λ ⧸ S.addSubgroupOf Λ), rfl⟩
  have hcard : Nat.card T = S.relIndex Λ := (Nat.card_congr (Equiv.ofBijective g hg)).symm
  have hfun : (fun q : Multiplicative A ⧸ K => if Multiplicative.toAdd q.out ∈ Λ then (1 : ℂ) else 0) =
      T.indicator 1 := by
    funext q
    by_cases h : q ∈ T
    · rw [Set.indicator_of_mem h]; exact if_pos h
    · rw [Set.indicator_of_notMem h]; exact if_neg h
  rw [hfun, ← hcard]
  by_cases hT : T.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hT, Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card T hT]
    simp
  · rw [finsum_of_infinite_support (by simpa using hT)]
    haveI : Infinite T := Set.Infinite.to_subtype hT
    simp

theorem mem_intMat_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    X ∈ intMat a b w ↔ Multiplicative.toAdd X ∈ intSub a b w := by
  constructor
  · intro hX
    induction hX using Subgroup.closure_induction with
    | mem x hx => exact fun i j => hx i j
    | one => exact isInt_zero w _ _
    | mul x y _ _ hx hy => exact IsInt.add hx hy
    | inv x _ hx => exact IsInt.neg hx
  · intro hX
    exact Subgroup.subset_closure fun i j => hX i j

theorem hint_indicator_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E))), intSub a b w ≤ Λ → hint (intMat a b w) (fun X => if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) = (((intSub a b w).relIndex Λ : ℕ) : ℂ) := by
  intro E _ _ _ a b w Λ h
  have hstab : intMat a b w ≤
      rStab (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) := by
    intro k hk x
    have hkΛ : Multiplicative.toAdd k ∈ Λ := h ((mem_intMat_iff a b w k).1 hk)
    have e : (Multiplicative.toAdd (x * k) ∈ Λ) ↔ Multiplicative.toAdd x ∈ Λ := by
      rw [toAdd_mul]
      exact Λ.add_mem_cancel_right hkΛ
    simp only [e]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (intMat a b w) (intMat a b w) _ le_rfl hstab
    (by simp [Subgroup.relIndex_self])]
  rw [Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_mul]
  exact finsum_out_indicator (intSub a b w) Λ h (intMat a b w) (mem_intMat_iff a b w)

end GlobalTheory.CompanionTheory.HintInd
end
end

section


theorem _root_.GlobalTheory.T.lattice_volume_unramified : PositivityTheory.SiegelWeilFormula.Gunr.VolLat := by
  first | exact @GlobalTheory.CompanionTheory.GunrVol.volLat | exact GlobalTheory.CompanionTheory.GunrVol.volLat | (intros; apply GlobalTheory.CompanionTheory.GunrVol.volLat <;> assumption)
end
