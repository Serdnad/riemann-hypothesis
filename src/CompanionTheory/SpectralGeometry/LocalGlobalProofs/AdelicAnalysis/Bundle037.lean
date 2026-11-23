module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PositiveDefiniteDensity
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryFiniteSetDecomposition
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityUnique
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import GroundTheory.AutomorphicForms.Bundle012
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle035
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.quadratic_level_set_density : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∃ Di : (InfinitePlace F → ℝ) → ℝ, Continuous Di ∧ (∀ y, 0 ≤ Di y) ∧ (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (P w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Di y)) ∧ Integrable (fun x : InfinitePlace F → ℝ => cG B ρ P (fun w => (x w : ℂ) + Complex.I)) ∧ ∀ z : InfinitePlace F → ℝ, ∫ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) = ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di z : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Dens.density_of_q | exact GlobalTheory.CompanionTheory.SW.Core.Dens.density_of_q | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Dens.density_of_q <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.positive_definite_density : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ (m : Measure V), IsFiniteMeasure m → Integrable (fun y => ∫ x, χ x y ∂m) μ → ∃ D : V → ℝ, Continuous D ∧ (∀ x, 0 ≤ D x) ∧ (∀ x, (D x : ℂ) = ∫ y, (∫ z, χ z y ∂m) * χ (-x) y ∂μ) ∧ ∀ U : Set V, MeasurableSet U → m U = ∫⁻ x in U, ENNReal.ofReal (D x) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Density.exists_density | exact GlobalTheory.CompanionTheory.SW.Core.Density.exists_density | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Density.exists_density <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_unitary_finite_set_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ∃ (ginf : HA (Ainf F) σ (blockOne (algebraMap F E t) J)) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ (blockOne (algebraMap F E t) J)) (Sh : Finset (HeightOneSpectrum (𝓞 F))), ∀ S, S₁ ⊆ S → (∀ (n : ℕ) (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (X : Fin n → Fin M → AF F ⊗[F] E), pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) = pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ _ ginf (consTup Y))) (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) X) ∧ ∀ (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) = (Ψinf (actW (Ainf F) σ _ ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) * ∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PureH.pure_h | exact GlobalTheory.CompanionTheory.SW.PureH.pure_h | (intros; apply GlobalTheory.CompanionTheory.SW.PureH.pure_h <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.EulerBox

section Box

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem pureL_indicator_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hS : ∀ v, v ∉ S → A v = latV b v) (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S φinf (fun v => (A v).indicator 1) X =
      {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v}.indicator
        (fun X => φinf (projInf X)) X := by
  by_cases hX : ∀ v, projV v (projFin X) ∈ A v
  · have hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := fun v hv => by
      rw [← hS v hv]; exact hX v
    have hB : X ∈ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := hX
    rw [pureL, Set.indicator_of_mem hI, Set.indicator_of_mem hB,
      Finset.prod_eq_one (fun v _ => Set.indicator_of_mem (hX v) _), mul_one]
  · have hB : X ∉ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := hX
    rw [Set.indicator_of_notMem hB]
    obtain ⟨v, hv⟩ := not_forall.1 hX
    by_cases hvS : v ∈ S
    · by_cases hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))
      · rw [pureL, Set.indicator_of_mem hI,
          Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _), mul_zero]
      · rw [pureL, Set.indicator_of_notMem hI]
    · have hI : X ∉ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := fun h => hv (by
        rw [hS v hvS]; exact h v hvS)
      rw [pureL, Set.indicator_of_notMem hI]

theorem box_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hS : ∀ v, v ∉ S → A v = latV b v) :
    {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
      intOff b S ∩ ⋂ v ∈ S, (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) ⁻¹' A v := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h
    exact ⟨fun v hv => by rw [← hS v hv]; exact h v, fun v _ => h v⟩
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S
    · exact h2 v hv
    · rw [hS v hv]; exact h1 v hv

end Box

theorem measurableSet_box (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨-, -, -, -, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  have : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := hB n M
  obtain ⟨-, hFin, hV, -, hOff, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  have hmeas : ∀ v, Measurable
      (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) := fun v => by
    have hc : Continuous (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) :=
      (hV v).comp hFin
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
    have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
    exact (((continuous_apply i).comp (continuous_apply a)).comp hc).measurable
  rw [box_eq b S A hS]
  exact (hOff S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v _ => hmeas v (hA v))

theorem euler_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I c minf m → ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable φinf → (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) < ⊤) → (∀ᶠ v in Filter.cofinite, A v = latV b v) → Multipliable (fun v => (m v (A v)).toReal) ∧ ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I = (c : ℝ≥0∞) * (∫⁻ X, φinf X ∂minf) * ENNReal.ofReal (∏' v, (m v (A v)).toReal) := by
  intro F E _ _ _ _ _ σ hσ d b n M I c minf m hE φinf A hφ hA hfin hcof
  classical
  obtain ⟨-, hsum, S₀, hS₀⟩ := hE
  have hfinite : {v | ¬ A v = latV b v}.Finite := Filter.eventually_cofinite.1 hcof
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ hfinite.toFinset with hSdef
  have hS : ∀ v, v ∉ S → A v = latV b v := fun v hv => by
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfinite.mem_toFinset.2 hne))
  have hsumA : Summable (fun v => |(m v (A v)).toReal - 1|) :=
    hsum.congr_cofinite (hcof.mono fun v hv => by simp only [hv])
  obtain ⟨hmul, hsplit, -, hnn⟩ := GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ _ hsumA
  refine ⟨hmul, ?_⟩
  have hbox := measurableSet_box F E σ hσ b n M S A hA hS
  have hform := hS₀ S Finset.subset_union_left φinf (fun v => (A v).indicator 1) hφ
    (fun v => measurable_one.indicator (hA v))
  have hlhs : ∫⁻ X, pureL b S φinf (fun v => (A v).indicator 1) X ∂I =
      ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I := by
    simp_rw [pureL_indicator_eq b S φinf A hS]
    exact lintegral_indicator hbox _
  have hloc : ∀ v, ∫⁻ X, (A v).indicator 1 X ∂(m v) = ENNReal.ofReal (m v (A v)).toReal := fun v => by
    rw [lintegral_indicator_one (hA v), ENNReal.ofReal_toReal (hfin v).ne]
  have htail : ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal =
      ∏' v : {v // v ∉ S}, (m v.1 (A v.1)).toReal :=
    tprod_congr fun v => by rw [hS v.1 v.2]
  rw [hlhs] at hform
  rw [hform, htail, (hsplit S).2]
  simp_rw [hloc]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg fun v _ => ENNReal.toReal_nonneg]
  ring

end GlobalTheory.CompanionTheory.SW.EulerBox
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.lintegral_coordW_succ_eq_iterated_of_unitary_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ (n : ℕ) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J), Measurable s → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ y, ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E, φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) ∂(coordW R b lam 1 (M + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame | exact GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame | (intros; apply GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_measures_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ m', IsGramFib R σ J n μ ν m' → ∀ S, m S = m' S := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique | exact GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique | (intros; apply GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramDensity

theorem isContDensityOn_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℂ, Continuous φ → HasCompactSupport φ → IsContDensityOn μ (gramR R σ J) Subtype.val ν {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} φ (fun S => ∫ X, φ X ∂(m S)) ∧ ∀ S, Integrable φ (m S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hfib φ hφ hφc
  have hunits : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have := iB n M
  have := iTR
  have := iLC
  have := iSC
  have := iT2
  obtain ⟨jLC, jSC, jT2, jB, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  have := jLC
  have := jSC
  have := jT2
  have := jB
  obtain ⟨g, hg, hgram⟩ := hlift M J hJ
  have hB : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hdet : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have hset : {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} =
        (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
          Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp [IsUnit]
    rw [hset]
    exact hunits.isOpen_range.preimage hdet
  have hpre : {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} =
      g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    ext X
    simp [hgram X]
  have hfib' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val
      (g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}) ν
      {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m := by
    rw [← hpre]
    exact hfib
  exact GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral _ _ _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hg hgram _ hB m hfib' φ hφ hφc

end GlobalTheory.CompanionTheory.SW.GramDensity
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StdEx

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open NumberField.mixedEmbedding
open scoped TensorProduct ENNReal NNReal Matrix

variable (F : Type) [Field F] [NumberField F]

theorem exists_isStdV (v : HeightOneSpectrum (𝓞 F)) : ∃ lam : Measure (Fv F v), IsStdV v lam := by
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hc := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let K : TopologicalSpace.PositiveCompacts (Fv F v) :=
    ⟨⟨(v.adicCompletionIntegers F : Set (Fv F v)), isCompact_iff_compactSpace.2 hc⟩, by
      change (interior (v.adicCompletionIntegers F : Set (Fv F v))).Nonempty
      have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
        Valued.isOpen_valuationSubring _
      rw [hO.interior_eq]
      exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩


omit [NumberField F] in
theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedSpace F) =
      fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)


omit [NumberField F] in
theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem mem_span_iff (x : mixedSpace F) :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis F)) ↔
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x ∈
        ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range := by
  have hk : x ∈ mixedEmbedding.integerLattice F ↔ ∃ a : 𝓞 F, mixedEmbedding F (a : F) = x := by
    simp [LinearMap.mem_range]
  rw [mem_span_latticeBasis, hk]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]
    rfl
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.injective
    rw [RingEquiv.symm_apply_apply]
    exact ha

theorem exists_isStdInf : ∃ laminf : Measure (Ainf F), IsStdInf laminf := by
  classical
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hce : Continuous e := continuous_toMixed F
  have hcs : Continuous e.symm := continuous_ofMixed F
  let D₀ : Set (mixedSpace F) := ZSpan.fundamentalDomain (latticeBasis F)
  let μ₀ : Measure (mixedSpace F) := volume
  have h0 : μ₀ D₀ ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero (latticeBasis F)
  have ht : μ₀ D₀ ≠ ∞ := (ZSpan.fundamentalDomain_isBounded (latticeBasis F)).measure_lt_top.ne
  have hD₀ : MeasurableSet D₀ := ZSpan.fundamentalDomain_measurableSet (latticeBasis F)
  let c : ℝ≥0 := ((μ₀ D₀).toNNReal)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (ENNReal.toNNReal_ne_zero.2 ⟨h0, ht⟩)
  let μ₁ : Measure (mixedSpace F) := c • μ₀
  have : μ₁.IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ₀ hc
  have hμ₁ : μ₁ D₀ = 1 := by
    have hv : ((μ₀ D₀).toNNReal : ℝ≥0∞) = μ₀ D₀ := ENNReal.coe_toNNReal ht
    have hne : (μ₀ D₀).toNNReal ≠ 0 := ENNReal.toNNReal_ne_zero.2 ⟨h0, ht⟩
    change (c • μ₀) D₀ = 1
    rw [Measure.smul_apply, ← hv, ENNReal.smul_def, smul_eq_mul, hv, ← hv, ← ENNReal.coe_mul,
      inv_mul_cancel₀ hne, ENNReal.coe_one]
  let E : Ainf F ≃ᵐ mixedSpace F :=
    (Homeomorph.mk e.toEquiv hce hcs).toMeasurableEquiv
  let lam : Measure (Ainf F) := Measure.map e.symm μ₁
  have hlamE : lam = Measure.map E.symm μ₁ := rfl
  have hmp : MeasurePreserving E lam μ₁ := by
    refine ⟨E.measurable, ?_⟩
    rw [hlamE, Measure.map_map E.measurable E.symm.measurable]
    simp
  refine ⟨lam, ?_, e ⁻¹' D₀, ?_, ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map μ₁ e.symm.toAddEquiv hcs hce
  · have hF₀ := ZSpan.isAddFundamentalDomain (latticeBasis F) μ₁
    refine hF₀.preimage_of_equiv (f := e) hmp.quasiMeasurePreserving
      (e := fun g => ⟨e.symm g.1, (mem_span_iff F g.1).1 g.2⟩) ⟨?_, ?_⟩ ?_
    · intro g h hgh
      exact Subtype.ext (e.symm.injective (congrArg Subtype.val hgh))
    · rintro ⟨y, hy⟩
      refine ⟨⟨e y, (mem_span_iff F (e y)).2 (by
        change e.symm (e y) ∈ _
        rw [e.symm_apply_apply]
        exact hy)⟩, ?_⟩
      exact Subtype.ext (e.symm_apply_apply y)
    · intro g x
      change e (e.symm g.1 + x) = g.1 + e x
      rw [map_add (f := _), e.apply_symm_apply]
  · exact (hmp.measure_preimage hD₀.nullMeasurableSet).trans hμ₁

theorem exists_std : ∀ (F : Type) [Field F] [NumberField F],
    (∃ laminf : Measure (Ainf F), IsStdInf laminf) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∃ lam : Measure (Fv F v), IsStdV v lam :=
  fun F _ _ => ⟨exists_isStdInf F, exists_isStdV F⟩

end GlobalTheory.CompanionTheory.SW.StdEx
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_coordinate_measure_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → (coordW (Ainf F) b laminf 1 M).map (fun X w => xw e b X w) = ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.infPush | exact GlobalTheory.CompanionTheory.SW.BB.infPush | (intros; apply GlobalTheory.CompanionTheory.SW.BB.infPush <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_block_one_schur_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → (∀ x ∈ B₀, ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) (S : HermR R σ (n + 1)), (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = gramR R σ (blockOne (algebraMap F E t) J) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X) → s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x ∧ cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c ∧ (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = gramR R σ J X) ∧ (∀ (S : HermR R σ (n + 1)) (X : Fin n → Fin M → R ⊗[F] E), s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ → gramR R σ J X = (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → gramR R σ (blockOne (algebraMap F E t) J) (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) ⊗ₜ[F] (1 : E)) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.lintegral_coordK_coordHerm_scale_shear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (u : Rˣ) (w : (Fin n → R ⊗[F] E) → HermR R σ n), Measurable w → ∀ f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞, Measurable f → ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) = (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j), S'' - w r) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate <;> assumption)
end
