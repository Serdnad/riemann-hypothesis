module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle054
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle063
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneGramMeasurableSection
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle284
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem fibre_family_near_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J), Measurable s → (∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y) → (∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C') → ∃ B : Set (HermR R σ (n + 1)), IsOpen B ∧ hermOf R σ _ hT' ∈ B ∧ (∀ S ∈ B, IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1)) (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B)) (coordHerm R σ b lam (n + 1)) B fib ∧ fib (hermOf R σ _ hT') = c ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hdet hT' R _ _ _ _ _ hR d b lam hlam m₁ m' hm₁ hm' c hc s hs hsec hcpt
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J hJ t ht
  obtain ⟨tu, htu⟩ : IsUnit (algebraMap F R t) := (isUnit_iff_ne_zero.mpr ht).map (algebraMap F R)
  obtain ⟨B₀, a, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.local_units_continuous_square_root R hR tu
  rw [htu] at h2 h5 h6
  obtain ⟨κ₁, cm, k1, k2, k3, k4, k5, k6⟩ := GlobalTheory.T.coordK_map_mul_eq_smul_continuous_modulus F E σ hCM (M + 1) _ hJ' t ht R hR d b lam hlam m₁ hm₁
  have D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm :=
    { hCM := hCM, hJ := hJ, ht := ht, hR := hR, hlam := hlam, hm₁ := hm₁, hm' := hm', hs := hs, hsec := hsec,
      hcpt := hcpt, hB₀ := h1, htB := h2, hac := h3, hoff := h4, hsq := h5, ha1 := h6, hκc := k1, hκ1 := k2,
      hscale := k3, hcmc := k4, hmod := k5 }
  have V := GlobalTheory.T.gram_fiber_cons_at_block_one_eq_map_prod F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D T hT hdet hT'
  refine ⟨Bset R σ t a B₀, (GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).2.2.2.2, V.1,
    GlobalTheory.T.isUnit_det_of_mem_Bset' F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D, fibS σ J t m₁ m' s B₀ a κ₁ cm,
    ⟨GlobalTheory.T.gram_fiber_cons_concentrated_on_fiber F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D, ?_, ?_⟩, ?_⟩
  · intro φ hφ
    exact (GlobalTheory.T.setLIntegral_Uset_coordW_eq_Mid F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ).trans
      (GlobalTheory.T.gram_fiber_cons_iterated_lintegral_eq_Mid F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ).symm
  · intro φ hc hs' _
    exact GlobalTheory.T.gram_fiber_cons_integrable_and_continuousOn_integral F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hc hs'
  · rw [V.2, k6 c hc]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransA

theorem trans_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (X : Fin n → Fin M → E) (Y : Fin n → Fin M → AF F ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
    ∃ h : HA (AF F) σ J, actW (AF F) σ J h (ratTup (AF F) X) = Y :=
  fun F E _ _ _ _ _ σ hcm M J hJ n =>
    GlobalTheory.T.adelic_orbit_of_rational_tuple F E σ hcm (AF F) (PIW.AdelicOrbitU.stP F) n M J hJ

end GlobalTheory.CompanionTheory.SW.TransA
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.lintegral_thetaMeas_block_one_eq_rank_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) 𝓕, IsHaarH F E σ (M + 1) _ μ → IsFDH F E σ (M + 1) _ μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ (Φ : (Fin (n + 1) → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, Φ (actW (AF F) σ _ h (consTup X)) ∂(thetaMeas σ J μ₁ 𝓕₁ {X | gramE σ J X = T})) → ∫⁻ X, Φ X ∂(thetaMeas σ _ μ 𝓕 {X | gramE σ (blockOne (algebraMap F E t) J) X = blockOne (algebraMap F E t) T}) = ∫⁻ y, Ψ y ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaStage.theta_stage | exact GlobalTheory.CompanionTheory.SW.ThetaStage.theta_stage | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaStage.theta_stage <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.rank_one_gram_measurable_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin M → R ⊗[F] E, IsUnit (gramR R σ J x).det → ∃ s : (Fin 1 → Fin M → R ⊗[F] E) → HA R σ J, Measurable s ∧ (∀ y, gramR R σ J y = gramR R σ J x → actW R σ J (s y) x = y) ∧ ∀ C : Set (Fin 1 → Fin M → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ J), IsCompact C' ∧ ∀ y ∈ C, gramR R σ J y = gramR R σ J x → s y ∈ C' := by
  first | exact @GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section | exact GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section | (intros; apply GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.siegel_weil_orbital_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ I : Measure (Fin n → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ℝ≥0, ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → ∫⁻ X, pureL b S φinf φ X ∂I = (c : ℝ≥0∞) * ((∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ T hT))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ T hT))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FactS.fact_S | exact GlobalTheory.CompanionTheory.SW.FactS.fact_S | (intros; apply GlobalTheory.CompanionTheory.SW.FactS.fact_S <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.theta_integral_over_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (S : Set (Fin M × Fin d → F)) (T : Set (Fin 1 → Fin M → E)), (∀ x, ofF b x ∈ T ↔ x ∈ S) → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 T) = ∫⁻ ω, ∑' x : S, Φ (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord | exact GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord | (intros; apply GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.FieldCocompact

theorem discrete_cocompact : ∀ (F : Type) [Field F] [NumberField F],
    (∃ C : Set (AdeleRing (𝓞 F) F), IsCompact C ∧
      ∀ y, ∃ l : F, y - algebraMap F (AdeleRing (𝓞 F) F) l ∈ C) ∧
    (∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C →
      {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite) ∧
    NoncompactSpace (AdeleRing (𝓞 F) F) := by
  intro F _ _
  have hfin : ∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C →
      {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite := fun C hC =>
    GlobalTheory.Eis.Conv.Discr.finite_of_isCompact (algebraMap F (AdeleRing (𝓞 F) F))
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F) hC
  refine ⟨GlobalTheory.AdeleCocompact.exists_compact_adele F, hfin, ⟨fun h => ?_⟩⟩
  have h1 := hfin Set.univ h
  simp only [Set.mem_univ, Set.setOf_true] at h1
  exact Set.infinite_univ h1

end GlobalTheory.CompanionTheory.Adelic.FieldCocompact
end
