module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaLint
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianDiagonalizeOverReducedTensor
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphTensorProductMeasure
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle060
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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ThetaCnt

theorem lintegral_thetaMeas : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ Y, Φ Y ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * cntI σ J μ 𝓕 S Φ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.thetacnt

end GlobalTheory.CompanionTheory.SW.ThetaCnt
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ThetaMean

theorem mean_thetaS_eq_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Measurable Φ → Integrable Φ (thetaMeas σ J μ 𝓕 S) → meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.theta_int

end GlobalTheory.CompanionTheory.SW.ThetaMean
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ThetaLint

theorem theta_lint_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' X : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.theta_lint

end GlobalTheory.CompanionTheory.SW.ThetaLint
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.WittTuples

theorem exists_actW_eq_of_gramR_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = gramR R σ J Y → IsUnit (gramR R σ J X).det → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ n X Y hXY hdet
  have hσ := HermTop.sigma_sigma hCM
  have hS : cT (sigR R σ) (gramR R σ J X) = gramR R σ J X := by
    ext a b
    exact HermTop.gramR_mem (R := R) hσ hJ.1 X a b
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.exists_diagonal_congr F E σ hCM R n _ hS hdet
  have hgram : ∀ Z : Fin n → Fin M → R ⊗[F] E, gramR R σ J (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J Z * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    fun Z => (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g 1).1
  have hX' := (hgram X).trans hg
  have hY' : gramR R σ J (rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      gramR R σ J (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    rw [hgram, hgram, hXY]
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag F E σ hCM R (GlobalTheory.CompanionTheory.SW.unitChoice_of_isArtinianRing_isReduced R) M J hJ n D _ _ hX' hY'
  refine ⟨h, ?_⟩
  have hk : actTup R (HA.mat R σ J h) (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      rmul R (actTup R (HA.mat R σ J h) X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J X g 1).2.2.2 _
  have he : rmul R (actW R σ J h X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := hk.symm.trans hh
  have hcancel : ∀ Z : Fin n → Fin M → R ⊗[F] E,
      rmul R (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = Z := by
    intro Z
    have h1 := GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [h1.2.1, Units.mul_inv, h1.2.2.1]
  rw [← hcancel (actW R σ J h X), he, hcancel]

end GlobalTheory.CompanionTheory.SW.WittTuples
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.coordinate_homeomorph_tensor_product_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ n : ℕ, ∃ e : (R × (Fin n → R ⊗[F] E) × HermR R σ n) ≃ₜ HermR R σ (n + 1), (∀ p, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 = p.1 ⊗ₜ[F] (1 : E)) ∧ (∀ p j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 (Fin.succ j) = p.2.1 j) ∧ (∀ p i j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (Fin.succ i) (Fin.succ j) = (p.2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j) ∧ (lam.prod ((Measure.pi fun _ => coordK R b lam).prod (coordHerm R σ b lam n))).map e = coordHerm R σ b lam (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermSplit.herm_split | exact GlobalTheory.CompanionTheory.SW.HermSplit.herm_split | (intros; apply GlobalTheory.CompanionTheory.SW.HermSplit.herm_split <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.witt_extension_diagonal_gram_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (D : Fin n → Rˣ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D i : R)) → gramR R σ J Y = gramR R σ J X → ∃ h : HA R σ J, actW R σ J h X = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag | exact GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag | (intros; apply GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.quotient_probability_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsProbabilityMeasure (prH μ 𝓕) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.isProbabilityMeasure_prH | exact GlobalTheory.CompanionTheory.SW.BB.isProbabilityMeasure_prH | (intros; apply GlobalTheory.CompanionTheory.SW.BB.isProbabilityMeasure_prH <;> assumption)
end
