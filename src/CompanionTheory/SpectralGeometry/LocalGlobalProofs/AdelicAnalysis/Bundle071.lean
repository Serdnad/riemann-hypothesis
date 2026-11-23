module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesSelfDual
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle070
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAll
public import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DiscriminantDifferentProductFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle050
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.adeles_self_dual : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → NADual (A F) (fun x y => ψ (x * y)) (ENNReal.ofReal (kap F) • lf) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.SelfDual.finiteAdeles_selfDual | exact GlobalTheory.CompanionTheory.SW.Core.SelfDual.finiteAdeles_selfDual | (intros; apply GlobalTheory.CompanionTheory.SW.Core.SelfDual.finiteAdeles_selfDual <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.hyperbolic_parabolic_siegel_set_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∃ (P : Subgroup (HA (AF F) σ (hypJ J))) (ν : Measure (HA (AF F) σ (hypJ J))) (S : ℤ → Set (HA (AF F) σ (hypJ J))) (ω : Set (AF F ⊗[F] E)ˣ) (Kc : ℝ≥0∞), (∀ h, h ∈ P ↔ ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ h (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ SFinite ν ∧ (∀ p ∈ P, ν.map (fun g => p * g) = ν) ∧ (∀ U ∈ 𝓝 (1 : HA (AF F) σ (hypJ J)), ν U ≠ 0) ∧ IsCompact ω ∧ Kc < ⊤ ∧ (∀ j, MeasurableSet (S j)) ∧ (∀ j : ℤ, ν (S j) ≤ Kc * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ))))) ∧ (∀ j : ℤ, ∀ p ∈ S j, p ∈ P ∧ ∃ c ∈ ω, actW (AF F) σ _ p (eOne _ (M + 1)) = ((τ (Multiplicative.ofAdd (j : ℝ)) * c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ ∀ᵐ p ∂ν, ∃ γ ∈ P, HA.mat (AF F) σ (hypJ J) γ ∈ HFin (AF F) σ (hypJ J) ∧ ∃ j, γ * p ∈ S j := by
  first | exact @GlobalTheory.CompanionTheory.SW.FNu.exists_nu_siegel | exact GlobalTheory.CompanionTheory.SW.FNu.exists_nu_siegel | (intros; apply GlobalTheory.CompanionTheory.SW.FNu.exists_nu_siegel <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.rank_one_local_density_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 → |(m (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocGood.density_standard_lattice | exact GlobalTheory.CompanionTheory.SW.LocGood.density_standard_lattice | (intros; apply GlobalTheory.CompanionTheory.SW.LocGood.density_standard_lattice <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SDOne
open GroundTheory.Global GroundTheory.LocalField

variable (F : Type) [Field F] [NumberField F]

theorem psiV_std (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    psiV F (Circle.coeHom.compAddChar (adelicChar F)) v y = ((localAdelicChar F v y : Circle) : ℂ) := by
  classical
  show ((adelicChar F (pairA F 0 (singleV F v y)) : Circle) : ℂ) = ((adelicChar F (finitePlaceIncl v y) : Circle) : ℂ)
  congr 2

theorem coe_integers_eq (v : HeightOneSpectrum (𝓞 F)) :
    ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v)) := by
  rw [show ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) = (valBall (Fv F v) 0 : Set (Fv F v)) from coe_valBall_zero.symm]
  ext x
  show x ∈ valBall (Fv F v) 0 ↔ x ∈ v.adicCompletionIntegers F
  rw [mem_valBall_iff_valued, HeightOneSpectrum.mem_adicCompletionIntegers]
  simp

noncomputable def cV (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 :=
  (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-differentExp v : ℤ) : ℝ) / 2)

theorem smul_eq_selfDualMeasure (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (h : IsStdV v lam) :
    cV F v • lam = GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v) := by
  obtain ⟨hH, h1⟩ := h
  have e := eq_smul_haarIntegers lam
  rw [coe_integers_eq F v, h1, one_smul] at e
  rw [e, GroundTheory.LocalField.selfDualMeasure, addCharConductor_localAdelicChar, residueCard_adicCompletion]
  rfl

theorem selfDual_std : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∃ ψ, IsCharAF F ψ ∧ ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (SelfDual (cinf • laminf) (fun s t => psiInf F ψ (s * t))) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (SelfDual (c v • lam v) (fun s t => psiV F ψ v (s * t))) := by
  intro F _ _ hF laminf lam hinf hlam
  refine ⟨Circle.coeHom.compAddChar (adelicChar F), ?_, Real.toNNReal (Real.sqrt |(discr F : ℝ)|), cV F, ?_, GlobalTheory.T.archimedean_selfdual_measure_discriminant_scaled F hF laminf hinf, fun v => ?_⟩
  · refine ⟨continuous_subtype_val.comp (continuous_adelicChar (K := F)), fun x => Circle.norm_coe _, fun a => ?_, ?_⟩
    · show ((adelicChar F _ : Circle) : ℂ) = 1
      rw [adelicChar_algebraMap]
      rfl
    · by_contra h
      push Not at h
      apply adelicChar_ne_one (K := F)
      ext x
      exact h x
  · exact GlobalTheory.T.discriminant_different_product_formula F
  · rw [smul_eq_selfDualMeasure F v (lam v) (hlam v)]
    simp only [psiV_std]
    exact GlobalTheory.T.local_field_selfdual_measure_exists _ _ (continuous_localAdelicChar v) (localAdelicChar_ne_one v)

end GlobalTheory.CompanionTheory.SW.SDOne
end
