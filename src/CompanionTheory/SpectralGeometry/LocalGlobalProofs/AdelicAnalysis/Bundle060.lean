module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle059
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatrixEulerProduct
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RightMultiplicationEulerProduct
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle001
public import CompanionTheory.AutomorphicTheory.ThetaDilations.HfSubSmul
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
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

theorem _root_.GlobalTheory.T.scalar_multiplication_euler_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : E, t ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Ainf F) t * y) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Fv F v) t * y) = c v • μ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula | exact GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula | (intros; apply GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.haar_modulus_gl_action_product_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (g : GL (Fin M) E), ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure → μ.map (actTup (Ainf F) (bc (inclR (Ainf F)) g)) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (actTup (Fv F v) (bc (inclR (Fv F v)) g)) = c v • μ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PfAct.product_formula_actTup | exact GlobalTheory.CompanionTheory.SW.PfAct.product_formula_actTup | (intros; apply GlobalTheory.CompanionTheory.SW.PfAct.product_formula_actTup <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.hermitian_matrix_euler_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) E), g.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure → ∀ τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = cT (sigR (Ainf F) σ) (g.map (inclR (Ainf F))) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g.map (inclR (Ainf F))) → ν.map τ = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ ν : Measure (HermR (Fv F v) σ n), ν.IsAddHaarMeasure → ∀ τ : HermR (Fv F v) σ n → HermR (Fv F v) σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) (g.map (inclR (Fv F v))) * (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * g.map (inclR (Fv F v))) → ν.map τ = c v • ν) := by
  first | exact @GlobalTheory.CompanionTheory.SW.pf_herm | exact GlobalTheory.CompanionTheory.SW.pf_herm | (intros; apply GlobalTheory.CompanionTheory.SW.pf_herm <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.right_multiplication_euler_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (g : Matrix (Fin n) (Fin n) E), g.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun X => rmul (Ainf F) X (g.map (inclR (Ainf F)))) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun X => rmul (Fv F v) X (g.map (inclR (Fv F v)))) = c v • μ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.RmulPF.rmul_product_formula | exact GlobalTheory.CompanionTheory.SW.RmulPF.rmul_product_formula | (intros; apply GlobalTheory.CompanionTheory.SW.RmulPF.rmul_product_formula <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.WittDiag

theorem trans_diag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (D : Fin n → Rˣ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D i : R)) → gramR R σ J Y = gramR R σ J X → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hcm R _ _ hU M J hJ n D X Y hX hY
  obtain ⟨g, hg, e⟩ := CompanionTheory.PlacePermOperatorBicommutantSpan.witt_diag (GlobalTheory.GaussMean.OneVec.sigR_sigR R hcm) (CompanionTheory.PlacePermOperatorBicommutantSpan.cT_JR' R hJ) _
    (fun i => (D i).isUnit.map _)
    (fun i t => LamUnit.exists_norm_one_sub_isUnit F E σ hcm R hU t (D i)) X Y
    (fun a b => congrFun (congrFun hX a) b)
    fun a b => congrFun (congrFun (hY.trans hX) a) b
  exact ⟨⟨g, hg⟩, funext e⟩

end GlobalTheory.CompanionTheory.SW.WittDiag
end

section

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem isProbabilityMeasure_prH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsProbabilityMeasure (prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ μ 𝓕 hμ h𝓕
  have hfin : μ 𝓕 < ⊤ := ((GlobalTheory.T.unitary_group_finite_volume F E σ hσ M J hJ).2 μ hμ).2 𝓕 h𝓕
  obtain ⟨hlc, hsc, ht2⟩ := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).1
  obtain ⟨htg, hlcH, hscH, ht2H, hbor, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have hcount : Countable (HFinIn (AF F) σ J) := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hσ M J hJ).1
  have hne : μ 𝓕 ≠ 0 :=
    (@GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain (HA (AF F) σ J) _ _ htg ht2H hlcH hscH _ hbor
      (HFinIn (AF F) σ J) hcount μ hμ 𝓕 h𝓕 hfin).1
  refine ⟨?_⟩
  simp only [prH, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hne hfin.ne

end GlobalTheory.CompanionTheory.SW.BB
end
end
