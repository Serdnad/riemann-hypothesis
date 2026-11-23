module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionRayAsymptotic
public import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle732
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityOfMassOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle726

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem _root_.GlobalTheory.T.rank_one_siegel_weil_theta_average : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ 1 J μ → IsFDH F E σ 1 J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ x : (AF F ⊗[F] E)ˣ, mean σ J μ 𝓕 φ A x = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, Th φ A (x * ue (AF F) σ J h⁻¹) ∂μ ∧ Measurable fun h : HA (AF F) σ J => Th φ A (x * ue (AF F) σ J h⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem _root_.GlobalTheory.T.unitary_scalar_has_norm_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ h : HA (AF F) σ J, IsNm σ (ue (AF F) σ J h) 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem _root_.GlobalTheory.T.theta_test_function_ray_asymptotic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∃ (N : ℕ) (ρ : ℝ), 0 < N ∧ ∀ k ∈ K, ∀ (X : Fin 1 → Fin 1 → E) (ε : ℝ), 0 < ε → Psi φ A (fun a i => ((k * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 → (∀ (p : Fin 1 × Fin 1 × Fin d) (v : HeightOneSpectrum (𝓞 F)), algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧ ∀ (p : Fin 1 × Fin 1 × Fin d) (w : InfinitePlace F), ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem _root_.GlobalTheory.T.idele_module_base_change_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ a : (AF F)ˣ, (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a)) : ℝ) = md a ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SW.MdBase.ideleModule_ideleEquiv_ofF | exact GlobalTheory.CompanionTheory.SW.MdBase.ideleModule_ideleEquiv_ofF | (intros; apply GlobalTheory.CompanionTheory.SW.MdBase.ideleModule_ideleEquiv_ofF <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi

theorem measurable_pure_rv_zero (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hG : Continuous G)
    (hg : ∀ v ∈ S, Continuous (g v)) :
    Measurable (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) := by
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hval : Measurable (Units.val : (AF F)ˣ → AF F) := comap_measurable _
  have hfst : Continuous (fun x : AF F => x.1) := continuous_fst
  have hev : ∀ v : HeightOneSpectrum (𝓞 F), Continuous (fun x : AF F => x.2 v) := fun v =>
    (RestrictedProduct.continuous_eval v).comp continuous_snd
  have hc : Continuous (fun x : AF F => G x.1 * ∏ v ∈ S, g v (x.2 v)) :=
    (hG.comp hfst).mul (continuous_finsetProd _ fun v hv => (hg v hv).comp (hev v))
  have hopen : IsOpen {x : AF F | ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers F} :=
    (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v : HeightOneSpectrum (𝓞 F) => v ∉ S)).preimage continuous_snd
  have hh : Measurable (fun x : AF F => if ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers F then
      ENNReal.ofReal (G x.1 * ∏ v ∈ S, g v (x.2 v)) else 0) :=
    Measurable.ite hopen.measurableSet (ENNReal.measurable_ofReal.comp hc.measurable)
      measurable_const
  have he : (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) = (fun x : AF F =>
      if ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G x.1 * ∏ v ∈ S, g v (x.2 v)) else 0) ∘ Units.val :=
    funext fun a => GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply S G g a
  rw [he]
  exact hh.comp hval

end GlobalTheory.CompanionTheory.BasePsi

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.module_ray_eq_pow_degree : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.md_ray | exact GlobalTheory.CompanionTheory.BasePsi.md_ray | (intros; apply GlobalTheory.CompanionTheory.BasePsi.md_ray <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.pure_adelic_function_formula : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a =
      if ∀ v, v ∉ S → (a : AF F).2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G (a : AF F).1 * ∏ v ∈ S, g v ((a : AF F).2 v)) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply | exact GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply | (intros; apply GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply <;> assumption)
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.local_density_of_mass_one : Scal → PositivityTheory.SiegelWeilFormula.Densx.MassOne → LocR := by
  first | exact @GlobalTheory.CompanionTheory.RankOneLoc.locR | exact GlobalTheory.CompanionTheory.RankOneLoc.locR | (intros; apply GlobalTheory.CompanionTheory.RankOneLoc.locR <;> assumption)
end
