module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSobolevInequalityAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteEpsilonFactorDependenceOnS
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle041
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp.RealLog

theorem exists_small_log : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D), IsInfFam θ → ∀ (V : HSp D) (δ : ℝ), 0 < δ →
    ∃ N ∈ 𝓝 (1 : GA D V), ∀ r ∈ N, r ∈ GinfC V →
      ∃ X : GlobalTheory.SmoothForms.LieN V, ‖X‖ < δ ∧ GlobalTheory.SmoothForms.expInf θ V X = r := by
  intro D θ hθ V δ hδ
  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨δ₁, C, hδ₁, hC, hlog⟩ := GlobalTheory.CuspGeo.MeanValue.exists_log hθ R
  set ε : ℝ := min δ₁ (δ / (2 * (C + 1))) with hε
  have hε0 : 0 < ε := lt_min hδ₁ (by positivity)
  have hCε : C * ε < δ := by
    have h1 : ε ≤ δ / (2 * (C + 1)) := min_le_right _ _
    have h2 : C * ε ≤ C * (δ / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h1 hC
    have h3 : C * (δ / (2 * (C + 1))) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    exact lt_of_le_of_lt h2 h3
  have hcont : ∀ τ, Continuous fun g : GA D V => infMat D.sp.cm.sig V.gram (θ τ) g := by
    intro τ
    have hc := GlobalTheory.SobLoc.continuous_arch (θ := θ) hθ V τ
    simpa only [Formalism.IndefR.FWT.archM_eq] using hc
  have hone : ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (1 : GA D V) = 1 :=
    fun τ => R.2.2.2.2.1 1 (one_mem _) τ
  refine ⟨⋂ τ, ⋂ i, ⋂ j, {g : GA D V | ‖(infMat D.sp.cm.sig V.gram (θ τ) g - 1) i j‖ < ε}, ?_, ?_⟩
  · refine Filter.iInter_mem.2 fun τ => Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => ?_
    refine IsOpen.mem_nhds ?_ ?_
    · exact isOpen_lt (((hcont τ).sub continuous_const).matrix_elem i j).norm continuous_const
    · simp only [Set.mem_ofPred_eq, hone, sub_self, Matrix.zero_apply, norm_zero]
      exact hε0
  · intro r hr hrinf
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hr
    have hclose : GlobalTheory.CuspGeo.CloseR θ V r ε := ⟨hrinf, fun τ i j => (hr τ i j).le⟩
    obtain ⟨Z, hZ, hn⟩ := hlog r ε hε0.le (min_le_left _ _) hclose
    exact ⟨Z, lt_of_le_of_lt hn hCε, hZ⟩

end GlobalTheory.CompanionTheory.HCCusp.RealLog

end
end

section

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity :=
  CompanionTheory.FamInh.globalArtin

end GlobalTheory.CompanionTheory.Hypotheses₂
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)


theorem _root_.GlobalTheory.T.finite_epsilon_factor_dependence_on_s : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ), finEps χ a s = finEps χ a (1 / 2) * (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift | exact GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsCovolOne (db : Measure (AF F)) : Prop :=
  db.IsAddHaarMeasure ∧ ∃ D : Set (AF F),
    IsAddFundamentalDomain (algebraMap F (AF F)).toAddMonoidHom.range D db ∧ db D = 1

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV
end
end
