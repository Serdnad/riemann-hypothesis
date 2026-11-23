module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle449
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdA
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.DataHost
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem domBound (θ : InfFam D) (hθ : IsInfFam θ) {a b : ℕ} (Φ : Mx D a b → ℂ) (hΦ : Φ ∈ schwartzA θ a b) :
    ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ) (M : ℝ), 0 ≤ M ∧
      ∀ x, ‖Φ x‖ ≤ M * ∑ i, ‖f i (fun τ i j => compAt θ τ x i j)‖ := by
  obtain ⟨-, k, f, g, hg, hb⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ a b Φ hΦ
  choose C hC using fun i => ((hg i).1.continuous).bounded_above_of_compact_support (hg i).2
  refine ⟨k, f, ∑ i, max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun x => ?_⟩
  have h1 : ‖Φ x‖ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ := by
    have h := hb x
    simp only [enorm_eq_nnnorm, ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_le_coe] at h
    have h' : ((‖Φ x‖₊ : NNReal) : ℝ) ≤ ((∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) *
        g i (fun i' j => finPart D (x i' j))‖₊ : NNReal) : ℝ) := NNReal.coe_le_coe.mpr h
    simpa only [coe_nnnorm, NNReal.coe_sum] using h'
  refine h1.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, mul_comm (∑ i, max (C i) 0)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (hC i _).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (f := fun i => max (C i) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ i)))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

abbrev fixE {F : Type} [Field F] [NumberField F] (ε : AF F) : AddSubgroup (AF F) := fixS (AddMonoidHom.mulLeft ε)


open Classical in
def IsIdF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) : Prop :=
  fstA F ε = 1 ∧ ∀ v, (sndA F ε) v = if v ∈ S then 1 else 0

def OneD : Prop := ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsIdF S ε → ∀ ν : Measure (fixE ε), ν.IsAddHaarMeasure →
  ∃ (g : ℕ → fixE ε → ℂ) (G : ℕ → AF F → ℝ) (Sp : ℕ → Set (AF F)),
    (∀ k, Integrable (g k) ν ∧ (∀ h, ‖g k h‖ ≤ 1) ∧ ∀ s, 0 ≤ G k s ∧ ∫ h, g k h * ψ (h.1 * s) ∂ν = G k s) ∧
    (∀ h, Tendsto (fun k => g k h) atTop (𝓝 1)) ∧
    (∀ k s, G k s ≠ 0 → -(ε * s) ∈ Sp k) ∧ Tendsto Sp atTop (𝓝 (0 : AF F)).smallSets

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw

def HasLevel {D : D7} {n : ℕ} {X : Type} (f : G D n → X) : Prop :=
  ∃ U : Subgroup (G D n), IsOpen (U : Set (G D n)) ∧ ∀ k ∈ U, k ∈ finPts D.sp.cm.sig (Jst D n) → ∀ g, f (g * k) = f g

def ResCore : Prop :=
  ∀ (D : D7) (n t : ℕ) (B W : HSp D), Nonempty (HypDec B W t) → W.rank + t = n → W.rank + 2 < 2 * t → W.rank < t →
  1 ≤ W.rank → ∀ ψ, IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ → ResEta D χ W.rank → ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μB : Measure (Mx D B.rank n)) (μW : Measure (Mx D W.rank n)), (∃ 𝓕, IsCovolOne (ratMx D B.rank n) μB 𝓕) →
    (∃ 𝓕, IsCovolOne (ratMx D W.rank n) μW 𝓕) →
  ∀ (ωB : G D n →* Module.End ℂ (schwartzA θ B.rank n)) (ωW : G D n →* Module.End ℂ (schwartzA θ W.rank n)),
    IsWeilSch ψ χ θ B μB ωB → IsWeilSch ψ χ θ W μW ωW →
  ∀ H : G D n → ℝ≥0, IsHt H → HasLevel H → ∀ Φ : schwartzA θ B.rank n,
  ∀ U d E σ, IsCont H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) U d E σ → ∀ ε, IsRad U d ((t : ℂ) / 2) ε →
    (∀ k, 2 ≤ k → cf d E ((t : ℂ) / 2) ε k = 0) ∧
    ∀ (X : Type) [MeasurableSpace X] (π : Measure X) [IsFiniteMeasure π] (c : X → G D n) (κ : X → ℂ), Measurable c →
      IsCompact (closure (Set.range c)) → Integrable κ π →
      (∀ (Ψ : schwartzA θ W.rank n) (h : GA D W), ∫ x, theta ωW Ψ (c x) h * κ x ∂π = 0) →
      ∫ x, cf d E ((t : ℂ) / 2) ε 1 (c x) * κ x ∂π = 0

end PositivityTheory.Rg.Rsw

end
end
