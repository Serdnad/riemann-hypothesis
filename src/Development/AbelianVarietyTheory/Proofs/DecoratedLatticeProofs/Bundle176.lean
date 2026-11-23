module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrthogonalTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle378
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ThetaOrthTotal

theorem eq_zero_of_orthogonal_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ q : WO S T → ℂ, Continuous q → (∀ γ w, q (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * q w) → (∀ f, IsThetaFunO ψ S T f → ∫ w in 𝓕, q w * star (f w) ∂μ = 0) → q = 0 := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 q hq hquasi horth
  obtain ⟨f₀, hne, h₀⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨hl, hr, halt, hdbl, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hψc, hψn, -, -⟩ := hψ.1
  have hann : ∀ x : WO S T, (∀ γ ∈ ratL T S, ψ (symplOH S T x γ + symplOH S T x γ) = 1) ↔ x ∈ ratL T S := by
    intro x
    simp only [hdbl]
    exact GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x
  have hq' : ∀ γ ∈ ratL T S, ∀ w, q (γ + w) = ψ (-(symplOH S T γ w)) * q w := by
    intro γ hγ w
    obtain ⟨γ', rfl⟩ := hγ
    exact hquasi γ' w
  have horth' : ∀ w, ∫ x in 𝓕, heisO ψ S T w f₀ x * star (q x) ∂μ = 0 := by
    intro w
    have h := horth _ ((GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 w f₀ h₀)
    have e : (fun x => heisO ψ S T w f₀ x * star (q x)) = fun x => (starRingEnd ℂ) (q x * star (heisO ψ S T w f₀ x)) := by
      funext x
      simp only [map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [e, integral_conj, h, map_zero]
  exact GlobalTheory.HeisTotal.eq_zero_abstract (G := WO S T) (ratL T S) K hK hcov ψ hψc hψn (symplOH S T) hl hr halt hcont hann
    f₀ q h₀.cont hq (GlobalTheory.HeisTotal.quasi_of_mem h₀) hq' hne μ 𝓕 hμ h𝓕 horth'

end GlobalTheory.ThetaOrthTotal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspFormMap_values_compact_sobolev_bound : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ Ω : Set (GA D V), IsCompact Ω → ∀ τ (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧ ∀ w : M.sm τ, ∀ g ∈ Ω, ‖T (Function.update v τ w) g‖ ≤ C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  first | exact @GlobalTheory.Core.Mi.sobolev_unif_bound | exact GlobalTheory.Core.Mi.sobolev_unif_bound | (intros; apply GlobalTheory.Core.Mi.sobolev_unif_bound <;> assumption)
end
