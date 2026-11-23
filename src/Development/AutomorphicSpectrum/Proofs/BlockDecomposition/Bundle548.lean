module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.VeryCuspZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle423
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle398
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle525
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle424
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle399
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle526
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundarySquareLeviReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeNoSecondWeights
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDecompositionLevi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemCone
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveRestrictionOfBdsqVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealKTypesInCone
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanishingKernelLeviReal
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.SqIntFD

theorem sqIntAt : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.SqIntAt := by
  intro E _ _ _ N mG bG μ _ 𝓕 h𝓕 φ h h'
  obtain rfl : mG = borel _ := bG.measurable_eq
  have hm := GlobalTheory.CuspRep.CuspidalL2GL.memL2_of_isAutForm (μ := μ) h h'
  have hc := ((memL2_iff_fundamental_domain h𝓕).1 hm).2
  simpa using lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
    two_ne_zero ENNReal.ofNat_ne_top hc.eLpNorm_lt_top

end GlobalTheory.CompanionTheory.SqIntFD
end
end

section

noncomputable section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E
open scoped ENNReal Pointwise
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace GlobalTheory.CompanionTheory.Growth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem size_facts (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (∀ C : Set (GA E n), IsCompact C → ∃ r, ∀ g ∈ C, logSize g ≤ r) ∧ (∀ g : GA E n, 0 ≤ logSize g) ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∀ g h : GA E n, logSize (g * h) ≤ logSize g + logSize h + c := by
  obtain ⟨h1, h2, -, c, hc⟩ := GlobalTheory.CompanionTheory.Size.sizeBasic GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin
    GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces E n
  exact ⟨h1, h2, max c 0, le_max_right _ _, fun g h =>
    (hc g h).trans (add_le_add le_rfl (le_max_left _ _))⟩

end GlobalTheory.CompanionTheory.Growth
end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.EigTorus

theorem eigU_complete :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ y : V, y ∉ jacU ρ →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ) →
    ∃ (y' : V) (ξ : GU σ n → ℂ), y' ∉ jacU ρ ∧ (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y' - ξ t • y' ∈ jacU ρ) ∧
      ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1 :=
  eigU_of GlobalTheory.T.iwahori_unipotent_datum GlobalTheory.T.dominant_unipotent_contraction GlobalTheory.CompanionTheory.KUFactsU.kuFacts (fun G _ _ _ => GlobalTheory.T.jacquet_lemma_holds G)

end GlobalTheory.CompanionTheory.EigTorus
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.unitary_jacquet_nonzero : PositivityTheory.SphericalProduct.JacNeU := by
  first | exact @GlobalTheory.CompanionTheory.JacSph.jacNeU | exact GlobalTheory.CompanionTheory.JacSph.jacNeU | (intros; apply GlobalTheory.CompanionTheory.JacSph.jacNeU <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.boundary_square_levi_real : PositivityTheory.RgBcC.RealD.BdSqL := by
  first | exact @GlobalTheory.CompanionTheory.KPChains.bdSqL | exact GlobalTheory.CompanionTheory.KPChains.bdSqL | (intros; apply GlobalTheory.CompanionTheory.KPChains.bdSqL <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.real_first_nilpotent : PositivityTheory.RgBcC.RealD.N1 := by
  first | exact @GlobalTheory.CompanionTheory.HarmCone.harm_cone | exact GlobalTheory.CompanionTheory.HarmCone.harm_cone | (intros; apply GlobalTheory.CompanionTheory.HarmCone.harm_cone <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.cone_no_second_weights : PositivityTheory.RgBcC.RealD.ConeWeightsNotSecondType := by
  first | exact @GlobalTheory.CompanionTheory.ConeSecondWeights.cone_weight_not_in_second | exact GlobalTheory.CompanionTheory.ConeSecondWeights.cone_weight_not_in_second | (intros; apply GlobalTheory.CompanionTheory.ConeSecondWeights.cone_weight_not_in_second <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.harish_chandra_decomposition_levi : PositivityTheory.RgBcC.RealD.HCdecLv := by
  first | exact @GlobalTheory.CompanionTheory.RealHCLv.hcdecLv | exact GlobalTheory.CompanionTheory.RealHCLv.hcdecLv | (intros; apply GlobalTheory.CompanionTheory.RealHCLv.hcdecLv <;> assumption)
end

section

open PositivityTheory.RgBcC.RealD (inCone)

theorem GlobalTheory.T.highest_weight_mem_cone :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (K : Fin n → Fin n → Module.End ℂ V),
      Formalism.REAL.GlRel K → ∀ lev : Fin n → ℕ, Monotone lev →
      ∀ (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ) (x : V),
        Formalism.REAL.KHighest (fun _ => true) K ν x →
        (∀ a b v, lev a = lev b → a ≠ b → ev (K a b v) = 0) →
        (∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) →
        (∃ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ev (T x) ≠ 0) →
        inCone lev (ν - μ) :=
  GlobalTheory.CompanionTheory.HighestCone.inCone_of_highest
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.injective_restriction_of_bdsq_vanish : PositivityTheory.RgBcC.RealD.BdSqL → PositivityTheory.RgBcC.RealD.VanKL → PositivityTheory.RgBcC.RealD.InjRL := by
  first | exact @GlobalTheory.CompanionTheory.InjRL.injRL_of | exact GlobalTheory.CompanionTheory.InjRL.injRL_of | (intros; apply GlobalTheory.CompanionTheory.InjRL.injRL_of <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.real_k_types_in_cone : PositivityTheory.RgBcC.RealD.KTypeGenerationHighest := by
  first | exact @GlobalTheory.CompanionTheory.KTypeCone.k_types_in_weight_cone | exact GlobalTheory.CompanionTheory.KTypeCone.k_types_in_weight_cone | (intros; apply GlobalTheory.CompanionTheory.KTypeCone.k_types_in_weight_cone <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.vanishing_kernel_levi_real : PositivityTheory.RgBcC.RealD.VanKL := by
  first | exact @GlobalTheory.CompanionTheory.KostL.vanKL | exact GlobalTheory.CompanionTheory.KostL.vanKL | (intros; apply GlobalTheory.CompanionTheory.KostL.vanKL <;> assumption)
end
