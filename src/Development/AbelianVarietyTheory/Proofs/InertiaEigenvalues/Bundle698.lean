module

public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle677
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNeZeroOfSameTransform
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle675
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle678
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle679
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLocalDualityOfLocalTateDuality
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_satU_eigenvector_alt : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  first | exact @GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector | exact GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector | (intros; apply GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.satakeParameter_ne_zero_of_sameTransform : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (α : Fin (n / 2) → ℂ) (β : Fin (n / 2) → ℂˣ), (∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h (fun i => (β i : ℂ))) → ∀ i, α i ≠ 0 := by
  first | exact @GlobalTheory.SatNonzero.satU_ne_zero | exact GlobalTheory.SatNonzero.satU_ne_zero | (intros; apply GlobalTheory.SatNonzero.satU_ne_zero <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachLatticeTrivialModUniformizer



theorem wachLattice_galois_trivial_mod_uniformizer : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P2 D HW F := by
  intro D HW F Cm l _ K s LL h T hT
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.NL.GamModX.gam_mod_π_mod_X D HW F Cm l K s LL h T hT
  refine ⟨(wach_gamma_stable_first _ T).1, (wach_gamma_stable_first _ T).2, fun x hx => ?_⟩
  obtain ⟨y, hy, e⟩ := h3 x hx
  exact ⟨y, hy, e.symm⟩

end GlobalTheory.NL.WachLatticeTrivialModUniformizer
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), P7 D HW F := by
  first | exact @GlobalTheory.NL.PoleCrys.main | exact GlobalTheory.NL.PoleCrys.main | (intros; apply GlobalTheory.NL.PoleCrys.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isDeRham_of_isSemistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.sst_isDR | exact GlobalTheory.sst_isDR | (intros; apply GlobalTheory.sst_isDR <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.firstCharacter_trivial_wildInertia_typePrime : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1 := by
  first | exact @GlobalTheory.ChiTame.main | exact GlobalTheory.ChiTame.main | (intros; apply GlobalTheory.ChiTame.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.ramifiedCoefficientChains_adm11 : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm11 D := by
  first | exact @GlobalTheory.Per.DcrisExact.fontaine_dcris | exact GlobalTheory.Per.DcrisExact.fontaine_dcris | (intros; apply GlobalTheory.Per.DcrisExact.fontaine_dcris <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.exists_decompositionGroup_equiv_padicGalois : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∃ i : ↥(A.decompositionSubgroup F) ≃ₜ*
      (PadicAlgCl p ≃ₐ[↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)))] PadicAlgCl p),
      ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x) := by
  first | exact @GlobalTheory.DecGalois.exists_continuousMulEquiv | exact GlobalTheory.DecGalois.exists_continuousMulEquiv | (intros; apply GlobalTheory.DecGalois.exists_continuousMulEquiv <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.coeff_coeff_pow_eq_of_coeff_coeff_eq_le : ∀ (R : Type) [CommRing R] (m i n : ℕ) (G H : R⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (G ^ m)) = coeff n (coeff i (H ^ m)) := by
  first | exact @GlobalTheory.coeff_coeff_pow_eq_of_box | exact GlobalTheory.coeff_coeff_pow_eq_of_box | (intros; apply GlobalTheory.coeff_coeff_pow_eq_of_box <;> assumption)
end

section


theorem _root_.GlobalTheory.T.rationalLocalDuality_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.RatIso := by
  first | exact @GlobalTheory.ratIso_of_localTateDuality | exact GlobalTheory.ratIso_of_localTateDuality | (intros; apply GlobalTheory.ratIso_of_localTateDuality <;> assumption)
end
