module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle056
import Formalism.LocalRingCardinality.DataHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import GroundTheory.GlobalFields.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightWordLaplacianPowerBound
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem latN_isOpen_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M N : ℕ), 0 < N →
    IsOpen (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ∧
    IsCompact (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ _ d b n M N hN
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  obtain ⟨u, hu⟩ : IsUnit (N : Af F) := by
    have h1 : IsUnit (algebraMap F (Af F) (N : F)) := (IsUnit.mk0 _ hNF).map _
    rwa [map_natCast] at h1
  have hSo : IsOpen {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have hpre : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun y => (↑u⁻¹ : Af F) * y) ⁻¹' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show (↑u⁻¹ : Af F) * ((N : Af F) * z) ∈ Oh F
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
        exact hz
      · intro hy
        exact ⟨(↑u⁻¹ : Af F) * y, hy, by rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [hpre]
    exact (AfTop.isOpen_Oh F).preimage (continuous_const_mul _)
  have hSc : IsCompact {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have himg : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun z => (N : Af F) * z) '' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [himg]
    exact (AfTop.isCompact_Oh F).image (continuous_const_mul _)
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let Bs := Algebra.TensorProduct.basis (Af F) b
  let e : (Af F ⊗[F] E) ≃ₜ (Fin d → Af F) :=
    { Bs.equivFun.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.symm.toLinearMap }
  have hT : {x : Af F ⊗[F] E | InNOh b N x} =
      e ⁻¹' Set.univ.pi (fun _ => {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z}) := by
    ext x
    rw [Set.mem_preimage, Set.mem_univ_pi]
    exact Iff.rfl
  have hlat : (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => {x : Af F ⊗[F] E | InNOh b N x})) := by
    ext X
    simp only [Set.mem_univ_pi]
    exact Iff.rfl
  have hTo : IsOpen {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => hSo).preimage e.continuous
  have hTc : IsCompact {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact e.isCompact_preimage.mpr (isCompact_univ_pi fun _ => hSc)
  rw [hlat]
  exact ⟨isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hTo,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hTc⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem exists_cube_subset_of_mem_nhds_zero {ι X : Type*} [Finite ι] [TopologicalSpace X] [Zero X]
    {V : Set (ι → X)} (hV : V ∈ nhds (0 : ι → X)) :
    ∃ W ∈ nhds (0 : X), ∀ Y : ι → X, (∀ i, Y i ∈ W) → Y ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr (fun i => by simpa using ht i), fun Y hY => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hY i) i

theorem latN_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ),
    ∀ U ∈ nhds (0 : Fin n → Fin M → Af F ⊗[F] E), ∃ N : ℕ, 0 < N ∧
      (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ⊆ U := by
  intro F E _ _ _ _ _ σ _ d b n M U hU
  let bb := Algebra.TensorProduct.basis (Af F) b
  obtain ⟨W1, hW1, hW1U⟩ := exists_cube_subset_of_mem_nhds_zero hU
  obtain ⟨W, hW, hWW1⟩ := exists_cube_subset_of_mem_nhds_zero hW1
  have hcont : Continuous (fun c : Fin d → Af F => ∑ k, c k • bb k) :=
    continuous_finsetSum _ (fun k _ => (continuous_apply k).smul continuous_const)
  have hV : (fun c : Fin d → Af F => ∑ k, c k • bb k) ⁻¹' W ∈ nhds (0 : Fin d → Af F) := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hW
  obtain ⟨V0, hV0, hV0V⟩ := exists_cube_subset_of_mem_nhds_zero hV
  obtain ⟨-, -, -, -, -, -, -, hN, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨N, hNpos, hNV0⟩ := hN V0 hV0
  refine ⟨N, hNpos, fun X hX => hW1U X fun a => hWW1 (X a) fun i => ?_⟩
  have hXai : InNOh b N (X a i) :=
    (show ∀ (a : Fin n) (i : Fin M), InNOh b N (X a i) from hX) a i
  have hmem : (⇑(bb.repr (X a i))) ∈ (fun c : Fin d → Af F => ∑ k, c k • bb k) ⁻¹' W := by
    apply hV0V
    intro k
    obtain ⟨y, hy, hk⟩ := hXai k
    rw [hk]
    exact hNV0 y hy
  simp only [Set.mem_preimage] at hmem
  rwa [bb.sum_repr] at hmem

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem

theorem exists_nat_mul_mem (F : Type) [Field F] [NumberField F] (x : F) :
    ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 F, (r : F) = (m : F) * x :=
  _root_.UpperTheory.Reformulated.B.ExistsNatMulMem.exists_nat_mul_mem F x

theorem repr_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Af F) b).repr (inclR (Af F) x) k
      = algebraMap F (Af F) (b.repr x k) := by
  have h : inclR (Af F) x = (1 : Af F) ⊗ₜ[F] x := rfl
  rw [h, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem natCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℕ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_natCast]

theorem intCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℤ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_intCast]

theorem exists_clear_family {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) {ι : Type} [Fintype ι] (e : ι → E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (t : ι) (o : 𝓞 E) (k : Fin d),
      ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (o : E))) k := by
  classical
  let B := RingOfIntegers.basis E
  choose m hm hr using fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d =>
    exists_nat_mul_mem F (b.repr (e p.1 * (B p.2.1 : E)) p.2.2)
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun t o k => ?_⟩
  set D : ℕ := ∏ p, m p with hDdef
  have hterm : ∀ l, ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (B l : E))) k := by
    intro l
    obtain ⟨c, hc⟩ : m (t, l, k) ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨r, hr1⟩ := hr (t, l, k)
    refine ⟨(c : 𝓞 F) * r, ?_⟩
    rw [natCast_mul_eq_smul (F := F), map_smul, Finsupp.smul_apply, smul_eq_mul, hc]
    simp only [map_mul, map_natCast, Nat.cast_mul]
    have hr2 : (r : F) = (m (t, l, k) : F) * b.repr (e t * (B l : E)) k := hr1
    change (c : F) * (r : F) = _
    rw [hr2]
    ring
  choose r hr' using hterm
  refine ⟨∑ l, (B.repr o l) • r l, ?_⟩
  have ho : (o : E) = ∑ l, ((B.repr o l : ℤ) : E) * (B l : E) := by
    have h3 := congrArg (algebraMap (𝓞 E) E) (B.sum_repr o)

    rw [map_sum] at h3
    rw [show (o : E) = algebraMap (𝓞 E) E o from rfl, ← h3]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  have hsum : (D : E) * (e t * (o : E))
      = ∑ l, ((B.repr o l : ℤ) : F) • ((D : E) * (e t * (B l : E))) := by
    rw [ho, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← intCast_mul_eq_smul]
    ring

  rw [hsum, map_sum, Finsupp.finsetSum_apply]
  have h4 : ((∑ l, (B.repr o l) • r l : 𝓞 F) : F) = ∑ l, ((B.repr o l : ℤ) : F) * (r l : F) := by

    rw [show ((∑ l, (B.repr o l) • r l : 𝓞 F) : F)
    = algebraMap (𝓞 F) F (∑ l, (B.repr o l) • r l) from rfl, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  rw [h4]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hr']

theorem ratTuple_mem_latN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n N : ℕ), 0 < N →
    ∃ s : ℕ, 0 < s ∧ ∀ ρ : Fin M → Fin n → 𝓞 E, ratTuple J s ρ ∈ latN b n M N := by
  intro F E _ _ _ _ _ d b M J n N hN
  obtain ⟨D, hD0, hD⟩ := exists_clear_family b (fun p : Fin M × Fin M => J⁻¹ p.1 p.2)
  refine ⟨N * D, Nat.mul_pos hN hD0, fun ρ => ?_⟩
  show ∀ a i, InNOh b N (ratTuple J (N * D) ρ a i)
  intro a j k
  choose r hr using fun i => hD (j, i) (ρ i a) k
  refine ⟨algebraMap F (Af F) (((∑ i, r i : 𝓞 F)) : F), ?_, ?_⟩
  · exact ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).2 ⟨_, rfl⟩
  · show (Algebra.TensorProduct.basis (Af F) b).repr
      (inclR (Af F) (((N * D : ℕ) : E) *
        (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j)) k = _
    rw [repr_inclR]
    have h1 : ((N * D : ℕ) : E) * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j
        = (N : F) • ∑ i, (D : E) * (J⁻¹ j i * (ρ i a : E)) := by
      rw [← natCast_mul_eq_smul, Nat.cast_mul, Matrix.mulVec, dotProduct, ← Finset.mul_sum,
        mul_assoc]

    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.finsetSum_apply,
    map_mul, map_natCast]
    congr 2

    rw [show ((∑ i, r i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∑ i, r i) from rfl, map_sum]
    exact Finset.sum_congr rfl fun i _ => (hr i).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_hypOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    IsHermND σ (hypOne J) := by
  refine ⟨fun i j => ?_, fun h => ?_⟩
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => change σ 0 = 0; simp
      | succ j =>
        induction j using Fin.cases with
        | zero => change σ 1 = 1; simp
        | succ j => change σ 0 = 0; simp
    | succ i =>
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => change σ 1 = 1; simp
        | succ j =>
          induction j using Fin.cases with
          | zero => change σ 0 = 0; simp
          | succ j => change σ 0 = 0; simp
      | succ i =>
        induction j using Fin.cases with
        | zero => change σ 0 = 0; simp
        | succ j =>
          induction j using Fin.cases with
          | zero => change σ 0 = 0; simp
          | succ j => exact hJ.1 i j
  · obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have hrow : ∀ i, ∑ j, hypOne J i j * v j = 0 := fun i => congrFun hv0 i
    have h1 : v 1 = 0 := by
      have := hrow 0
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [hypOne_zero_rest, hypOne_zero_zero, hypOne_zero_one] using this
    have h0 : v 0 = 0 := by
      have := hrow 1
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [hypOne_one_rest, hypOne_one_zero, hypOne_one_one] using this
    have ht : J.mulVec (fun j : Fin M => v j.succ.succ) = 0 := by
      funext i
      have := hrow i.succ.succ
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [Matrix.mulVec, dotProduct, hypOne_rest_rest, hypOne_rest_zero, hypOne_rest_one] using this
    have hz : (fun j : Fin M => v j.succ.succ) = 0 := by
      by_contra hne
      exact hJ.2 (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hne, ht⟩)
    apply hv
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i =>
      induction i using Fin.cases with
      | zero => exact h1
      | succ i => exact congrFun hz i

end Alg

theorem measurableSet_primV (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet (primV σ J b v) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  obtain ⟨-, -, -, t2, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := t2
  obtain ⟨-, lc, sc, -, -, hact⟩ := GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ (M + 2) (hypOne J)
    (isHermND_hypOne σ J hJ) (Fv F v)
  haveI := lc
  haveI := sc
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hσ 1 (M + 2) v
  have hc := (hact 1).1
  have hlat := (GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 (M + 2)).2.2.2.1 v
  have hclopen : IsClopen (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    ⟨hlat.1.isClosed, hlat.2⟩
  have hcl : IsClosed {g : HA (Fv F v) σ (hypOne J) | latStab σ (hypOne J) b v g} := by
    have hE : {g : HA (Fv F v) σ (hypOne J) | latStab σ (hypOne J) b v g} =
        ⋂ x : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E,
          {g | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} := by
      ext g
      simp [latStab]
    rw [hE]
    refine isClosed_iInter fun x => ?_
    have hcx : Continuous fun g : HA (Fv F v) σ (hypOne J) => actW (Fv F v) σ (hypOne J) g x :=
      hc.comp (continuous_id.prodMk continuous_const)
    have hp := hclopen.preimage hcx
    by_cases hx : x ∈ (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E))
    · have hs : {g : HA (Fv F v) σ (hypOne J) | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} =
          (fun g => actW (Fv F v) σ (hypOne J) g x) ⁻¹' latV b v := by
        ext g
        simp [hx]
      rw [hs]
      exact hp.1
    · have hs : {g : HA (Fv F v) σ (hypOne J) | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} =
          ((fun g => actW (Fv F v) σ (hypOne J) g x) ⁻¹' latV b v)ᶜ := by
        ext g
        simp [hx]
      rw [hs]
      exact hp.compl.1
  have hcont : Continuous fun g : HA (Fv F v) σ (hypOne J) => actW (Fv F v) σ (hypOne J) g (e0 _ M) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have him : IsSigmaCompact (primV σ J b v) := by
    exact (isSigmaCompact_univ.of_isClosed_subset hcl (Set.subset_univ _)).image hcont
  obtain ⟨K, hK, hU⟩ := him
  rw [← hU]
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

theorem measurable_purePr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → Measurable (purePr σ J b S Ψinf Ψ) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b S Ψinf Ψ hΨinf hΨ
  obtain ⟨hpi, hpf, hpv, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 (M + 2)
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_af F E σ hσ 1 (M + 2)
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_ainf F E σ hσ 1 (M + 2)
  haveI : ∀ v, BorelSpace (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
    fun v => GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hσ 1 (M + 2) v
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hset : MeasurableSet {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
      ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} := by
    have hE : {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
        ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} =
        ⋂ v, ⋂ _ : v ∉ S, (fun y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E => projV v (projFin y)) ⁻¹'
          primV σ J b v := by
      ext y
      simp
    rw [hE]
    refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
    exact ((hpv v).comp hpf).measurable (measurableSet_primV F E σ hσ M J hJ d b v)
  unfold purePr
  refine Measurable.indicator ?_ hset
  refine (hΨinf.comp hpi.measurable).mul ?_
  refine Finset.measurable_prod _ fun v _ => ?_
  exact (hΨ v).comp ((hpv v).comp hpf).measurable

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.right_word_laplacian_power_bound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    LgFacts → Unimod → RCalc → AlgEst → ClsFacts → IbpSob →
    ∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ f : Mat n → V, Sob μ f →
      ‖cls μ (Rw w f)‖ ≤ C * ∑ j ∈ range (w.length + 1), ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ := by
  first | exact @GlobalTheory.CompanionTheory.FcSmooth.WordBd.word_bound | exact GlobalTheory.CompanionTheory.FcSmooth.WordBd.word_bound | (intros; apply GlobalTheory.CompanionTheory.FcSmooth.WordBd.word_bound <;> assumption)
end
