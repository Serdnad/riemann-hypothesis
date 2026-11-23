module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open _root_.Topology

theorem exists_den {F : Type} [Field F] [NumberField F] (y : F) :
    ∃ D : ℕ, 0 < D ∧ ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y := by
  have hal : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨z, hz, hint⟩ := hal.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_⟩
  have hint' : IsIntegral ℤ ((z.natAbs : F) * y) := by
    rcases Int.natAbs_eq z with h | h
    · have : ((z.natAbs : F) * y) = z • y := by
        rw [zsmul_eq_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rwa [this]
    · have : ((z.natAbs : F) * y) = -(z • y) := by
        rw [zsmul_eq_mul, ← neg_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rw [this]
      exact hint.neg
  exact ⟨IsIntegralClosure.mk' (𝓞 F) _ hint', IsIntegralClosure.algebraMap_mk' _ _ _⟩

theorem exists_common_den {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (y : ι → F) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y i := by
  choose D hD r hr using fun i => exists_den (y i)
  refine ⟨∏ i, D i, Finset.prod_pos fun i _ => hD i, fun i => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  refine ⟨(m : 𝓞 F) * r i, ?_⟩
  rw [hm, map_mul, hr, map_natCast]
  push_cast
  ring

theorem coords_den {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (o : 𝓞 E) (k : Fin d), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = (D : F) * b.repr (algebraMap (𝓞 E) E o) k := by
  let e := RingOfIntegers.basis E
  obtain ⟨D, hD, h⟩ := exists_common_den (F := F)
    (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d => b.repr (algebraMap (𝓞 E) E (e p.1)) p.2)
  refine ⟨D, hD, fun o k => ?_⟩
  choose r hr using h
  refine ⟨∑ i, (e.repr o i) • r (i, k), ?_⟩
  have ho : algebraMap (𝓞 E) E o = ∑ i, (e.repr o i) • algebraMap (𝓞 E) E (e i) := by
    conv_lhs => rw [← e.sum_repr o]

    simp [map_sum]

  rw [ho, map_sum, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, Finsupp.smul_apply, hr (i, k)]
  simp only [zsmul_eq_mul]
  ring

theorem nhds_unif {ι Y : Type} [Finite ι] [TopologicalSpace Y] (y0 : Y) (W : Set (ι → Y))
    (hW : W ∈ 𝓝 (fun _ => y0)) : ∃ V ∈ 𝓝 y0, ∀ y : ι → Y, (∀ i, y i ∈ V) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr ht, fun y hy => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hy i) i

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open _root_.Topology

theorem exists_smul_mem_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  intro F E _ _ _ _ _ σ hcm n U hU t ht
  obtain ⟨-, hSC, hT2, -, -, -, hF, hN, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : SecondCountableTopology (Af F) := hSC
  haveI : T2Space (Af F) := hT2
  haveI : LocallyCompactSpace (Af F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).1
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Af F)
  let b := Module.finBasis F E
  have hh := hH _ b
  set h := hh.homeomorph with hdef
  have happ : ∀ (y : Af F ⊗[F] E) k, h y k = (Algebra.TensorProduct.basis (Af F) b).repr y k :=
    fun _ _ => rfl
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.mp hU
  let G : (Fin n × Fin n × Fin (Module.finrank F E) → Af F) →
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun x a c => h.symm (fun k => x (a, c, k))
  have hG : Continuous G := by
    refine continuous_matrix fun a c => ?_
    exact h.symm.continuous.comp (continuous_pi fun k => continuous_apply _)
  have hG0 : G (fun _ => 0) = 0 := by
    ext a c
    apply h.injective
    show h (h.symm _) = h 0
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    simp
  have h0 : (0 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ U' := by
    have h1 : (0 : HermR (Af F) σ n) ∈ (U : Set (HermR (Af F) σ n)) := U.zero_mem
    rw [← hU'] at h1
    exact h1
  have hW : G ⁻¹' U' ∈ 𝓝 (fun _ => (0 : Af F)) :=
    (hU'o.preimage hG).mem_nhds (by rw [Set.mem_preimage, hG0]; exact h0)
  obtain ⟨V, hV, hVW⟩ := nhds_unif _ _ hW
  obtain ⟨N, hNpos, hNV⟩ := hN V hV
  obtain ⟨D₁, hD₁, p, hp⟩ := exists_den (t⁻¹)
  obtain ⟨D₂, hD₂, hco⟩ := coords_den b
  refine ⟨D₁ * D₂ * N, by positivity, fun c hc => ?_⟩
  let y : Fin n × Fin n × Fin (Module.finrank F E) → Af F := fun q =>
    algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 q.1 q.2.1) q.2.2)
  have hy : ∀ q, y q ∈ V := by
    rintro ⟨a, a', k⟩
    obtain ⟨o, ho⟩ := hc a a'
    obtain ⟨r, hr⟩ := hco o k
    have hval : b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k
        = (N : F) * (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) := by
      have : (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a')
          = (((D₁ * D₂ * N : ℕ) : F) / t) • algebraMap (𝓞 E) E o := by
        rw [ho]; rfl
      rw [this, map_smul, Finsupp.smul_apply, hp, hr, smul_eq_mul, div_eq_mul_inv]
      push_cast
      ring
    have hmem : algebraMap F (Af F) (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) ∈
        GlobalTheory.CompanionTheory.SW.Core.Oh F := (hF _).mpr ⟨p * r, by simp⟩
    have := hNV _ hmem
    show algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k) ∈ V
    rw [hval, map_mul, map_natCast]
    exact this
  have hGy : G y ∈ U' := hVW y hy
  have heq : G y = (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 := by
    ext a a'
    apply h.injective
    show h (h.symm _) = _
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    show y (a, a', k) = _
    have hentry : (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 a a' =
        (1 : Af F) ⊗ₜ[F] (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') := rfl
    rw [hentry, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, one_smul, Finsupp.mapRange_apply]
    rfl
  have hfin : hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c) ∈ (U : Set (HermR (Af F) σ n)) := by
    rw [← hU']
    show _ ∈ U'
    rw [← heq]
    exact hGy
  exact hfin

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens
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

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle

theorem pair_single : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψf : Af F → ℂ) (c : hermE σ n) (c₀ : Fin n) (i₀ : Fin M) (x : Af F ⊗[F] E) (s : ℕ)
      (ρ : Fin M → Fin n → 𝓞 E),
    pairB σ J ψf (hermIn (Af F) σ n c) (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ) =
      ψf (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)))) := by
  intro F E _ _ _ _ _ σ M J hJ n ψf c c₀ i₀ x s ρ
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have key : ∀ a, hR (Af F) σ J (fun i => if i = i₀ then x else 0) (ratTuple J s ρ a) =
      sigR (Af F) σ x * inclR (Af F) ((s : E) * algebraMap (𝓞 E) E (ρ i₀ a)) := by
    intro a
    have hv : ∑ j, J i₀ j * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j
        = algebraMap (𝓞 E) E (ρ i₀ a) := by
      have h1 : (J *ᵥ (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a))) i₀ =
          algebraMap (𝓞 E) E (ρ i₀ a) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
      simpa [Matrix.mulVec, dotProduct] using h1
    unfold hR Formalism.UG.hform
    rw [Finset.sum_eq_single i₀]
    · simp only [if_true, JR, ratTuple, Matrix.map_apply]
      rw [← hv]

      simp only [map_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · intro i _ hi
      simp [hi]
    · simp
  have hz : ∀ (c' : Fin n) (a : Fin n), c' ≠ c₀ →
      hR (Af F) σ J (fun i => if c' = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ a) = 0 := by
    intro c' a hc
    simp [hR, Formalism.UG.hform, hc]
  have hin : ∀ a b, ((hermIn (Af F) σ n c : HermR (Af F) σ n) :
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) a b = inclR (Af F) (c.1 a b) := fun a b => rfl
  have htr : Matrix.trace (((hermIn (Af F) σ n c : HermR (Af F) σ n) :
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gram2 σ J (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ)) =
      sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hin, gram2]
    have h2 : ∀ a, ∑ c', inclR (Af F) (c.1 a c') *
        hR (Af F) σ J (fun i => if c' = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ a) =
        inclR (Af F) (c.1 a c₀) *
          (sigR (Af F) σ x * inclR (Af F) ((s : E) * algebraMap (𝓞 E) E (ρ i₀ a))) := by
      intro a
      rw [Finset.sum_eq_single c₀]
      · simp only [true_and]
        rw [key a]
      · intro c' _ hc
        rw [hz c' a hc, mul_zero]
      · simp
    simp only [h2]

    rw [Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_mul]
    ring
  unfold pairB
  rw [htr]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.ChartGram

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_halfR (σ : E →ₐ[F] E) : sigR R σ (halfR (F := F) (E := E) R) = halfR (F := F) (E := E) R := by
  unfold halfR
  rw [sigR_inclR, AlgHom.commutes]

theorem halfR_add_halfR (h2 : (2 : F) ≠ 0) :
    halfR (F := F) (E := E) R + halfR (F := F) (E := E) R = 1 := by
  have h : (1 / 2 : F) + 1 / 2 = 1 := by field_simp; norm_num
  unfold halfR
  rw [← map_add (f := _), ← map_add (f := _), h, map_one, map_one]

theorem vH_zero {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : vH a s Y 0 = a := rfl
theorem vH_one {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : vH a s Y 1 = s := rfl
theorem tailH_vH {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : tailH (vH a s Y) = Y := rfl

theorem hR_hypOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin (M + 2) → R ⊗[F] E) :
    hR R σ (hypOne J) x y =
      sigR R σ (x 0) * y 1 + sigR R σ (x 1) * y 0 + hR R σ J (tailH x) (tailH y) := by
  unfold hR hform JR tailH
  simp only [Fin.sum_univ_succ, Matrix.map_apply, Fin.succ_zero_eq_one, hypOne_zero_zero, hypOne_zero_one,
    hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one,
    hypOne_rest_rest, map_zero, map_one, mul_zero, zero_mul, mul_one, Finset.sum_const_zero, add_zero, zero_add]
  ring

theorem sigR_hR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  unfold hR hform JR

  simp only [map_sum, map_mul, sigR_sigR R σ hσ, Matrix.map_apply, sigR_inclR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem hR_comb_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : R ⊗[F] E)
    (x u w : Fin M → R ⊗[F] E) :
    hR R σ J x (fun i => c * u i + w i) = c * hR R σ J x u + hR R σ J x w := by
  unfold hR hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_comb_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : R ⊗[F] E)
    (u w y : Fin M → R ⊗[F] E) :
    hR R σ J (fun i => c * u i + w i) y = sigR R σ c * hR R σ J u y + hR R σ J w y := by
  unfold hR hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, map_add (f := _), map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sigR_tHalf (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin (M + 2) → R ⊗[F] E) :
    sigR R σ (tHalf R σ J x) = tHalf R σ J x := by
  unfold tHalf
  rw [map_mul, sigR_halfR, hR_hypOne, map_add (f := _), map_add (f := _), map_mul, map_mul, sigR_sigR R σ hσ, sigR_sigR R σ hσ,
    sigR_hR R σ hσ J hJ]
  ring

theorem hR_cvec_right (h2 : (2 : F) ≠ 0) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x v : Fin (M + 2) → R ⊗[F] E) (hu : IsUnit (x 0)) :
    hR R σ (hypOne J) x (cvec R σ J x v) = v 1 + tHalf R σ J x * v 0 := by
  have e1 : Ring.inverse (sigR R σ (x 0)) * sigR R σ (x 0) = 1 :=
    Ring.inverse_mul_cancel _ (hu.map (sigR R σ))
  have e3 : tHalf R σ J x + tHalf R σ J x = hR R σ (hypOne J) x x := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  have e4 := hR_hypOne R σ J x x
  have ht : tailH (cvec R σ J x v) = fun i => v 0 * tailH x i + tailH v i := rfl
  rw [hR_hypOne, ht, hR_comb_right]
  simp only [cvec, vH_zero, vH_one]
  linear_combination (v 1 - tHalf R σ J x * v 0 - hR R σ J (tailH x) (tailH v)) * e1 - v 0 * e3 - v 0 * e4

theorem hR_cvec_cvec (h2 : (2 : F) ≠ 0) (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (x v w : Fin (M + 2) → R ⊗[F] E) (hu : IsUnit (x 0)) :
    hR R σ (hypOne J) (cvec R σ J x v) (cvec R σ J x w) = hR R σ (hypOne J) v w := by
  have e1 : Ring.inverse (sigR R σ (x 0)) * sigR R σ (x 0) = 1 :=
    Ring.inverse_mul_cancel _ (hu.map (sigR R σ))
  have e2 : sigR R σ (Ring.inverse (sigR R σ (x 0))) * x 0 = 1 := by
    have := congrArg (sigR R σ) e1
    rwa [map_mul, sigR_sigR R σ hσ, map_one] at this
  have e3 : tHalf R σ J x + tHalf R σ J x = hR R σ (hypOne J) x x := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  have e4 := hR_hypOne R σ J x x
  have htv : tailH (cvec R σ J x v) = fun i => v 0 * tailH x i + tailH v i := rfl
  have htw : tailH (cvec R σ J x w) = fun i => w 0 * tailH x i + tailH w i := rfl
  rw [hR_hypOne, hR_hypOne R σ J v w, htv, htw, hR_comb_left, hR_comb_right, hR_comb_right]
  simp only [cvec, vH_zero, vH_one, map_add (f := _), map_sub, map_mul, sigR_tHalf R σ hσ J hJ,
    sigR_hR R σ hσ J hJ]
  linear_combination
    (sigR R σ (v 0) * (w 1 - tHalf R σ J x * w 0 - hR R σ J (tailH x) (tailH w))) * e1 +
    (w 0 * (sigR R σ (v 1) - tHalf R σ J x * sigR R σ (v 0) - hR R σ J (tailH v) (tailH x))) * e2 -
    sigR R σ (v 0) * w 0 * e3 - sigR R σ (v 0) * w 0 * e4

end Alg

theorem gramR_chartS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 0 = hR R σ (hypOne J) (x 0) (x 0) ∧ (∀ j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 j.succ = s 0 j) ∧ ∀ i j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) i.succ j.succ = gramR R σ J Y i j + (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j - hR R σ (hypOne J) (x 0) (x 0) * (sigR R σ (a 0 i) * a 0 j)) := by
  intro F E _ _ _ _ _ σ hc M J hJ R _ _ n x a s Y hu
  have hσ := sig_invol σ hc
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have e3 : tHalf R σ J (x 0) + tHalf R σ J (x 0) = hR R σ (hypOne J) (x 0) (x 0) := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  refine ⟨rfl, fun j => ?_, fun i j => ?_⟩
  · change hR R σ (hypOne J) (x 0) (cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))) = s 0 j
    rw [hR_cvec_right R h2 σ J _ _ hu, vH_zero, vH_one]
    ring
  · change hR R σ (hypOne J) (cvec R σ J (x 0) (vH (a 0 i) (s 0 i - tHalf R σ J (x 0) * a 0 i) (Y i)))
      (cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))) = hR R σ J (Y i) (Y j) + _
    rw [hR_cvec_cvec R h2 σ hσ J hJ.1 _ _ _ hu, hR_hypOne]
    simp only [vH_zero, vH_one, tailH_vH, map_sub, map_mul, sigR_tHalf R σ hσ J hJ.1]
    linear_combination (-(sigR R σ (a 0 i) * a 0 j)) * e3

end GlobalTheory.CompanionTheory.WeilSiegel.ChartGram
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.Orbit

theorem isUnder_of_sameOrbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder w z → SameOrbit z' z → IsUnder w z' := by
  rintro m n w z z' h ⟨c, hc, rfl⟩ k i
  refine ⟨(h k i).1.trans ?_, fun j hy => ((h k i).2 j hy).trans ?_⟩
  · show z ⟨k, i⟩ ≠ 0 ↔ c k * z ⟨k, i⟩ ≠ 0
    simp [hc k]
  · exact (mul_div_mul_left _ _ (hc k)).symm

end GlobalTheory.CompanionTheory.MixZ.Orbit
end
