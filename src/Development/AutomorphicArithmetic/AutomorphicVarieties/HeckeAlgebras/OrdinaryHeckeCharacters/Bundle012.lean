module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.levelUR2EigPart :
    ∀ (K W ι : Type) [Field K] [AddCommGroup W] [Module K W] (J : Type 1) (op : ι → Module.End K W) (Z : J → Submodule K W) (μ : J → ι → K), (∀ j i, ∀ F ∈ Z j, op i F = μ j i • F) → ∀ F ∈ ⨆ j, Z j, F ≠ 0 → ∀ ν : ι → K, (∀ i, op i F = ν i • F) → ∃ j, μ j = ν := by
  intro K W ι _ _ _ J op Z μ hZ F hF hF0 ν hν
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hF
  have inv : ∀ (t : Finset J) i, ∀ G ∈ ⨆ j ∈ t, Z j, op i G ∈ ⨆ j ∈ t, Z j := by
    intro t i
    have hle : (⨆ j ∈ t, Z j) ≤ (⨆ j ∈ t, Z j).comap (op i) := by
      refine iSup₂_le fun j hj => ?_
      intro G hG
      rw [Submodule.mem_comap, hZ j i G hG]
      exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun j (_ : j ∈ t) => Z j) j hj) hG)
    exact fun G hG => hle hG
  suffices key : ∀ t : Finset J, ∀ G ∈ ⨆ j ∈ t, Z j, G ≠ 0 → (∀ i, op i G = ν i • G) → ∃ j, μ j = ν from
    key s F hs hF0 hν
  intro t
  refine Finset.induction_on t ?_ ?_
  · intro G hG hG0 _
    simp at hG
    exact absurd hG hG0
  · intro a t ha ih G hG hG0 hGν
    rw [Finset.iSup_insert, Submodule.mem_sup] at hG
    obtain ⟨H, hH, G', hG', rfl⟩ := hG
    by_cases hμ : μ a = ν
    · exact ⟨a, hμ⟩
    obtain ⟨i, hi⟩ : ∃ i, μ a i ≠ ν i := by
      by_contra h
      push_neg at h
      exact hμ (funext h)
    have e : (μ a i - ν i) • H = ν i • G' - op i G' := by
      have h1 := hGν i
      rw [map_add (f := _), hZ a i H hH, smul_add] at h1
      rw [sub_smul, sub_eq_sub_iff_add_eq_add, h1, add_comm]
    have hsub : (μ a i - ν i) • H ∈ ⨆ j ∈ t, Z j := by
      rw [e]
      exact sub_mem (Submodule.smul_mem _ _ hG') (inv t i G' hG')
    have hH' : H ∈ ⨆ j ∈ t, Z j := by
      have hne : μ a i - ν i ≠ 0 := sub_ne_zero.mpr hi
      have h2 := Submodule.smul_mem _ (μ a i - ν i)⁻¹ hsub
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    exact ih (H + G') (add_mem hH' hG') hG0 hGν
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.levelUR2Glue :
    ∀ (A R P κ : Type) [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Nonempty κ] (N : κ → Submodule A P) (μ : ∀ k, R →+* Module.End A (N k)), (∀ z, ∃ k, z ∈ N k) → (∀ k k', ∃ k'', N k ≤ N k'' ∧ N k' ≤ N k'') → (∀ k k' (h : N k ≤ N k') t (y : N k), ((μ k' t (Submodule.inclusion h y) : N k') : P) = (μ k t y : N k)) → ∃ α : R →+* Module.End A P, ∀ k t (y : N k), α t y = (μ k t y : N k) := by
  intro A R P κ _ _ _ _ _ N μ hcov hdir hcomp
  have key : ∀ t (z : P) k k' (hk : z ∈ N k) (hk' : z ∈ N k'),
      ((μ k t ⟨z, hk⟩ : N k) : P) = ((μ k' t ⟨z, hk'⟩ : N k') : P) := by
    intro t z k k' hk hk'
    obtain ⟨k'', h1, h2⟩ := hdir k k'
    have e1 := hcomp k k'' h1 t ⟨z, hk⟩
    have e2 := hcomp k' k'' h2 t ⟨z, hk'⟩
    have e3 : Submodule.inclusion h1 ⟨z, hk⟩ = Submodule.inclusion h2 ⟨z, hk'⟩ := Subtype.ext rfl
    rw [← e1, ← e2, e3]
  let f : R → P → P := fun t z => ((μ (hcov z).choose t ⟨z, (hcov z).choose_spec⟩ : N _) : P)
  have hf : ∀ t k (y : N k), f t y = ((μ k t y : N k) : P) := fun t k y => key t y _ k _ y.2
  have two : ∀ z w : P, ∃ k, z ∈ N k ∧ w ∈ N k := by
    intro z w
    obtain ⟨k1, h1⟩ := hcov z
    obtain ⟨k2, h2⟩ := hcov w
    obtain ⟨k, hk1, hk2⟩ := hdir k1 k2
    exact ⟨k, hk1 h1, hk2 h2⟩
  let L : R → Module.End A P := fun t =>
    { toFun := f t
      map_add' := by
        intro z w
        obtain ⟨k, hz, hw⟩ := two z w
        calc f t (z + w) = f t ((⟨z, hz⟩ + ⟨w, hw⟩ : N k) : P) := rfl
          _ = ((μ k t (⟨z, hz⟩ + ⟨w, hw⟩) : N k) : P) := hf t k _
          _ = ((μ k t ⟨z, hz⟩ : N k) : P) + ((μ k t ⟨w, hw⟩ : N k) : P) := by
            rw [map_add (f := _), Submodule.coe_add]
          _ = f t z + f t w := by rw [← hf t k ⟨z, hz⟩, ← hf t k ⟨w, hw⟩]
      map_smul' := by
        intro a z
        obtain ⟨k, hz⟩ := hcov z
        calc f t (a • z) = f t ((a • ⟨z, hz⟩ : N k) : P) := rfl
          _ = ((μ k t (a • ⟨z, hz⟩) : N k) : P) := hf t k _
          _ = a • ((μ k t ⟨z, hz⟩ : N k) : P) := by rw [map_smul, Submodule.coe_smul]
          _ = (RingHom.id A) a • f t z := by rw [RingHom.id_apply, ← hf t k ⟨z, hz⟩] }
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f 1 z = z
    exact (hf 1 k ⟨z, hz⟩).trans (by simp)
  · intro s t
    refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f (s * t) z = f s (f t z)
    calc f (s * t) z = ((μ k (s * t) ⟨z, hz⟩ : N k) : P) := hf _ k ⟨z, hz⟩
      _ = ((μ k s (μ k t ⟨z, hz⟩) : N k) : P) := by rw [map_mul]; rfl
      _ = f s ((μ k t ⟨z, hz⟩ : N k) : P) := (hf s k _).symm
      _ = f s (f t z) := congrArg (f s) (hf t k ⟨z, hz⟩).symm
  · refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f 0 z = 0
    exact (hf 0 k ⟨z, hz⟩).trans (by simp)
  · intro s t
    refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f (s + t) z = f s z + f t z
    calc f (s + t) z = ((μ k (s + t) ⟨z, hz⟩ : N k) : P) := hf _ k ⟨z, hz⟩
      _ = ((μ k s ⟨z, hz⟩ : N k) : P) + ((μ k t ⟨z, hz⟩ : N k) : P) := by
        rw [map_add (f := _), LinearMap.add_apply, Submodule.coe_add]
      _ = f s z + f t z := by rw [← hf s k ⟨z, hz⟩, ← hf t k ⟨z, hz⟩]
  · intro k t y
    exact hf t k y
end
