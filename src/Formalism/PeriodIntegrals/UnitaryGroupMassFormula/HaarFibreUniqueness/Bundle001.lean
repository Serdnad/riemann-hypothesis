module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.AdditiveCharacterNontrivial
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreExistence
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.UniqGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.OmFibreUniq.W.SdChar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain

theorem eq_one_of_pow_near (w : ℂ) (hw : ‖w‖ = 1) (h : ∀ m : ℕ, ‖w ^ m - 1‖ < 1) : w = 1 := by
  apply PI.OmFibreUniq.W.Sd.eq_one_of_pow_near <;> assumption

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
  (hψn : ∀ r, ‖ψ0 r‖ = 1)

include hψa hψn in
theorem psi_zero : ψ0 0 = 1 := by
  have h := hψa 0 0
  rw [add_zero] at h
  have hne : ψ0 0 ≠ 0 := by
    intro h0
    have := hψn 0
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h2 : ψ0 0 * (ψ0 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hne)


include hψa hψn in
theorem psi_natCast_mul (m : ℕ) (t : Fv F v) : ψ0 ((m : Fv F v) * t) = ψ0 t ^ m := by
  induction m with
  | zero => simp [psi_zero v ψ0 hψa hψn]
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul, hψa, ih, pow_succ]

def Aset : Set (Fv F v) := {t | ∀ c ∈ v.adicCompletionIntegers F, ψ0 (c * t) = 1}

include hψc hψa hψn in
theorem Aset_mem_nhds : Aset v ψ0 ∈ 𝓝 (0 : Fv F v) := by
  have h0 : ψ0 0 = 1 := psi_zero v ψ0 hψa hψn
  have hU : {x | ‖ψ0 x - 1‖ < 1} ∈ 𝓝 (0 : Fv F v) := by
    apply (isOpen_lt (hψc.sub continuous_const).norm continuous_const).mem_nhds
    simp [h0]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  apply Filter.mem_of_superset (Valued.mem_nhds_zero.mpr ⟨γ, subset_rfl⟩)
  intro t ht c hc
  have hin : ∀ c' ∈ v.adicCompletionIntegers F, ‖ψ0 (c' * t) - 1‖ < 1 := by
    intro c' hc'
    apply hγ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valuation.restrict_le_one_iff] at hc'
    simp only [Set.mem_setOf_eq, map_mul]
    calc Valued.v.restrict c' * Valued.v.restrict t ≤ 1 * Valued.v.restrict t := by gcongr
      _ = Valued.v.restrict t := one_mul _
      _ < _ := ht
  apply eq_one_of_pow_near _ (hψn _)
  intro m
  rw [← psi_natCast_mul v ψ0 hψa hψn, ← mul_assoc]
  exact hin _ (mul_mem (natCast_mem _ m) hc)

include hψa hψn in
theorem Aset_bdd (hnt : ∃ y, ψ0 y ≠ 1) :
    ∃ y0 : Fv F v, y0 ≠ 0 ∧ ∀ t ∈ Aset v ψ0, ∃ s ∈ v.adicCompletionIntegers F, t = y0 * s := by
  obtain ⟨y, hy⟩ := hnt
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (psi_zero v ψ0 hψa hψn)
  refine ⟨y, hy0, fun t ht => ⟨t / y, ?_, by field_simp⟩⟩
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  by_cases ht0 : t = 0
  · simp [ht0]
  rcases le_total (Valued.v (t / y)) 1 with hle | hge
  · exact hle
  · exfalso
    apply hy
    have hne : Valued.v (t / y) ≠ 0 := (Valuation.ne_zero_iff _).2 (div_ne_zero ht0 hy0)
    have hc : y / t ∈ v.adicCompletionIntegers F := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← inv_div, map_inv₀]
      calc (Valued.v (t / y))⁻¹ = (Valued.v (t / y))⁻¹ * 1 := (mul_one _).symm
        _ ≤ (Valued.v (t / y))⁻¹ * Valued.v (t / y) := by gcongr
        _ = 1 := inv_mul_cancel₀ hne
    have := (show ∀ c ∈ v.adicCompletionIntegers F, ψ0 (c * t) = 1 from ht) _ hc
    rwa [div_mul_cancel₀ _ ht0] at this

end PI.OmFibreUniq.W.SdChar
end
end

section

noncomputable section

namespace PI.OmFibreUniq.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology
open PI.OmFibreUniq PI.VolStabSW PI.VolStabSW.TensAllW
open scoped TensorProduct

theorem td_of_inj {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    [TotallyDisconnectedSpace α] (e : β → α) (he : Continuous e) (hi : Function.Injective e) :
    TotallyDisconnectedSpace β :=
  ⟨fun t _ ht x hx y hy =>
    hi ((isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (ht.image e he.continuousOn)) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

theorem gram_map_fibre_uniqueness : FibUniq := by
  intro F E _ _ _ _ _ σ n J v a μ ν hν fib fib' h h'
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨ι, _, ⟨e⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
  have : TotallyDisconnectedSpace (Fv F v ⊗[F] E) := td_of_inj e e.continuous e.injective
  have : LocallyCompactSpace (Fv F v ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  have : T2Space (Fv F v ⊗[F] E) := e.isEmbedding.t2Space
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  have := hν
  have hfree : IsOpen (IndepV (E := E) (n := n) v a) :=
    isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)
      (a := a) (M := n)
  have hA : ∀ S : Set (HermR (Fv F v) σ a), MeasurableSet S →
      MeasurableSet (gramR (Fv F v) σ J ⁻¹' (Subtype.val '' S)) := by
    intro S hS
    letI : MeasurableSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := borel _
    haveI : BorelSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := ⟨rfl⟩
    have hcl : IsClosedEmbedding
        (Subtype.val : HermR (Fv F v) σ a → Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal
    have hemb : MeasurableEmbedding
        (Subtype.val : HermR (Fv F v) σ a → Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      hcl.measurableEmbedding
    exact (hemb.measurableSet_image.2 hS).preimage (continuous_gramR (Fv F v) σ J).measurable
  exact fib_unique μ ν (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a) hA
    Subtype.val_injective hfree fib fib' h h'

theorem omUnique_of_sdEx (h0 : SdEx) {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ) : OmUnique σ J ψ v a :=
  omUnique_of σ J ψ v a h0 gram_map_fibre_existence gram_map_fibre_uniqueness

end PI.OmFibreUniq.W
end
end
