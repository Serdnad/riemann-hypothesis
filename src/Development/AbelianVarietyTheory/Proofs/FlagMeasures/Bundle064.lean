module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Mathlib.MeasureTheory.Group.Defs
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Group.FundamentalDomain

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  intro V₁ V₂ _ _ Λ D₁ D₂ h1 h2 v
  obtain ⟨l₂, ⟨⟨s, hs⟩, hl₂D⟩, -⟩ := h2 v.2
  obtain ⟨l₁, ⟨hl₁, hl₁D⟩, -⟩ := h1 (v.1 + s)
  have hl₁' : ((l₁, 0) : V₁ × V₂) ∈ Λ := hl₁
  refine ⟨(s + l₁, l₂), ⟨?_, ?_⟩, ?_⟩
  · have e : ((s + l₁, l₂) : V₁ × V₂) = (s, l₂) + (l₁, 0) := by simp
    rw [e]; exact Λ.add_mem hs hl₁'
  · refine ⟨?_, ?_⟩
    · show v.1 + (s + l₁) ∈ D₁
      rw [← add_assoc]; exact hl₁D
    · exact hl₂D
  · rintro ⟨m₁, m₂⟩ ⟨hm, hmD⟩
    have hmD1 : v.1 + m₁ ∈ D₁ := hmD.1
    have hmD2 : v.2 + m₂ ∈ D₂ := hmD.2
    have e2 : m₂ = l₂ := (h2 v.2).unique ⟨⟨m₁, hm⟩, hmD2⟩ ⟨⟨s, hs⟩, hl₂D⟩
    subst e2
    have hx : ((m₁ - s, 0) : V₁ × V₂) ∈ Λ := by
      have := Λ.sub_mem hm hs
      simpa using this
    have e1 : m₁ - s = l₁ := (h1 (v.1 + s)).unique
      ⟨hx, by show v.1 + s + (m₁ - s) ∈ D₁; simpa using hmD1⟩ ⟨hl₁, hl₁D⟩
    have : m₁ = s + l₁ := by rw [← e1]; abel
    rw [this]

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem fractionalIdeal_basis_transport (K : Type) [Field K] [NumberField K] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W)
    (e : mixedEmbedding.mixedSpace K ≃L[ℝ] W) (he : MeasurePreserving e volume μ)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ W),
      (Submodule.span ℤ (Set.range b) : Set W) =
        (fun x : K => e (mixedEmbedding K x)) '' {x : K | x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)} ∧
      μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal (FractionalIdeal.absNorm
        (J : FractionalIdeal (𝓞 K)⁰ K) * (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(discr K : ℝ)|) := by
  set b₀ := mixedEmbedding.fractionalIdealLatticeBasis K J with hb₀
  refine ⟨_, inferInstance, b₀.map e.toLinearEquiv, ?_, ?_⟩
  · let f : mixedEmbedding.mixedSpace K →ₗ[ℤ] W := e.toLinearEquiv.toLinearMap.restrictScalars ℤ
    have hr : Set.range (b₀.map e.toLinearEquiv) = f '' Set.range b₀ := by
      rw [← Set.range_comp]; rfl
    have h0 : (Submodule.span ℤ (Set.range b₀) : Set (mixedEmbedding.mixedSpace K)) =
        mixedEmbedding K '' (J : Set K) := by
      ext x
      exact mixedEmbedding.mem_span_fractionalIdealLatticeBasis K J
    rw [hr, Submodule.span_image, Submodule.map_coe, h0, Set.image_image]
    rfl
  · have hfd : ZSpan.fundamentalDomain (b₀.map e.toLinearEquiv) =
        e '' ZSpan.fundamentalDomain b₀ := (ZSpan.map_fundamentalDomain b₀ e.toLinearEquiv).symm
    let E := e.toHomeomorph.toMeasurableEquiv
    have hE : MeasurePreserving E volume μ := he
    have h1 : μ (ZSpan.fundamentalDomain (b₀.map e.toLinearEquiv)) =
        volume (ZSpan.fundamentalDomain b₀) := by
      rw [← hE.measure_preimage_equiv, hfd]
      congr 1
      exact Set.preimage_image_eq _ e.injective
    rw [h1]
    have hfin : volume (ZSpan.fundamentalDomain b₀) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded b₀).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, ← mixedEmbedding.covolume_idealLattice K J,
      ZLattice.covolume_eq_measure_fundamentalDomain _ _
        (mixedEmbedding.fundamentalDomain_idealLattice K J), measureReal_def]

end GlobalTheory.SnMass.VolN
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem covolQuotient_real (d : ℝ) (f t : ℕ) (hd : 1 ≤ d) :
    ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2) =
      ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) *
        ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ))) := by
  have hd0 : 0 < d := by linarith
  have hd0' : d ≠ 0 := hd0.ne'
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd0.le

  have h1 : d ^ (1 / 2 - 2 * (t : ℝ)) = Real.sqrt d / d ^ (2 * t) := by
    rw [Real.rpow_sub hd0, Real.sqrt_eq_rpow]
    congr 1
    exact_mod_cast Real.rpow_natCast d (2 * t)
  rw [Real.sqrt_sq hd0.le, h1]
  calc ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * d
      = ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * (Real.sqrt d * Real.sqrt d) := by rw [hs]
    _ = _ := by
        rw [← pow_mul, show 2 * (2 * t) = 2 * t + 2 * t by ring, pow_add]
        field_simp

theorem covolQuotient_arith : ∀ (d c : ℝ) (f t : ℕ) (m : ℝ≥0∞), 1 ≤ d → 0 < c →
    ENNReal.ofReal (((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2)) =
      ENNReal.ofReal ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) * m →
    ENNReal.ofReal ((2 * c) ^ f) * m = ENNReal.ofReal (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by
  intro d c f t m hd hc h
  have hd0 : 0 < d := by linarith
  have hY : 0 < (d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d :=
    mul_pos (mul_pos (inv_pos.mpr (pow_pos hd0 _)) (by norm_num)) (Real.sqrt_pos.mpr hd0)
  have hZ : 0 ≤ (2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hd0.le _)

  rw [covolQuotient_real d f t hd, ENNReal.ofReal_mul hY.le] at h
  have hm : m = ENNReal.ofReal ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ))) :=
    ((ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hY).ne' ENNReal.ofReal_ne_top).mp h).symm
  rw [hm, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) f)]
  congr 1
  have h2 : (2 : ℝ) ^ f * (2⁻¹ : ℝ) ^ f = 1 := by rw [← mul_pow]; norm_num
  calc (2 * c) ^ f * ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ)))
      = ((2 : ℝ) ^ f * (2⁻¹ : ℝ) ^ f) * (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by ring
    _ = d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f := by rw [h2, one_mul]

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem exists_fundamentalDomain_snd_of_two_smul_mem {ι : Type} [Fintype ι]
    (Λ : Submodule ℤ ((ι → ℝ) × (ι → ℝ))) [DiscreteTopology Λ] :
    Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) = ⊤ →
    (∀ a b, (a, b) ∈ Λ → ((0 : ι → ℝ), (2 : ℝ) • b) ∈ Λ) →
    ∃ D : Set (ι → ℝ), MeasurableSet D ∧
      ∀ y, ∃! l, l ∈ {b : ι → ℝ | ∃ a, (a, b) ∈ Λ} ∧ y + l ∈ D := by
  intro hspan h2
  let L₂ : Submodule ℤ (ι → ℝ) := Λ.map (LinearMap.snd ℤ (ι → ℝ) (ι → ℝ))
  have hmem : ∀ b, b ∈ L₂ ↔ ∃ a, (a, b) ∈ Λ := by
    intro b
    simp only [L₂, Submodule.mem_map, LinearMap.snd_apply]
    constructor
    · rintro ⟨⟨a, b'⟩, h, rfl⟩; exact ⟨a, h⟩
    · rintro ⟨a, h⟩; exact ⟨(a, b), h, rfl⟩
  have hin : ∀ x : L₂, ((0 : ι → ℝ), (2 : ℝ) • (x : ι → ℝ)) ∈ Λ := by
    intro x
    obtain ⟨a, ha⟩ := (hmem x).1 x.2
    exact h2 a x ha
  haveI : DiscreteTopology L₂ := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : L₂ => (⟨((0 : ι → ℝ), (2 : ℝ) • (x : ι → ℝ)), hin x⟩ : Λ)) ?_ ?_
    · exact Continuous.subtype_mk
        (by fun_prop) _
    · intro x y hxy
      have h := congrArg (fun z : Λ => (z : (ι → ℝ) × (ι → ℝ)).2) hxy
      simp only at h
      exact Subtype.ext (smul_right_injective _ (two_ne_zero) h)
  haveI : IsZLattice ℝ L₂ := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    intro y _
    have hy : ((0 : ι → ℝ), y) ∈ Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) := by
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := LinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) hy
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨⟨a, b⟩, h, rfl⟩
    exact (hmem b).2 ⟨a, h⟩
  refine ⟨latticeDomain L₂, measurableSet_latticeDomain L₂, fun y => ?_⟩
  obtain ⟨⟨l, hl⟩, h1, h3⟩ := existsUnique_add_mem_latticeDomain L₂ y
  refine ⟨l, ⟨(hmem l).1 hl, h1⟩, ?_⟩
  rintro m ⟨hm, hm'⟩
  exact congrArg Subtype.val (h3 ⟨m, (hmem m).2 hm⟩ hm')

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem addFundamentalDomains_measure_eq : ∀ {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (L : Submodule ℤ V) [Countable L] (D D' : Set V), MeasurableSet D → MeasurableSet D' → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D') → μ D = μ D' := by
  intro V _ _ _ μ _ L _ D D' hD hD' hu hu'
  let G : AddSubgroup V := L.toAddSubgroup
  haveI : Countable G := inferInstanceAs (Countable L)
  have key : ∀ E : Set V, MeasurableSet E → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ E) →
      IsAddFundamentalDomain G E μ := by
    intro E hE hEu
    refine IsAddFundamentalDomain.mk' hE.nullMeasurableSet ?_
    intro x
    obtain ⟨l, ⟨hlL, hlE⟩, huniq⟩ := hEu x
    refine ⟨⟨l, hlL⟩, ?_, ?_⟩
    · show (l : V) + x ∈ E
      rwa [add_comm]
    · rintro ⟨g, hg⟩ hgE
      have hgE' : x + g ∈ E := by
        have : (g : V) + x ∈ E := hgE
        rwa [add_comm]
      exact Subtype.ext (huniq g ⟨hg, hgE'⟩)
  exact (key D hD hu).measure_eq (key D' hD' hu')

end GlobalTheory
end
