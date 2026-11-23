module

public import Mathlib.FieldTheory.KrullTopology
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory

theorem restrictScalarsHom_continuous_krull (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω]
    (K : IntermediateField E Ω) :
    Continuous (AlgEquiv.restrictScalarsHom E : G K Ω →* G E Ω) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨L, hL, hLs⟩ := hs
  let b := Module.finBasis E L
  have hint : ∀ i, IsIntegral K ((b i : L) : Ω) := fun i =>
    ((IsIntegral.of_finite E (b i)).map (IsScalarTower.toAlgHom E L Ω)).tower_top
  have hN : ⋂ i, ((IntermediateField.adjoin K {((b i : L) : Ω)}).fixingSubgroup : Set (G K Ω))
      ∈ nhds (1 : G K Ω) := Filter.iInter_mem.mpr fun i => by
    haveI := IntermediateField.adjoin.finiteDimensional (hint i)
    exact (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hN ?_
  intro σ hσ
  apply hLs
  simp only [Set.mem_iInter, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, σ ((b i : L) : Ω) = ((b i : L) : Ω) := fun i =>
    hσ i _ (IntermediateField.mem_adjoin_simple_self K _)
  obtain ⟨y, rfl⟩ : ∃ y : L, (y : Ω) = x := ⟨⟨x, hx⟩, rfl⟩
  rw [← b.sum_repr y]
  change (AlgEquiv.restrictScalars E σ) _ = _

  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgEquiv.restrictScalars_apply, hb]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

noncomputable section

namespace GlobalTheory.FrobRestrict

open scoped Pointwise

open NumberField IsDedekindDomain in
open scoped Pointwise in
theorem _root_.GlobalTheory.FrobRestrict.isFrob_pow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : _root_.Formalism.ConjugateSelfDual.G F Ω} (hφ : _root_.Formalism.ConjugateSelfDual.IsFrob A q φ) (n : ℕ) :
    _root_.Formalism.ConjugateSelfDual.IsFrob A (q ^ n) (φ ^ n) := by
  have hdec : φ ∈ ValuationSubring.decompositionSubgroup F A := hφ.1
  induction n with
  | zero => exact ⟨one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hdec _, fun x hx => ?_⟩
    have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one' hx q
    have e : (φ ^ (n + 1)) x - x ^ q ^ (n + 1)
        = ((φ ^ n) (x ^ q) - (x ^ q) ^ q ^ n) + (φ ^ n) (φ x - x ^ q) := by
      rw [pow_succ, AlgEquiv.mul_apply, map_sub, pow_succ', pow_mul]
      ring
    rw [e]
    refine Valuation.map_add_lt _ (ih.2 _ hxq) ?_
    rw [_root_.ReciprocityTheory.Gal.valuation_apply_lt_one_iff (Subgroup.pow_mem _ hdec n)]
    exact hφ.2 x hx

open NumberField IsDedekindDomain in
open scoped Pointwise in
private lemma restrictScalars_mem_decompositionSubgroup {E Ω : Type} [Field E] [Field Ω]
    [Algebra E Ω] {K : IntermediateField E Ω} {A : ValuationSubring Ω} {ι : _root_.Formalism.ConjugateSelfDual.G K Ω}
    (h : ι ∈ ValuationSubring.decompositionSubgroup K A) :
    ι.restrictScalars E ∈ ValuationSubring.decompositionSubgroup E A := by
  simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at h ⊢
  exact h

open NumberField IsDedekindDomain in
open scoped Pointwise in
theorem _root_.GlobalTheory.FrobRestrict.frob_restrict : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)),
    w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω,
    _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧
    (∀ ι ∈ _root_.ReciprocityTheory.Gal.Ine (F := K) A, ι.restrictScalars E ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∧
    ∀ (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) (φ : _root_.Formalism.ConjugateSelfDual.G E Ω), _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV w) σ → _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) φ →
    σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A := by
  intro E Ω _ _ _ _ K _ _ v w h A hw
  have hnorm : _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E) := by
    haveI : w.asIdeal.LiesOver v.asIdeal := ⟨h.symm⟩
    haveI := v.isMaximal
    haveI := w.isMaximal
    rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
    unfold _root_.Formalism.ConjugateSelfDual.normV
    letI := Ideal.Quotient.field v.asIdeal
    exact Module.natCard_eq_pow_finrank (K := 𝓞 E ⧸ v.asIdeal) (V := 𝓞 K ⧸ w.asIdeal)
  refine ⟨fun x => ?_, hnorm, fun ι hι => ?_, fun σ φ hσ hφ => ?_⟩
  · have e : (algebraMap K Ω) ((algebraMap (𝓞 E) (𝓞 K) x : 𝓞 K) : K)
        = algebraMap E Ω (x : E) := by
      rw [IsScalarTower.algebraMap_apply E K Ω]
      rfl
    rw [← e, hw, ← h, Ideal.mem_comap]
  · rw [_root_.ReciprocityTheory.Gal.mem_Ine] at hι ⊢
    exact ⟨restrictScalars_mem_decompositionSubgroup hι.1, hι.2⟩
  · have hσ' : _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E)) (σ.restrictScalars E) := by
      rw [← hnorm]
      exact ⟨restrictScalars_mem_decompositionSubgroup hσ.1, hσ.2⟩
    have hφf := _root_.GlobalTheory.FrobRestrict.isFrob_pow hφ (w.asIdeal.inertiaDeg (𝓞 E))
    have h1 := _root_.ReciprocityTheory.Gal.inv_mul_mem_Ine_of_isFrob hφf hσ'
    have h2 := _root_.ReciprocityTheory.Gal.conj_mem_Ine (g := φ ^ w.asIdeal.inertiaDeg (𝓞 E)) hφf.1 h1
    rwa [mul_inv_cancel_left] at h2

end GlobalTheory.FrobRestrict
end
end
