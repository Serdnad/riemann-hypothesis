module

public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.Fintype.Order
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Associator

@[expose] public section

section

open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ModChar

theorem modularCharacterFun_eq_of_map_left_mul :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (ρ : Measure Q) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [ρ.IsMulRightInvariant] (δ : Q →* ℝ≥0), (∀ q : Q, ρ.map (fun x => q * x) = (δ q)⁻¹ • ρ) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  intro Q _ _ _ _ _ _ _ _ ρ _ _ _ δ h q
  have : ρ.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  have hδ : (δ q⁻¹)⁻¹ = δ q := by
    rw [inv_eq_iff_eq_inv]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel, map_one]
  have hcomp : (fun x : Q => x * q) ∘ Inv.inv = Inv.inv ∘ (fun y : Q => q⁻¹ * y) := by
    funext y
    simp [mul_inv_rev]
  have hmap : Measure.map (fun x : Q => x * q) ρ.inv = δ q • ρ.inv := by
    rw [Measure.inv_def, Measure.map_map (measurable_mul_const q) measurable_inv, hcomp,
      ← Measure.map_map measurable_inv (measurable_const_mul q⁻¹), h q⁻¹, Measure.map_smul, hδ]
    exact measurable_inv.aemeasurable
  rw [Measure.modularCharacterFun_eq_haarScalarFactor ρ.inv q]
  simp only [hmap, Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self, smul_eq_mul, mul_one]

end GlobalTheory.CompanionTheory.ModChar
end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.MeasureTails

theorem tendsto_setLIntegral_diff_compactCovering
    {α : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [T2Space α]
    [SigmaCompactSpace α] (μ : Measure α) (F : Set α) (h : α → ℝ≥0∞)
    (hfin : ∫⁻ x in F, h x ∂μ < ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ x in F \ compactCovering α k, h x ∂μ) atTop (𝓝 0) := by
  set m : Measure α := (μ.restrict F).withDensity h with hm
  have hmeas : ∀ k : ℕ, MeasurableSet (compactCovering α k)ᶜ := fun k =>
    ((isCompact_compactCovering α k).isClosed.measurableSet).compl
  have hrew : ∀ k : ℕ, ∫⁻ x in F \ compactCovering α k, h x ∂μ = m (compactCovering α k)ᶜ := by
    intro k
    rw [hm, withDensity_apply h (hmeas k), Measure.restrict_restrict (hmeas k), Set.diff_eq,
      Set.inter_comm]
  have huniv : m Set.univ < ⊤ := by
    rw [hm, withDensity_apply h MeasurableSet.univ, Measure.restrict_univ]
    exact hfin
  have hanti : Antitone (fun k : ℕ => (compactCovering α k)ᶜ) := fun i j hij =>
    Set.compl_subset_compl.mpr (compactCovering_subset α hij)
  have hinter : ⋂ k : ℕ, (compactCovering α k)ᶜ = ∅ := by
    rw [← Set.compl_iUnion, iUnion_compactCovering, Set.compl_univ]
  have hne : ∃ k : ℕ, m (compactCovering α k)ᶜ ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top huniv.ne (measure_mono (Set.subset_univ _))⟩
  have key := tendsto_measure_iInter_atTop (μ := m)
    (fun k => (hmeas k).nullMeasurableSet) hanti hne
  rw [hinter, measure_empty] at key
  simp only [hrew]
  exact key

end GlobalTheory.CompanionTheory.MeasureTails
end

section

open ValuativeRel MeasureTheory Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.LocalModule

theorem distribHaarChar_eq_one_of_valuation_eq_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (u : kˣ), valuation k (u : k) = 1 → distribHaarChar k u = 1 := by
  intro k _ _ _ _ u hu
  borelize k
  have hsc : IsCompact {x : k | valuation k x ≤ 1} :=
    IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hso : IsOpen {x : k | valuation k x ≤ 1} :=
    Valuation.isOpen_integer (v := valuation k)
  have hus : u • {x : k | valuation k x ≤ 1} = {x : k | valuation k x ≤ 1} := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_ofPred_eq, Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hu, inv_one, one_mul]
  have h0 : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ 0 :=
    (hso.measure_pos Measure.addHaar ⟨0, by simp⟩).ne'
  have hfin : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ ⊤ := hsc.measure_lt_top.ne
  exact distribHaarChar_eq_of_measure_smul_eq_mul h0 hfin (by rw [hus, ENNReal.coe_one, one_mul])

end GlobalTheory.CompanionTheory.LocalModule
end

section

open Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalLattice

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSubgroup (k : Type) [Field k] [ValuativeRel k] (n : ℕ) (γ : ValueGroupWithZero k) :
    AddSubgroup (Fin n → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ γ}
  zero_mem' := fun i => by simp
  add_mem' := fun {a b} ha hb i =>
    (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))
  neg_mem' := fun {a} ha i => by simpa using ha i

theorem coe_ballSubgroup (n : ℕ) (γ : ValueGroupWithZero k) :
    (ballSubgroup k n γ : Set (Fin n → k)) =
      Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
  ext x
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq]
  rfl

theorem isCompact_ballSubgroup (n : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact (ballSubgroup k n γ : Set (Fin n → k)) := by
  rw [coe_ballSubgroup]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ

theorem isOpen_ballSubgroup (n : ℕ) {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    IsOpen (ballSubgroup k n γ : Set (Fin n → k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  rw [GlobalTheory.CompanionTheory.LocalLattice.coe_ballSubgroup]
  refine set_pi_mem_nhds Set.finite_univ fun i _ => ?_
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2
    ⟨Units.mk0 γ hγ, fun x (hx : valuation k x < γ) => hx.le⟩

theorem exists_compact_open_addSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)) (hK : IsCompact K) :
    ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
      IsOpen (A : Set (Fin n → k)) ∧ K ⊆ A := by
  have hne : ∀ γ : ValueGroupWithZero k, max γ 1 ≠ 0 :=
    fun γ => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right γ 1))
  have hmono : Monotone fun γ : ValueGroupWithZero k =>
      (GlobalTheory.CompanionTheory.LocalLattice.ballSubgroup k n (max γ 1) : Set (Fin n → k)) :=
    fun γ δ hγδ x hx i => (hx i).trans (max_le_max hγδ le_rfl)
  have hcover : K ⊆ ⋃ γ : ValueGroupWithZero k, (GlobalTheory.CompanionTheory.LocalLattice.ballSubgroup k n (max γ 1) : Set (Fin n → k)) := by
    intro x _
    obtain ⟨γ, hγ⟩ := Finite.exists_le fun i => valuation k (x i)
    exact Set.mem_iUnion.2 ⟨γ, fun i => (hγ i).trans (le_max_left γ 1)⟩
  obtain ⟨γ, hγ⟩ := hK.elim_directed_cover _
    (fun γ => GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup n (hne γ)) hcover hmono.directed_le
  exact ⟨_, GlobalTheory.CompanionTheory.LocalLattice.isCompact_ballSubgroup n _, GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup n (hne γ), hγ⟩

end GlobalTheory.CompanionTheory.LocalLattice
end
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Dblock.ComapLat

theorem comap_mulVec_compact_open : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  intro k _ _ _ _ n g hg A hc ho
  haveI : IsTopologicalRing k := inferInstance
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hcont : ∀ m : Matrix (Fin n) (Fin n) k, Continuous (fun x : Fin n → k => m.mulVec x) :=
    fun m => continuous_const.matrix_mulVec continuous_id
  have hset : ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k))
      = (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k)) := rfl
  rw [hset]
  refine ⟨?_, ho.preimage (hcont g)⟩
  have himg : (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k))
      = (fun x : Fin n → k => g⁻¹.mulVec x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.mulVec x, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hdet, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet,
        Matrix.one_mulVec]
      exact hy
  rw [himg]
  exact hc.image (hcont g⁻¹)

end GlobalTheory.CompanionTheory.Dblock.ComapLat
end

section

open Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.LatticePoint

theorem isOpen_valBall {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change valuation k x ≤ γ at hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  change valuation k (y - x) < ((Units.mk0 γ hγ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) at hy
  rw [Units.val_mk0] at hy
  show valuation k y ≤ γ
  calc valuation k y = valuation k ((y - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation k (y - x)) (valuation k x) := Valuation.map_add _ _ _
    _ ≤ γ := max_le hy.le hx

theorem exists_compact_open_addSubgroup_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ) (x : Fin n → k),
      ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
        IsOpen (A : Set (Fin n → k)) ∧ x ∈ A := by
  intro k _ _ _ _ n x
  let γ : ValueGroupWithZero k := Finset.univ.sup (fun i => valuation k (x i)) ⊔ 1
  have hγ : γ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one le_sup_right)
  let S : AddSubgroup k :=
    { carrier := {y | valuation k y ≤ γ}
      add_mem' := fun {a b} ha hb => by
        change valuation k a ≤ γ at ha
        change valuation k b ≤ γ at hb
        show valuation k (a + b) ≤ γ
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by
        show valuation k 0 ≤ γ
        simp
      neg_mem' := fun {a} ha => by
        change valuation k a ≤ γ at ha
        show valuation k (-a) ≤ γ
        rwa [Valuation.map_neg] }
  have hS : (S : Set k) = {y | valuation k y ≤ γ} := rfl
  refine ⟨AddSubgroup.pi Set.univ (fun _ => S), ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi, hS]
    exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
  · rw [AddSubgroup.coe_pi, hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall γ hγ
  · rw [AddSubgroup.mem_pi]
    intro i _
    show valuation k (x i) ≤ γ
    exact le_sup_of_le_left (Finset.le_sup (f := fun i => valuation k (x i)) (Finset.mem_univ i))

end GlobalTheory.CompanionTheory.LatticePoint
end

section

open ValuativeRel MeasureTheory Matrix
open Filter Topology

namespace GlobalTheory.CompanionTheory.CompactScaling

theorem exists_pow_smul_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∀ U ∈ nhds (0 : Fin n → k), ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ x ∈ K, ϖ ^ l • x ∈ U := by
  intro k _ _ _ _ n K hK U hU ϖ hϖ
  have hpow : Tendsto (fun l : ℕ => ϖ ^ l) atTop (𝓝 (0 : k)) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hϖ γ
    rw [eventually_atTop]
    refine ⟨m, fun l hl => ?_⟩
    simp only [Set.mem_ofPred_eq, map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hl) hm
  have hnear : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ K, c • x ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun x _ => ?_)
    have hcont : Continuous (fun p : k × (Fin n → k) => p.1 • p.2) :=
      continuous_fst.smul continuous_snd
    have hlim : Tendsto (fun p : k × (Fin n → k) => p.1 • p.2) (𝓝 (0, x)) (𝓝 0) := by
      simpa using hcont.tendsto (0, x)
    exact hlim hU
  exact (hpow.eventually hnear).exists

end GlobalTheory.CompanionTheory.CompactScaling
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem traceDual_clear_by_integer : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ f : F,
    (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f := by
  intro F _ _
  obtain ⟨a, ha, hint⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)).isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  refine ⟨Ideal.absNorm (Ideal.span {a}), ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha0
  · intro f hf
    have hmem : f ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (nonZeroDivisors (𝓞 F)) F))]
      intro x hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      obtain ⟨m, hm⟩ := hf r
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, eq_intCast]
      exact hm.symm
    obtain ⟨o, ho⟩ := hint f hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨c * o, ?_⟩
    rw [Algebra.smul_def] at ho
    show algebraMap (𝓞 F) F (c * o) = _
    rw [map_mul, ho, ← mul_assoc, ← map_mul, hc, map_natCast]

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.NumberFieldCoord

theorem abs_repr_le_of_forall_norm_embedding_le :
    ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)),
      Function.Surjective (fun i => InfinitePlace.mk (τ i)) →
      ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) →
        ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  intro E _ _ I _ τ hτ
  classical
  set Lc := LinearMap.toContinuousLinearMap (mixedEmbedding.latticeBasis E).equivFun.toLinearMap
    with hLc
  refine ⟨‖Lc‖ + 1, by positivity, fun e R hR k => ?_⟩
  have hR0 : 0 ≤ R := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    obtain ⟨i, -⟩ := hτ w
    exact (norm_nonneg _).trans (hR i)
  have hw : ∀ w : InfinitePlace E, w (e : E) ≤ R := by
    intro w
    obtain ⟨i, rfl⟩ := hτ w
    simpa only [InfinitePlace.apply] using hR i
  have hn : ‖mixedEmbedding E (e : E)‖ ≤ R := by
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_of_isReal w.2] at h
      simpa [mixedEmbedding] using h
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_eq] at h
      simpa [mixedEmbedding] using h
  have hval : Lc (mixedEmbedding E (e : E)) k = (((RingOfIntegers.basis E).repr e k : ℤ) : ℝ) := by
    change (mixedEmbedding.latticeBasis E).equivFun (mixedEmbedding E (e : E)) k = _
    rw [Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply]
    have := integralBasis_repr_apply E e k
    rw [show (e : E) = algebraMap (𝓞 E) E e from rfl, this]
    simp
  rw [← hval, ← Real.norm_eq_abs]
  calc ‖Lc (mixedEmbedding E (e : E)) k‖ ≤ ‖Lc (mixedEmbedding E (e : E))‖ := norm_le_pi_norm _ k
    _ ≤ ‖Lc‖ * ‖mixedEmbedding E (e : E)‖ := Lc.le_opNorm _
    _ ≤ ‖Lc‖ * R := by gcongr
    _ ≤ (‖Lc‖ + 1) * R := by nlinarith

end GlobalTheory.CompanionTheory.NumberFieldCoord
end

section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem preimage_box_shrinking : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by
  intro G A ι _ _ _ _ _ e U hU hlim
  refine ⟨fun k => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ => (hU k).1)
  · exact (isOpen_set_pi Set.finite_univ fun _ _ => (hU k).2.1).preimage e.continuous
  · show e 0 ∈ Set.pi Set.univ (fun _ => U k)
    rw [map_zero]
    exact Set.mem_univ_pi.2 fun _ => (hU k).2.2
  · rw [Filter.tendsto_smallSets_iff] at hlim ⊢
    intro t ht
    have hc : Filter.Tendsto e.symm (nhds 0) (nhds 0) := by
      have h0 : Filter.Tendsto e.symm (nhds 0) (nhds (e.symm 0)) := e.symm.continuous.tendsto 0
      rw [map_zero] at h0
      exact h0
    have h1 : e.symm ⁻¹' t ∈ nhds (0 : ι → A) := hc ht
    rw [nhds_pi, Filter.mem_pi'] at h1
    obtain ⟨I, s, hs, hsub⟩ := h1
    have hW : (⋂ i, s i) ∈ nhds (0 : A) := Filter.iInter_mem.2 hs
    filter_upwards [hlim _ hW] with k hk
    intro x hx
    have h2 : e x ∈ Set.pi (I : Set ι) s := fun i _ =>
      Set.mem_iInter.1 (hk (hx i (Set.mem_univ i))) i
    simpa using hsub h2

end GlobalTheory.CompanionTheory.BigCell
end

section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FiniteComplete

theorem isAdicComplete_of_finite : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [AddCommGroup M] [Module O M]
    [Module.Finite O M], IsAdicComplete (IsLocalRing.maximalIdeal O) M := by
  intro O M _ _ _ hO _ _ _
  set I := IsLocalRing.maximalIdeal O
  have hb : Function.Bijective (AdicCompletion.of I O) := AdicCompletion.of_bijective_iff.2 hO
  let φ : O ≃ₗ[O] AdicCompletion I O := LinearEquiv.ofBijective (AdicCompletion.of I O) hb
  let e : M ≃ₗ[O] AdicCompletion I O ⊗[O] M :=
    (TensorProduct.lid O M).symm.trans (TensorProduct.congr φ (LinearEquiv.refl O M))
  have h1 : AdicCompletion.of I O 1 = 1 := by
    ext n
    simp
  have hfac : ⇑(AdicCompletion.of I M) = ⇑(AdicCompletion.ofTensorProduct I M) ∘ ⇑e := by
    funext m
    have he : e m = (1 : AdicCompletion I O) ⊗ₜ[O] m := by
      simp [e, φ, h1]
    simp [he]
  refine AdicCompletion.of_bijective_iff.1 ?_
  rw [hfac]
  exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).comp e.bijective

end GlobalTheory.CompanionTheory.FiniteComplete
end
