module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.Cusp

variable {G : Type} [Group G] [TopologicalSpace G] (Γ N : Subgroup G)

def Cocompact : Prop := ∃ K : Set N, IsCompact K ∧ ∀ n : N, ∃ γ ∈ Γ.subgroupOf N, γ * n ∈ K

instance discreteTopology_subgroupOf [DiscreteTopology Γ] : DiscreteTopology (Γ.subgroupOf N) :=
  .of_continuous_injective (f := fun x : Γ.subgroupOf N => (⟨x.1.1, x.2⟩ : Γ))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => z.1) h))

instance secondCountable_subgroup [SecondCountableTopology G] : SecondCountableTopology N :=
  TopologicalSpace.Subtype.secondCountableTopology _

variable [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ]
  [LocallyCompactSpace N]

def probMeasure : Measure (Quot (Γ.subgroupOf N)) :=
  (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure (Γ.subgroupOf N) Measure.haar univ)⁻¹ • _root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure (Γ.subgroupOf N) Measure.haar

def constTermOn (φ : G → ℂ) (x : G) : ℂ := ∫ q, φ ((q.out : N) * x) ∂probMeasure Γ N

variable {Γ N} {φ ψ : G → ℂ} {μ : Measure N} {𝓕 : Set N}


omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [DiscreteTopology Γ] [LocallyCompactSpace N] in
theorem leftInv_integrand (hφ : LeftInv Γ φ) (x : G) : LeftInv (Γ.subgroupOf N) fun n : N => φ (n * x) :=
  fun γ hγ n => by simp only [Subgroup.coe_mul, mul_assoc]; exact hφ _ hγ _

theorem probMeasure_eq (μ : Measure N) [μ.IsHaarMeasure] :
    probMeasure Γ N = (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure (Γ.subgroupOf N) μ univ)⁻¹ • _root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure (Γ.subgroupOf N) μ := by
  have h0 : ((Measure.haarScalarFactor μ Measure.haar : NNReal) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure μ Measure.haar).ne'
  conv_rhs => rw [Measure.isMulLeftInvariant_eq_smul μ Measure.haar]
  rw [ENNReal.smul_def, quotMeasure_smul, smul_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.coe_ne_top), mul_right_comm, ENNReal.inv_mul_cancel h0 ENNReal.coe_ne_top,
    one_mul, probMeasure]

theorem constTermOn_eq [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (hφ : LeftInv Γ φ) (x : G) :
    constTermOn Γ N φ x = (μ.real 𝓕)⁻¹ • ∫ n in 𝓕, φ (n * x) ∂μ := by
  rw [constTermOn, probMeasure_eq μ, integral_smul_measure, quotMeasure_univ h, integral_quotMeasure h,
    ENNReal.toReal_inv, measureReal_def]
  exact congrArg _ (integral_congr_ae (.of_forall (leftInv_integrand hφ x).descend_mk))

theorem constTermOn_eq_of_measure_eq_one [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ)
    (h1 : μ 𝓕 = 1) (hφ : LeftInv Γ φ) (x : G) : constTermOn Γ N φ x = ∫ n in 𝓕, φ (n * x) ∂μ := by
  simp [constTermOn_eq h hφ, measureReal_def, h1]

theorem constTermOn_mul_right (φ : G → ℂ) (x g : G) :
    constTermOn Γ N (fun y => φ (y * g)) x = constTermOn Γ N φ (x * g) := by
  simp only [constTermOn, mul_assoc]

theorem constTermOn_smul (c : ℂ) (φ : G → ℂ) (x : G) : constTermOn Γ N (c • φ) x = c * constTermOn Γ N φ x :=
  integral_const_mul c _

theorem constTermOn_mul_left_of_normalizer (hφ : LeftInv Γ φ) {γ : G} (hγ : γ ∈ Γ)
    (hN : ∀ n, n ∈ N ↔ γ * n * γ⁻¹ ∈ N) (x : G) : constTermOn Γ N φ (γ * x) = constTermOn Γ N φ x := by
  let e : N ≃ₜ* N :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, (hN _).1 n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, (hN _).2 (by simp [mul_assoc])⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let m := e.toHomeomorph.toMeasurableEquiv
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) (Measure.haar.map e)
  have hp : MeasurePreserving m Measure.haar (Measure.haar.map e) := ⟨m.measurable, rfl⟩
  have h' : IsFundamentalDomain (Γ.subgroupOf N) (m ⁻¹' stdDom (Γ.subgroupOf N)) Measure.haar :=
    h.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  rw [constTermOn_eq h hφ, constTermOn_eq h' hφ, ← hp.setIntegral_preimage_emb m.measurableEmbedding,
    measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  refine congrArg _ (integral_congr_ae (.of_forall fun n => ?_))
  change φ (γ * n * γ⁻¹ * (γ * x)) = φ (n * x)
  rw [mul_assoc, inv_mul_cancel_left, mul_assoc, hφ γ hγ]

namespace Cocompact

variable (hc : Cocompact Γ N)
include hc


omit [LocallyCompactSpace N] in
theorem integrableOn [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (hφ : LeftInv Γ φ)
    (hφc : Continuous φ) (x : G) : IntegrableOn (fun n : N => φ (n * x)) 𝓕 μ :=
  let ⟨K, hK, hs⟩ := hc
  GlobalTheory.integrableOn_fundamentalDomain_of_cocompact N _ K hK hs μ inferInstance 𝓕 h _ (by fun_prop)
    (leftInv_integrand hφ x)


omit [LocallyCompactSpace N] in
theorem measure_ne_top [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) : μ 𝓕 ≠ ⊤ :=
  ((integrableOn_const_iff (C := (1 : ℂ))).1
    (hc.integrableOn h (φ := fun _ => 1) (fun _ _ _ => rfl) continuous_const 1)).elim (by simp) LT.lt.ne

theorem isProbabilityMeasure : IsProbabilityMeasure (probMeasure Γ N) :=
  ⟨ENNReal.inv_mul_cancel (NeZero.ne _) (by
    rw [quotMeasure_univ (isFundamentalDomain_stdDom _ _)]; exact hc.measure_ne_top (isFundamentalDomain_stdDom _ _))⟩

theorem integrable (hφ : LeftInv Γ φ) (hφc : Continuous φ) (x : G) :
    Integrable (fun q : Quot (Γ.subgroupOf N) => φ ((q.out : N) * x)) (probMeasure Γ N) := by
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) Measure.haar
  refine Integrable.smul_measure (memLp_one_iff_integrable.1 ((memLp_quotMeasure_iff h).2 ?_))
    (ENNReal.inv_ne_top.2 (NeZero.ne _))
  rw [show lift _ (fun q : Quot (Γ.subgroupOf N) => φ ((q.out : N) * x)) = _ from
    (leftInv_integrand (N := N) hφ x).lift_descend]
  exact memLp_one_iff_integrable.2 (hc.integrableOn h hφ hφc x)

theorem constTermOn_const (c : ℂ) (x : G) : constTermOn Γ N (fun _ => c) x = c := by
  have := hc.isProbabilityMeasure
  simp [constTermOn]

theorem constTermOn_add (hφ : LeftInv Γ φ) (hφc : Continuous φ) (hψ : LeftInv Γ ψ) (hψc : Continuous ψ) (x : G) :
    constTermOn Γ N (φ + ψ) x = constTermOn Γ N φ x + constTermOn Γ N ψ x :=
  integral_add (hc.integrable hφ hφc x) (hc.integrable hψ hψc x)

theorem constTermOn_eq_zero_iff [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (hφ : LeftInv Γ φ)
    (x : G) : constTermOn Γ N φ x = 0 ↔ ∫ n in 𝓕, φ (n * x) ∂μ = 0 :=
  (constTermOn_eq h hφ x).symm ▸ smul_eq_zero_iff_right (inv_ne_zero
    (ENNReal.toReal_ne_zero.2 ⟨h.measure_ne_zero (NeZero.ne μ), hc.measure_ne_top h⟩))

theorem isMulRightInvariant (μ : Measure N) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := ⟨fun g => by
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) μ
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  have h' : IsFundamentalDomain (Γ.subgroupOf N) ((· * g) ⁻¹' stdDom (Γ.subgroupOf N)) μ :=
    h.preimage_of_equiv ⟨(measurable_mul_const g).aemeasurable, e ▸ Measure.smul_absolutelyContinuous⟩ Function.bijective_id
      fun γ x => mul_assoc _ _ _
  have h1 := h'.measure_eq h
  rw [← Measure.map_apply (measurable_mul_const g) (measurableSet_stdDom _), e, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul, ENNReal.mul_eq_right (h.measure_ne_zero (NeZero.ne μ)) (hc.measure_ne_top h), ENNReal.coe_eq_one] at h1
  rw [e, h1, one_smul]⟩

theorem constTermOn_mul_left (hφ : LeftInv Γ φ) {n : G} (hn : n ∈ N) (x : G) :
    constTermOn Γ N φ (n * x) = constTermOn Γ N φ x := by
  have := hc.isMulRightInvariant Measure.haar
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) Measure.haar
  have hp := measurePreserving_mul_right (Measure.haar : Measure N) ⟨n, hn⟩
  have h' := h.preimage_of_equiv hp.quasiMeasurePreserving Function.bijective_id fun γ x => mul_assoc _ _ _
  rw [constTermOn_eq h' hφ, constTermOn_eq h hφ, ← hp.setIntegral_preimage_emb (measurableEmbedding_mulRight _) _
    (stdDom _), measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  simp only [Subgroup.coe_mul, mul_assoc]

theorem continuous_constTermOn [LocallyCompactSpace G] (hφ : LeftInv Γ φ) (hφc : Continuous φ) :
    Continuous (constTermOn Γ N φ) := by
  have := hc.isProbabilityMeasure
  obtain ⟨K, hK, hs⟩ := id hc
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨C, hC⟩ := (hK.prod hU).exists_bound_of_continuousOn (f := fun p : N × G => φ (p.1 * p.2)) (by fun_prop)
  refine continuousAt_of_dominated (bound := fun _ => C) (.of_forall fun y => (hc.integrable hφ hφc y).1)
    (Filter.Eventually.mono hx fun y hy => .of_forall fun q => ?_) (integrable_const C) (.of_forall fun q => by fun_prop)
  obtain ⟨γ, hγ, hk⟩ := hs q.out
  exact (congrArg norm (leftInv_integrand hφ y γ hγ q.out)).ge.trans (hC (_, y) ⟨hk, hy⟩)

end Cocompact

end GlobalTheory.Cusp

end
end

section

noncomputable section

namespace GlobalTheory.Eis

open scoped NNReal
open Filter Topology Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

section Sums

variable {G : Type} [Group G] (P Γ : Subgroup G)

abbrev Cosets : Type := Quot (P.subgroupOf Γ)

def term {X : Type} (Φ : G → X) (g : G) (q : Cosets P Γ) : X := Φ ((q.out : Γ) * g)

def cosetSum (Φ : G → ℂ) (g : G) : ℂ := ∑' q, term P Γ Φ g q

def CosetConv (Φ : G → ℂ) (g : G) : Prop := Summable fun q => ‖term P Γ Φ g q‖

def rmulEquiv (γ : Γ) : Cosets P Γ ≃ Cosets P Γ :=
  ⟨rmul _ γ, rmul _ γ⁻¹, fun q => by rw [← rmul_mul, mul_inv_cancel, rmul_one],
    fun q => by rw [← rmul_mul, inv_mul_cancel, rmul_one]⟩

variable {P Γ} {X : Type} {Φ Ψ : G → ℂ} {g : G}

theorem term_mk {Φ : G → X} (h : LeftInv (P ⊓ Γ) Φ) (g : G) (γ : Γ) : term P Γ Φ g (mk _ γ) = Φ (γ * g) :=
  LeftInv.descend_mk (Γ := P.subgroupOf Γ) (φ := fun x : Γ => Φ (x * g))
    (fun δ hδ x => (congrArg Φ (mul_assoc _ _ _)).trans (h δ ⟨hδ, δ.2⟩ _)) γ

theorem term_mul_left {Φ : G → X} (h : LeftInv (P ⊓ Γ) Φ) (γ : Γ) (g : G) (q : Cosets P Γ) :
    term P Γ Φ (γ * g) q = term P Γ Φ g (rmulEquiv P Γ γ q) :=
  Quotient.inductionOn q fun x => (term_mk h _ x).trans (((term_mk h g (x * γ)).trans (by simp [mul_assoc])).symm)

theorem leftInv_cosetSum (h : LeftInv (P ⊓ Γ) Φ) : LeftInv Γ (cosetSum P Γ Φ) := fun γ hγ g =>
  (tsum_congr (term_mul_left h ⟨γ, hγ⟩ g)).trans ((rmulEquiv P Γ ⟨γ, hγ⟩).tsum_eq _)

theorem cosetConv_mul_left (h : LeftInv (P ⊓ Γ) Φ) {γ : G} (hγ : γ ∈ Γ) : CosetConv P Γ Φ (γ * g) ↔ CosetConv P Γ Φ g := by
  rw [CosetConv, CosetConv, ← (rmulEquiv P Γ ⟨γ, hγ⟩).summable_iff (f := fun q => ‖term P Γ Φ g q‖)]
  exact summable_congr fun q => congrArg norm (term_mul_left h ⟨γ, hγ⟩ g q)

theorem cosetSum_mul_right (Φ : G → ℂ) (k g : G) : cosetSum P Γ (fun x => Φ (x * k)) g = cosetSum P Γ Φ (g * k) := by
  simp only [cosetSum, term, mul_assoc]

theorem cosetSum_eq_tsum (h : LeftInv (P ⊓ Γ) Φ) {ι : Type} {r : ι → Γ}
    (hr : Function.Bijective fun i => mk (P.subgroupOf Γ) (r i)) (g : G) : cosetSum P Γ Φ g = ∑' i, Φ (r i * g) :=
  ((Equiv.ofBijective _ hr).tsum_eq _).symm.trans (tsum_congr fun i => term_mk h g (r i))

theorem cosetConv_iff (h : LeftInv (P ⊓ Γ) Φ) {ι : Type} {r : ι → Γ}
    (hr : Function.Bijective fun i => mk (P.subgroupOf Γ) (r i)) : CosetConv P Γ Φ g ↔ Summable fun i => ‖Φ (r i * g)‖ :=
  (Equiv.ofBijective _ hr).summable_iff.symm.trans (summable_congr fun i => congrArg norm (term_mk h g (r i)))

theorem CosetConv.hasSum (h : CosetConv P Γ Φ g) : HasSum (term P Γ Φ g) (cosetSum P Γ Φ g) := h.of_norm.hasSum

theorem CosetConv.of_norm_le (h : CosetConv P Γ Ψ g) {C : ℝ} (e : ∀ x, ‖Φ x‖ ≤ C * ‖Ψ x‖) : CosetConv P Γ Φ g :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => e _) (h.mul_left C)

theorem CosetConv.add (h : CosetConv P Γ Φ g) (h' : CosetConv P Γ Ψ g) : CosetConv P Γ (Φ + Ψ) g :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _) (Summable.add h h')

theorem CosetConv.smul (h : CosetConv P Γ Φ g) (c : ℂ) : CosetConv P Γ (c • Φ) g :=
  h.of_norm_le fun x => (norm_smul c (Φ x)).le

theorem cosetSum_add (h : CosetConv P Γ Φ g) (h' : CosetConv P Γ Ψ g) :
    cosetSum P Γ (Φ + Ψ) g = cosetSum P Γ Φ g + cosetSum P Γ Ψ g := (h.hasSum.add h'.hasSum).tsum_eq

theorem cosetSum_smul (c : ℂ) (Φ : G → ℂ) (g : G) : cosetSum P Γ (c • Φ) g = c * cosetSum P Γ Φ g := tsum_mul_left

theorem cosetSum_of_le (e : Γ ≤ P) (h : LeftInv (P ⊓ Γ) Φ) (g : G) : CosetConv P Γ Φ g ∧ cosetSum P Γ Φ g = Φ g := by
  have hr : Function.Bijective fun _ : Unit => mk (P.subgroupOf Γ) 1 := ⟨fun _ _ _ => rfl, fun q =>
    Quotient.inductionOn q fun x => ⟨(), mk_eq_iff.2 ⟨⟨x, e x.2⟩, mul_one _⟩⟩⟩
  exact ⟨(cosetConv_iff h hr).2 .of_finite, by simpa using cosetSum_eq_tsum h hr g⟩

theorem cosetSum_indicator (g : G) : LeftInv (P ⊓ Γ) (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) ∧
    CosetConv P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) 1) g ∧
    cosetSum P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) 1) g = indicator (Γ : Set G) 1 g := by
  have h : LeftInv (P ⊓ Γ) (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) := fun γ hγ x => by
    classical simp only [indicator, SetLike.mem_coe, Subgroup.mul_mem_cancel_left _ hγ, Pi.one_apply]
  by_cases hg : g ∈ Γ
  · have h0 : ∀ q ≠ mk (P.subgroupOf Γ) 1, term P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) 1 q = 0 :=
      fun q => Quotient.inductionOn q fun x hx => (term_mk h 1 x).trans (indicator_of_notMem
        (fun e => hx (mk_eq_iff.2 ⟨⟨x, Subgroup.mem_subgroupOf.2 (by simpa using e.1)⟩, mul_one _⟩).symm) _)
    rw [← mul_one g, cosetConv_mul_left h hg, leftInv_cosetSum h g hg, mul_one, indicator_of_mem hg]
    refine ⟨h, summable_of_ne_finset_zero (s := {mk _ 1}) fun q hq => by rw [h0 q (by simpa using hq), norm_zero], ?_⟩
    rw [cosetSum, tsum_eq_single _ h0, term_mk h]
    exact indicator_of_mem (by simp) _
  · have h0 : term P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) g = 0 := funext fun q =>
      indicator_of_notMem (fun (e : ((q.out : Γ) : G) * g ∈ ((P ⊓ Γ : Subgroup G) : Set G)) =>
        hg ((Γ.mul_mem_cancel_left q.out.2).1 (show ((q.out : Γ) : G) * g ∈ P ∧ ((q.out : Γ) : G) * g ∈ Γ from e).2)) _
    rw [CosetConv, cosetSum, h0, indicator_of_notMem hg]
    exact ⟨h, by simpa using summable_zero, tsum_zero⟩

end Sums

theorem rpow_le_add {x a b t : ℝ} (hx : 0 < x) (h1 : a ≤ t) (h2 : t ≤ b) : x ^ t ≤ x ^ a + x ^ b := by
  rcases le_total x 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge hx h h1).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le h h2).trans (le_add_of_nonneg_left (by positivity))

theorem differentiable_npow {r : ℝ≥0} (hr : 0 < r) : Differentiable ℂ (npow r) := by
  rw [funext (npow_eq_exp hr)]; fun_prop

theorem analyticOnNhd_tsum_npow {ι : Type} {f : ι → ℂ} {a : ι → ℝ≥0} (ha : ∀ i, 0 < a i) {σ : ℝ} {s₀ : ℂ}
    (h : ∀ s : ℂ, σ < s.re → Summable fun i => ‖f i * npow (a i) (s - s₀)‖) :
    AnalyticOnNhd ℂ (fun s => ∑' i, f i * npow (a i) (s - s₀)) (rightOf σ) := fun s hs => by
  obtain ⟨τ, h1, h2⟩ := exists_between (mem_rightOf.1 hs)
  have ho : IsOpen {z : ℂ | τ < z.re ∧ z.re < s.re + 1} :=
    (isOpen_rightOf τ).inter (isOpen_lt Complex.continuous_re continuous_const)
  refine (Complex.differentiableOn_tsum_of_summable_norm ((h τ h1).add (h (s.re + 1 : ℝ) (by simp; linarith)))
    (fun i => ?_) ho fun i z hz => ?_).analyticAt (ho.mem_nhds ⟨h2, lt_add_one _⟩)
  · exact (((differentiable_npow (ha i)).comp (differentiable_id.sub_const s₀)).const_mul _).differentiableOn
  · simp only [norm_mul, norm_npow (ha i), ← mul_add, Complex.sub_re, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_left (rpow_le_add (ha i) (by linarith [hz.1]) (by linarith [hz.2])) (norm_nonneg _)

section Family

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P Γ K : Subgroup G} {δ : P →* ℝ≥0}
  {χ : P →* Circle} {ρ σ : ℝ} {Φ : ℂ → G → ℂ} (hI : IsIwasawa δ K) (hK : IsCompact (K : Set G))
  (hc : ContinuousOn (fun x : ℂ × G => Φ x.1 x.2) (rightOf σ ×ˢ univ)) (hl : ∀ s ∈ rightOf σ, IndLaw δ χ (s + ρ) (Φ s))
  (hs : ∀ τ, σ < τ → Summable fun q => ((term P Γ (iwAbs δ K) 1 q : ℝ≥0) : ℝ) ^ (τ + ρ))
include hI hK hc hl hs

theorem exists_majorant {S : Set ℂ} {C : Set G} (hS : IsCompact S) (hσ : S ⊆ rightOf σ) (hC : IsCompact C) :
    ∃ u : Cosets P Γ → ℝ, Summable u ∧ ∀ q, ∀ s ∈ S, ∀ g ∈ C, ‖term P Γ (Φ s) g q‖ ≤ u q := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, summable_zero, fun _ _ h => h.elim⟩
  obtain ⟨a, ha, h1⟩ := hS.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨b, hb, h2⟩ := hS.exists_isMaxOn hne Complex.continuous_re.continuousOn
  obtain ⟨M, hM⟩ := (hS.prod (hK.mul hC)).exists_bound_of_continuousOn (hc.mono (prod_mono hσ (subset_univ _)))
  refine ⟨_, ((hs _ (hσ ha)).add (hs _ (hσ hb))).mul_right M, fun q s h g hg => ?_⟩
  obtain ⟨p, k, hk, e⟩ := hI.1 (q.out : Γ)
  have h3 := hM (s, k * g) ⟨h, mul_mem_mul hk hg⟩
  simp only [term, e, mul_one, hI.iwAbs_mul p hk]
  rw [mul_assoc, hl s (hσ h), norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_npow (hom_pos δ p), Complex.add_re,
    Complex.ofReal_re]
  exact mul_le_mul (rpow_le_add (hom_pos δ p) (add_le_add_left (h1 h) _) (add_le_add_left (h2 h) _)) h3 (norm_nonneg _)
    (by positivity)

theorem cosetConv_of_spherical {s : ℂ} (h : σ < s.re) (g : G) : CosetConv P Γ (Φ s) g :=
  let ⟨_, hu, e⟩ := exists_majorant hI hK hc hl hs isCompact_singleton (singleton_subset_iff.2 h) (isCompact_singleton (x := g))
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => e q s rfl g rfl) hu

theorem continuousOn_cosetSum [WeaklyLocallyCompactSpace G] :
    ContinuousOn (fun x : ℂ × G => cosetSum P Γ (Φ x.1) x.2) (rightOf σ ×ˢ univ) := fun x hx => by
  obtain ⟨S, hS, h1, h2⟩ := local_compact_nhds ((isOpen_rightOf σ).mem_nhds hx.1)
  obtain ⟨C, hC, h3⟩ := exists_compact_mem_nhds x.2
  obtain ⟨u, hu, e⟩ := exists_majorant hI hK hc hl hs h2 h1 hC
  refine ((continuousOn_tsum (s := S ×ˢ C) (fun q => ?_) hu fun q y hy => e q _ hy.1 _ hy.2).continuousAt
    (prod_mem_nhds hS h3)).continuousWithinAt
  exact hc.comp (f := fun y : ℂ × G => (y.1, ((q.out : Γ) : G) * y.2)) (by fun_prop) fun y hy => ⟨h1 hy.1, trivial⟩

theorem analyticOnNhd_cosetSum (hd : ∀ g, DifferentiableOn ℂ (Φ · g) (rightOf σ)) (g : G) :
    AnalyticOnNhd ℂ (fun s => cosetSum P Γ (Φ s) g) (rightOf σ) := fun s h => by
  obtain ⟨S, hS, h1, h2⟩ := local_compact_nhds ((isOpen_rightOf σ).mem_nhds h)
  obtain ⟨u, hu, e⟩ := exists_majorant hI hK hc hl hs h2 h1 (isCompact_singleton (x := g))
  exact (Complex.differentiableOn_tsum_of_summable_norm hu (fun q => (hd _).mono (interior_subset.trans h1)) isOpen_interior
    fun q z hz => e q z (interior_subset hz) g rfl).analyticAt (interior_mem_nhds.2 hS)

end Family

end GlobalTheory.Eis

end
end
