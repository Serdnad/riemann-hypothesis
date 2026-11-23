module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle138
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle172
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

noncomputable section

namespace GlobalTheory.StableRange

open IsDedekindDomain NumberField

theorem exists_inv_mod_maximal {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (b : S) :
    ∃ y : S, ∀ m : Ideal S, m.IsMaximal → b ∈ m ∨ 1 - b * y ∈ m := by
  let I : Ideal S := (Ideal.jacobson (⊥ : Ideal B)).map (algebraMap B S)
  have hI : ∀ m : Ideal S, m.IsMaximal → I ≤ m := by
    intro m hm
    rw [Ideal.map_le_iff_le_comap]
    have : (m.comap (algebraMap B S)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) m
    exact sInf_le ⟨bot_le, this⟩
  have hp : ∀ p : Ideal S, p.IsPrime → I ≤ p → p.IsMaximal := by
    intro p hp hIp
    rw [Ideal.map_le_iff_le_comap] at hIp
    have hq : (p.comap (algebraMap B S)).IsPrime := Ideal.comap_isPrime _ _
    have hmax : (p.comap (algebraMap B S)).IsMaximal := by
      rw [Ideal.isMaximal_iff]
      refine ⟨(Ideal.ne_top_iff_one _).1 hq.ne_top, fun J x hJ hx hxJ => ?_⟩
      obtain ⟨y, hy⟩ := hB x
      have h1 : x * (1 - x * y) ∈ p.comap (algebraMap B S) :=
        hIp (Ideal.mem_jacobson_bot.2 hy)
      have h2 := (hq.mem_or_mem h1).resolve_left hx
      have := J.add_mem (hJ h2) (J.mul_mem_right y hxJ)
      simpa using this
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) p hmax
  let M : Submonoid S :=
    { carrier := {s | ∃ (n : ℕ) (y : S), s = b ^ n * (1 - b * y)}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, y, rfl⟩ ⟨k, w, rfl⟩
        exact ⟨n + k, y + w - b * y * w, by ring⟩ }
  by_cases hd : Disjoint (I : Set S) (M : Set S)
  · exfalso
    obtain ⟨p, hpp, hIp, hdis⟩ := Ideal.exists_le_prime_disjoint I M hd
    have hm := hp p hpp hIp
    have hb : b ∉ p := fun h => Set.disjoint_left.1 hdis h ⟨1, 0, by simp⟩
    obtain ⟨y, i, hi, hy⟩ := hm.exists_inv hb
    refine Set.disjoint_left.1 hdis hi ⟨0, y, ?_⟩
    rw [← hy]; ring
  · obtain ⟨s, hsI, n, y, rfl⟩ := Set.not_disjoint_iff.1 hd
    refine ⟨y, fun m hm => ?_⟩
    rcases hm.isPrime.mem_or_mem (hI m hm hsI) with h | h
    · exact Or.inl (hm.isPrime.mem_of_pow_mem n h)
    · exact Or.inr h

theorem stable_of_isIntegral {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (a b : S)
    (h : IsCoprime a b) : ∃ t : S, IsUnit (a + t * b) := by
  obtain ⟨y, hy⟩ := exists_inv_mod_maximal hB b
  obtain ⟨u, w, huw⟩ := h
  refine ⟨y * (1 - a), ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (a := a + y * (1 - a) * b) hn
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hy m hm with hb | hb
  · have e : (1 : S) = u * (a + y * (1 - a) * b) + (w - u * (y * (1 - a))) * b := by
      linear_combination -huw
    rw [e]
    exact m.add_mem (m.mul_mem_left _ hmem) (m.mul_mem_left _ hb)
  · have e : (1 : S) = (a + y * (1 - a) * b) + (1 - a) * (1 - b * y) := by ring
    rw [e]
    exact m.add_mem hmem (m.mul_mem_left _ hb)

theorem stable_of_subrings {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R]
    (hA : ∀ s : Finset A, ∃ B : Subring A, (s : Set A) ⊆ B ∧
      ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1))
    (a b : R) (h : IsCoprime a b) : ∃ t : R, IsUnit (a + t * b) := by
  classical
  obtain ⟨u, w, huw⟩ := h
  choose p hpm hp using fun r : R => (Algebra.IsIntegral.isIntegral (R := A) r)
  obtain ⟨B, hs, hB⟩ := hA ((p a).coeffs ∪ (p b).coeffs ∪ (p u).coeffs ∪ (p w).coeffs)
  have key : ∀ r : R, ((p r).coeffs : Set A) ⊆ B → IsIntegral B r := by
    intro r hr
    refine ⟨(p r).toSubring B hr, (Polynomial.monic_toSubring _ _ hr).2 (hpm r), ?_⟩
    have e : algebraMap B R = (algebraMap A R).comp B.subtype := rfl
    rw [e, ← Polynomial.eval₂_map, Polynomial.map_toSubring]
    exact hp r
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  obtain ⟨t, ht⟩ := stable_of_isIntegral (S := integralClosure B R) hB ⟨a, key a h1⟩ ⟨b, key b h2⟩
    ⟨⟨u, key u h3⟩, ⟨w, key w h4⟩, Subtype.ext huw⟩
  exact ⟨t, ht.map (integralClosure B R).val⟩

variable (K : Type*) [Field K] [NumberField K]

def intOutside (T : Set (HeightOneSpectrum (𝓞 K))) : Subring (AdeleRing (𝓞 K) K) where
  carrier := {x | ∀ v ∉ T, x.2 v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v hv := mul_mem (ha v hv) (hb v hv)
  one_mem' v _ := one_mem (v.adicCompletionIntegers K)
  add_mem' ha hb v hv := add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := zero_mem (v.adicCompletionIntegers K)
  neg_mem' ha v hv := neg_mem (ha v hv)

def mkAdele {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (f : ∀ w : InfinitePlace K, w.Completion) (g : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hg : ∀ v ∉ T, g v ∈ v.adicCompletionIntegers K) : intOutside K T :=
  ⟨(f, ⟨g, hT.subset fun v hv => by
    by_contra h
    exact hv (hg v h)⟩), hg⟩

theorem isUnit_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) (x : intOutside K T)
    (h1 : ∀ w, x.1.1 w ≠ 0) (h2 : ∀ v, x.1.2 v ≠ 0) (h3 : ∀ v ∉ T, Valued.v (x.1.2 v) = 1) :
    IsUnit x := by
  refine IsUnit.of_mul_eq_one (mkAdele K hT (fun w => (x.1.1 w)⁻¹) (fun v => (x.1.2 v)⁻¹)
    fun v hv => ?_) ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h3 v hv, inv_one]
  · refine Subtype.ext (Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_))
    · exact mul_inv_cancel₀ (h1 w)
    · exact mul_inv_cancel₀ (h2 v)

theorem mul_one_sub_mul_inv {L : Type*} [Field L] (x : L) : x * (1 - x * x⁻¹) = 0 := by
  by_cases h : x = 0
  · simp [h]
  · simp [h]

open Classical in
theorem regular_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (x : intOutside K T) :
    ∃ y : intOutside K T, ∀ z : intOutside K T, IsUnit (x * (1 - x * y) * z + 1) := by
  refine ⟨mkAdele K hT (fun w => (x.1.1 w)⁻¹)
    (fun v => if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0) fun v hv => ?_, fun z => ?_⟩
  · split_ifs with h
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h.resolve_left hv, inv_one]
    · exact zero_mem _
  · have hv : ∀ v, Valued.v (x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1) = 1 := by
      intro v
      split_ifs with h
      · rw [mul_one_sub_mul_inv]; simp
      · obtain ⟨hT', h1⟩ := not_or.1 h
        have hx : Valued.v (x.1.2 v) ≤ 1 := x.2 v hT'
        have hz : Valued.v (z.1.2 v) ≤ 1 := z.2 v hT'
        rw [mul_zero, sub_zero, mul_one, add_comm]
        apply Valuation.map_one_add_of_lt
        rw [map_mul]
        exact (mul_le_of_le_one_right' hz).trans_lt (lt_of_le_of_ne hx h1)
    refine isUnit_intOutside K hT _ (fun w => ?_) (fun v => ?_) (fun v _ => hv v)
    · change x.1.1 w * (1 - x.1.1 w * (x.1.1 w)⁻¹) * z.1.1 w + 1 ≠ 0
      rw [mul_one_sub_mul_inv]; simp
    · intro h0
      have h1 := hv v
      have h2 : x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1 = 0 := h0
      rw [h2] at h1
      simp at h1

theorem stable_adele {R : Type*} [CommRing R] [Algebra (AdeleRing (𝓞 K) K) R]
    [Algebra.IsIntegral (AdeleRing (𝓞 K) K) R] (a b : R) (h : IsCoprime a b) :
    ∃ t : R, IsUnit (a + t * b) := by
  refine stable_of_subrings (A := AdeleRing (𝓞 K) K) (fun s => ?_) a b h
  have hT : (⋃ x ∈ (s : Set (AdeleRing (𝓞 K) K)),
      {v : HeightOneSpectrum (𝓞 K) | x.2 v ∉ v.adicCompletionIntegers K}).Finite :=
    s.finite_toSet.biUnion fun x _ => x.2.2
  refine ⟨intOutside K _, fun x hx v hv => ?_, regular_intOutside K hT⟩
  by_contra h
  exact hv (Set.mem_biUnion hx h)

end GlobalTheory.StableRange

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem GlobalTheory.StableRange.adeles_stableRange_one :
    ∀ (D : D7) (a b : AE D), IsCoprime a b → ∃ t : AE D, IsUnit (a + t * b) :=
  fun D a b h => GlobalTheory.StableRange.stable_adele D.host.F a b h
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.RationalSubgroupFund

theorem countable_discrete_exists_fundamentalDomain : ∀ (D : D7) (W : HSp D) (Γ : Subgroup (GA D W)), Γ ≤ GQ W → Countable Γ ∧ DiscreteTopology Γ ∧ ∀ μ : Measure (GA D W), μ.IsHaarMeasure → ∃ 𝓑 : Set (GA D W), IsFundamentalDomain Γ 𝓑 μ := by
  intro D W Γ hΓ
  obtain ⟨_, h2, _, h4, h5, h6, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := h2; haveI := h4; haveI := h5; haveI := h6
  haveI hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨(x : GA D W), hΓ x.2⟩ : GQ W))
      (continuous_subtype_val.subtype_mk _)
      (fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy))
  obtain ⟨hc, 𝓓, h𝓓m, h𝓓⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  haveI := hc
  refine ⟨hc, hdisc, fun μ _ => ⟨𝓓, ?_⟩⟩
  exact IsFundamentalDomain.mk' h𝓓m.nullMeasurableSet (fun g => h𝓓 g)

end GlobalTheory.RationalSubgroupFund
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.CutSum

open Filter Topology

theorem measurable_tsum_of_summable {X I : Type} [MeasurableSpace X] [Countable I]
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) (hs : ∀ x, Summable fun i => F i x) :
    Measurable fun x => ∑' i, F i x :=
  measurable_of_tendsto_metrizable' (atTop : Filter (Finset I))
    (f := fun s x => ∑ i ∈ s, F i x) (fun s => Finset.measurable_sum s fun i _ => hF i)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum)

theorem summable_of_tsum_enorm_ne_top {I : Type} (f : I → ℂ) (h : ∑' i, ‖f i‖ₑ ≠ ⊤) :
    Summable f := by
  refine Summable.of_norm ?_
  simp only [enorm_eq_nnnorm] at h
  exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h)

theorem integrableOn_of_enorm_le {X : Type} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (hs : μ s ≠ ⊤) {φ : X → ℂ} (hφ : Measurable φ) (B : NNReal) (hb : ∀ x, ‖φ x‖ₑ ≤ B) :
    IntegrableOn φ s μ := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  show ∫⁻ x in s, ‖φ x‖ₑ ∂μ < ⊤
  exact (lintegral_mono hb).trans_lt
    ((setLIntegral_const s _).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hs.lt_top))

end GlobalTheory.CutSum


open GlobalTheory.CutSum in
theorem GlobalTheory.CutSum.integral_tsum_eq_zero : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ M : Subgroup N), Countable Γ → DiscreteTopology Γ → M.Normal → IsClosed (M : Set N) → (∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ Γ.subgroupOf M, ∃ k ∈ K, m = γ * k) → ∀ 𝓝 : Set N, IsFundamentalDomain Γ 𝓝 ν → ν 𝓝 ≠ ⊤ → ∀ (I C : Type) [Countable I] (κ : I → C) (F : I → N → ℂ), (∀ i, Measurable (F i)) → (∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B) → (∀ γ ∈ Γ, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n) → (∀ c, ∀ γ ∈ Γ, γ ∈ M → ∀ n, ∑' i : {i // κ i = c}, F i (γ * n) = ∑' i : {i // κ i = c}, F i n) → (∀ c, ∃ u ∈ M, ∃ a : ℂ, a ≠ 1 ∧ ∀ i, κ i = c → ∀ m ∈ M, ∀ n, F i (m * u * n) = a * F i (m * n)) → ∫ n in 𝓝, ∑' i, F i n ∂ν = 0 := by
  intro N _ _ _ _ _ _ _ _ ν _ Γ M hΓc hΓd hMn hMc hK 𝓝 h𝓝 h𝓝fin I C _ cl F hFm hB hΓ hcl heig
  classical
  haveI := hΓd
  haveI : LocallyCompactSpace M := hMc.locallyCompactSpace
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace M := Subtype.borelSpace _
  obtain ⟨B, hB⟩ := hB

  have hinj : Function.Injective fun γ : Γ.subgroupOf M =>
      (⟨(γ : M), Subgroup.mem_subgroupOf.1 γ.2⟩ : Γ) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : Γ => (x : N)) h))
  haveI : Countable (Γ.subgroupOf M) := hinj.countable
  haveI : DiscreteTopology (Γ.subgroupOf M) := DiscreteTopology.of_continuous_injective
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  let μM : Measure M := Measure.haar
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf M)
  have hDf : μM D ≠ ⊤ := by
    obtain ⟨K, hKc, hKcov⟩ := hK
    refine ne_top_of_le_ne_top hKc.measure_lt_top.ne
      (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hD μM) (D' := K)
        (Filter.Eventually.of_forall fun m => ?_))
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hKcov m
    refine ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    show ((⟨γ, hγ⟩⁻¹ : Γ.subgroupOf M) : M) * (γ * k) ∈ K
    rw [Subgroup.coe_inv, Subgroup.coe_mk, inv_mul_cancel_left]
    exact hk
  have hR : ∀ u : M, μM.map (· * u) = μM :=
    GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain N Γ M hΓc hMc μM D inferInstance (hD μM) hDf

  have hs : ∀ n, Summable fun i => F i n := fun n =>
    summable_of_tsum_enorm_ne_top _ (ne_top_of_le_ne_top ENNReal.coe_ne_top (hB n))
  let g : I → Set.range cl := Set.rangeFactorization cl
  haveI : Countable (Set.range cl) := (Set.countable_range cl).to_subtype
  let G : Set.range cl → N → ℂ := fun c n => ∑' i : {i // cl i = c.1}, F i n
  have hfib : ∀ c n, ∑' b : ↑(g ⁻¹' {c}), F b n = G c n := fun c n =>
    (Equiv.subtypeEquivRight (fun i => by
      simp [g, Set.rangeFactorization, Subtype.ext_iff])).tsum_eq
      (fun j : {i // cl i = c.1} => F j.1 n)
  have hsplit : ∀ n, ∑' i, F i n = ∑' c, G c n := fun n =>
    (((hs n).hasSum.tsum_fiberwise g).tsum_eq).symm.trans (tsum_congr fun c => hfib c n)
  have hGle : ∀ n, ∑' c, ‖G c n‖ₑ ≤ B := fun n => by
    calc ∑' c, ‖G c n‖ₑ ≤ ∑' c, ∑' b : ↑(g ⁻¹' {c}), ‖F b n‖ₑ :=
          ENNReal.tsum_le_tsum fun c => by rw [← hfib c n]; exact enorm_tsum_le_tsum_enorm
      _ = ∑' i, ‖F i n‖ₑ := ENNReal.tsum_fiberwise (fun i => ‖F i n‖ₑ) g
      _ ≤ B := hB n
  have hGm : ∀ c, Measurable (G c) := fun c =>
    measurable_tsum_of_summable (fun i : {i // cl i = c.1} => F i) (fun i => hFm i)
      (fun n => (hs n).comp_injective Subtype.val_injective)
  have hfm : Measurable fun n => ∑' i, F i n := measurable_tsum_of_summable F hFm hs

  have hzero : ∀ c (h : N), ∫ m in D, G c ((m : N) * h) ∂μM = 0 := by
    intro c h
    obtain ⟨u, huM, a, ha1, hu⟩ := heig c.1
    set φ : M → ℂ := fun m => G c ((m : N) * h) with hφ
    have hφm : Measurable φ := (hGm c).comp (measurable_subtype_coe.mul_const h)
    have hφint : IntegrableOn φ D μM :=
      integrableOn_of_enorm_le hDf hφm B fun m => (ENNReal.le_tsum c).trans (hGle _)
    have hinv : ∀ γ ∈ Γ.subgroupOf M, ∀ m : M, φ (γ * m) = φ m := by
      intro γ hγ m
      show G c (((γ * m : M) : N) * h) = G c ((m : N) * h)
      rw [Subgroup.coe_mul, mul_assoc]
      exact hcl c.1 γ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _
    have hshift : ∀ m : M, φ (m * ⟨u, huM⟩) = a * φ m := by
      intro m
      show G c (((m * ⟨u, huM⟩ : M) : N) * h) = a * G c ((m : N) * h)
      rw [Subgroup.coe_mul, Subgroup.coe_mk]
      show ∑' i : {i // cl i = c.1}, F i ((m : N) * u * h)
        = a * ∑' i : {i // cl i = c.1}, F i ((m : N) * h)
      rw [← tsum_mul_left]
      exact tsum_congr fun i => hu i i.2 m m.2 h
    have key := (GlobalTheory.fundamentalDomain_setIntegral_mul_right (Γ.subgroupOf M) μM D (hD μM)
      ⟨u, huM⟩ (hR _) φ hinv hφint).2
    simp only [hshift, integral_const_mul] at key
    have h2 : (a - 1) * ∫ m in D, φ m ∂μM = 0 := by rw [sub_mul, one_mul, key, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha1)

  have hmean : ∀ h : N, ∫ m in D, (∑' i, F i ((m : N) * h)) ∂μM = 0 := by
    intro h
    have hm : ∀ c, Measurable fun m : M => G c ((m : N) * h) := fun c =>
      (hGm c).comp (measurable_subtype_coe.mul_const h)
    simp_rw [hsplit]
    rw [integral_tsum (fun c => (hm c).aestronglyMeasurable) ?_]
    · simp [hzero]
    · rw [← lintegral_tsum (fun c => (hm c).enorm.aemeasurable)]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := B)) hDf) ?_
      exact (lintegral_mono fun m => hGle _).trans_eq (setLIntegral_const D _)
  have hfin := GlobalTheory.UnfoldNormal.unfold_zero_mean N ν Γ M hΓc hMc
    (fun γ _ n hn => hMn.conj_mem n hn γ) μM D inferInstance (hD μM) hDf
    (fun _ => 1) (fun n => ∑' i, F i n) measurable_const hfm (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun γ hγ n => hΓ γ hγ n) hmean 𝓝 h𝓝
    (integrableOn_of_enorm_le h𝓝fin (measurable_const.mul hfm) B fun n => by
      simpa using enorm_tsum_le_tsum_enorm.trans (hB n))
  simpa using hfin
end
