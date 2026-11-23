module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
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

@[expose] public section

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem padicCoeff_exists_pow_smul_mem_one :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O],
    PadicCoeff p O → ∀ y : FractionRing O,
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := by
  intro p O _ _ _ _ hP y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ϖ ∣ (p : O) := by
    have h := hP.p_mem
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h
    exact h
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) y
  dsimp only
  have hb : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hbk : (b : O) ∣ (p : O) ^ k := by
    rw [hu]
    exact (Units.mul_left_dvd).mpr (pow_dvd_pow_of_dvd hdvd k)
  obtain ⟨c, hc⟩ := hbk
  refine ⟨k, ?_⟩
  rw [Submodule.mem_comap, LinearMap.lsmul_apply, Submodule.mem_one]
  refine ⟨c * a, ?_⟩
  rw [Algebra.smul_def, hc, map_mul, map_mul, mul_assoc, mul_left_comm, IsLocalization.mk'_spec']

end GlobalTheory
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem h2_twist_exists_of_iUnion_open : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    (ε : G →* Oˣ) {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ z : H2 (twist ε M), ∃ n, ∃ z' : H2 (twist ε (N n)),
      mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype) z' = z := by
  intro O _ _ G _ _ _ ε M _ _ _ _ _ N hmono hopen hcov z
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hK : IsCompact (Set.range f.1) := isCompact_range f.2.1
  have hmono' : Monotone (fun n => (N n : Set M)) := fun a b h => SetLike.coe_subset_coe.mpr (hmono h)
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => (N n : Set M)) hopen
    (fun x _ => Set.mem_iUnion.mpr (hcov x)) hmono'.directed_le
  let f' : G × G → N n := fun x => ⟨f.1 x, hn ⟨x, rfl⟩⟩
  have hc : Continuous f' := f.2.1.subtype_mk _
  have hcoc : f' ∈ Z2 (twist ε (N n)) := by
    refine ⟨hc, fun g h k => ?_⟩
    apply Subtype.ext
    have e := f.2.2 g h k
    have key : ∀ x : N n, ((twist ε (N n) g x : N n) : M) = twist ε M g (x : M) := fun x => rfl
    simpa [f', key] using e
  refine ⟨n, Submodule.Quotient.mk ⟨f', hcoc⟩, ?_⟩
  rfl

end GlobalTheory
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem map_H2_subtype_injective_of_union : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ (hfg : ∀ n, IsFGTop O (N n)) (n : ℕ),
      Function.Injective (mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)) := by
  intro O _ _ G _ _ _ ε Θ M _ _ _ _ _ N hmono hopen hcov hfg n
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | H f =>
  unfold mapH2 at hz
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hz

  have hK : IsCompact (Set.range c) := isCompact_range hc
  obtain ⟨i, hi⟩ := hK.elim_directed_cover (fun k => (N k : Set M)) hopen
    (fun x _ => Set.mem_iUnion.2 (hcov x)) (hmono.directed_le)
  set m := max n i with hm
  have hnm : N n ≤ N m := hmono (le_max_left n i)
  have him : ∀ g, c g ∈ N m := fun g => hmono (le_max_right n i) (hi ⟨g, rfl⟩)
  have hincl : Continuous (Submodule.inclusion hnm) := continuous_inclusion hnm
  have hzero : mapH2 (twist ε (N n)) (twist ε (N m)) (Submodule.inclusion hnm) hincl
      (twist_map ε (Submodule.inclusion hnm)) (Submodule.Quotient.mk f) = 0 := by
    unfold mapH2
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => ⟨c g, him g⟩, hc.subtype_mk him, ?_⟩
    funext p
    apply Subtype.ext
    have e := congrFun hcf p
    simp [d1, twist] at e ⊢
    rw [e]
    rfl
  have hnat := Θ.nat (N n) (N m) (hfg n) (hfg m) (Submodule.inclusion hnm) hincl (Submodule.Quotient.mk f)
  rw [hzero, map_zero] at hnat
  have h0 : Θ.θ (N n) (hfg n) (Submodule.Quotient.mk f) = 0 := by
    have := hnat.symm
    rw [← (Submodule.inclusion hnm).map_zero] at this
    exact Submodule.inclusion_injective hnm this
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

end GlobalTheory
end
