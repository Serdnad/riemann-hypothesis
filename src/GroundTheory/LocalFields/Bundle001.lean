module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Quotient
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Fintype.Defs
import Mathlib.RepresentationTheory.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section Basics

variable {G : Type*} [Group G]

variable [Fintype G]

end Basics

section IndFunMore

variable {G H H' : Type*} [Group G] [Group H] [Group H'] [Fintype G] [Fintype H] [Fintype H']

end IndFunMore

section Conj

variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]

def conjNormal (g : G) : A ≃* A where
  toFun a := ⟨g⁻¹ * a * g, by simpa using hA.conj_mem a a.2 g⁻¹⟩
  invFun a := ⟨g * a * g⁻¹, hA.conj_mem a a.2 g⟩
  left_inv a := by
    ext
    simp [mul_assoc]
  right_inv a := by
    ext
    simp [mul_assoc]
  map_mul' a b := by
    ext
    simp [mul_assoc]

theorem conjNormal_mul (g h : G) (a : A) :
    conjNormal A (g * h) a = conjNormal A h (conjNormal A g a) := by
  apply Subtype.ext
  change (g * h)⁻¹ * (a : G) * (g * h) = h⁻¹ * (g⁻¹ * (a : G) * g) * h
  simp [mul_assoc]

theorem conjNormal_one (a : A) : conjNormal A 1 a = a := by
  apply Subtype.ext
  change (1 : G)⁻¹ * (a : G) * 1 = (a : G)
  simp

def inertia (θ : A → ℂ) : Subgroup G where
  carrier := {g | ∀ a, θ (conjNormal A g a) = θ a}
  one_mem' := by
    intro a
    rw [conjNormal_one]
  mul_mem' {g h} hg hh := by
    intro a
    rw [conjNormal_mul, hh, hg]
  inv_mem' {g} hg := by
    intro a
    calc θ (conjNormal A g⁻¹ a) = θ (conjNormal A g (conjNormal A g⁻¹ a)) := (hg _).symm
      _ = θ a := by rw [← conjNormal_mul, inv_mul_cancel, conjNormal_one]


end Conj

section Clifford

variable {G : Type*} [Group G] [Fintype G] {A : Subgroup G} [A.Normal]


end Clifford

end GroundTheory.LocalField
end
end

section

namespace GroundTheory.LocalField

open Filter Topology Uniformity

section Filtration

variable {G : Type*} [Group G]

@[to_additive AddFiltrationCauchy
]
def FiltrationCauchy (F : ℕ → Subgroup G) (x : ℕ → G) : Prop :=
  ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, x n / x m ∈ F N

@[to_additive AddFiltrationTendsto
]
def FiltrationTendsto (F : ℕ → Subgroup G) (x : ℕ → G) (y : G) : Prop :=
  ∀ N, ∃ M, ∀ n ≥ M, x n / y ∈ F N

@[to_additive AddFiltrationComplete
]
def FiltrationComplete (F : ℕ → Subgroup G) : Prop :=
  ∀ x : ℕ → G, FiltrationCauchy F x → ∃ y, FiltrationTendsto F x y

@[to_additive AddFiltrationSeparated
]
def FiltrationSeparated (F : ℕ → Subgroup G) : Prop :=
  ∀ g : G, (∀ n, g ∈ F n) → g = 1

end Filtration

section Surjectivity

variable {G H : Type*} [Group G] [Group H]

@[to_additive map_eq_of_graded_surjective_add
]
theorem map_eq_of_graded_surjective {F : ℕ → Subgroup G} {E : ℕ → Subgroup H}
    (hF : Antitone F) (hE : Antitone E) (hG : FiltrationComplete F)
    (hH : FiltrationSeparated E) (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (k : ℕ) (hmap : ∀ n, k ≤ n → ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, k ≤ n → ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    (F k).map f = E (φ k) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact hmap k le_rfl g hg
  intro h hh
  rw [Subgroup.mem_map]
  have hs : ∀ (n : ℕ) (a : H), ∃ g : G,
      k ≤ n → a ∈ E (φ n) → g ∈ F n ∧ a / f g ∈ E (φ (n + 1)) := by
    intro n a
    by_cases hc : k ≤ n ∧ a ∈ E (φ n)
    · obtain ⟨g, hg1, hg2⟩ := hgr n hc.1 a hc.2
      exact ⟨g, fun _ _ => ⟨hg1, hg2⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose s hs using hs

  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → H, r 0 = h ∧ ∀ j, r (j + 1) = r j / f (s (k + j) (r j)) :=
    ⟨fun j => Nat.rec h (fun j rj => rj / f (s (k + j) rj)) j, rfl, fun _ => rfl⟩
  have hrE : ∀ j, r j ∈ E (φ (k + j)) := by
    intro j
    induction j with
    | zero => simpa [hr0] using hh
    | succ j ih =>
      rw [hrs, ← add_assoc]
      exact (hs (k + j) (r j) (Nat.le_add_right k j) ih).2

  obtain ⟨D, hD⟩ : ∃ D : ℕ → G, ∀ j, D j = s (k + j) (r j) := ⟨_, fun _ => rfl⟩
  have hDF : ∀ j, D j ∈ F (k + j) := fun j => by
    rw [hD]
    exact (hs (k + j) (r j) (Nat.le_add_right k j) (hrE j)).1
  have hrs' : ∀ j, r (j + 1) = r j / f (D j) := fun j => by rw [hrs, hD]

  obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → G, x 0 = D 0 ∧ ∀ j, x (j + 1) = D (j + 1) * x j :=
    ⟨fun j => Nat.rec (D 0) (fun j xj => D (j + 1) * xj) j, rfl, fun _ => rfl⟩
  have hxr : ∀ j, h / f (x j) = r (j + 1) := by
    intro j
    induction j with
    | zero => rw [hx0, hrs', hr0]
    | succ j ih =>
      rw [hxs, hrs' (j + 1), ← ih, map_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  have hxF : ∀ m d, x (m + d) / x m ∈ F (k + m + 1) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : x (m + (d + 1)) / x m = D (m + d + 1) * (x (m + d) / x m) := by
        rw [← add_assoc, hxs, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      rw [e]
      exact (F _).mul_mem (hF (by omega) (hDF (m + d + 1))) ih
  have hC : FiltrationCauchy F x := by
    intro N
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total m n with hmn | hnm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact hF (by omega) (hxF m d)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have e := (F _).inv_mem (hxF n d)
      rw [inv_div] at e
      exact hF (by omega) e
  have hxk : ∀ j, x j ∈ F k := by
    intro j
    induction j with
    | zero => rw [hx0]; simpa using hDF 0
    | succ j ih => rw [hxs]; exact (F k).mul_mem (hF (by omega) (hDF (j + 1))) ih
  obtain ⟨y, hy⟩ := hG x hC
  obtain ⟨M0, hM0⟩ := hy k
  have hyk : y ∈ F k := by
    have e : (x M0 / y)⁻¹ * x M0 = y := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [← e]
    exact (F k).mul_mem ((F k).inv_mem (hM0 M0 le_rfl)) (hxk M0)
  refine ⟨y, hyk, ?_⟩
  have h1 : h / f y = 1 := by
    apply hH
    intro m
    obtain ⟨N0, hN0⟩ := Filter.tendsto_atTop_atTop.mp hφ m
    obtain ⟨M, hM⟩ := hy (max N0 k)
    have e : h / f y = r (max M N0 + 1) * f (x (max M N0) / y) := by
      rw [← hxr (max M N0), map_div]
      simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
    rw [e]
    refine (E m).mul_mem ?_ ?_
    · exact hE (hN0 _ (by omega)) (hrE (max M N0 + 1))
    · exact hE (hN0 _ (le_max_left _ _))
        (hmap _ (le_max_right _ _) _ (hM (max M N0) (le_max_left _ _)))
  exact (div_eq_one.mp h1).symm

@[to_additive surjective_of_graded_surjective_add
]
theorem surjective_of_graded_surjective {F : ℕ → Subgroup G} {E : ℕ → Subgroup H}
    (hF : Antitone F) (hE : Antitone E) (hG : FiltrationComplete F)
    (hH : FiltrationSeparated E) (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hF0 : F 0 = ⊤) (hE0 : E (φ 0) = ⊤) (hmap : ∀ n, ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    Function.Surjective f := by
  intro h
  have e := map_eq_of_graded_surjective hF hE hG hH f hφ 0 (fun n _ => hmap n)
    (fun n _ => hgr n)
  have hh : h ∈ E (φ 0) := by rw [hE0]; exact Subgroup.mem_top h
  rw [← e, hF0] at hh
  obtain ⟨g, -, rfl⟩ := hh
  exact ⟨g, rfl⟩

end Surjectivity

section Topological

end Topological

end GroundTheory.LocalField
end

section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Base

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

@[instance_reducible]
def normedField : NontriviallyNormedField K :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

theorem normedField_norm_le_norm_iff (x y : K) :
    letI := normedField K
    ‖x‖ ≤ ‖y‖ ↔ x ≤ᵥ y := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  let : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  rw [(valuation K).vle_iff_le]
  exact Valued.toNormedField.norm_le_iff

theorem normedField_isUltrametricDist :
    letI := normedField K
    IsUltrametricDist K := by
  let := normedField K
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => ?_
  rcases vle_add_cases x y with h | h
  · exact ((normedField_norm_le_norm_iff K _ _).2 h).trans (le_max_left _ _)
  · exact ((normedField_norm_le_norm_iff K _ _).2 h).trans (le_max_right _ _)

theorem normedField_completeSpace :
    letI := normedField K
    CompleteSpace K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact (inferInstance : CompleteSpace K)

theorem normedField_properSpace :
    letI := normedField K
    ProperSpace K := by
  let := normedField K
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K

end Base

section Extension

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

@[instance_reducible]
def spectralNormedField : NontriviallyNormedField L :=
  letI := normedField K
  haveI := normedField_isUltrametricDist K
  haveI := normedField_completeSpace K
  spectralNorm.nontriviallyNormedField K L

theorem spectralNormedField_isUltrametricDist :
    letI := spectralNormedField K L
    IsUltrametricDist L := by
  let := normedField K
  have := normedField_isUltrametricDist K
  have := normedField_completeSpace K
  let := spectralNormedField K L
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := L))

theorem spectralNormedField_norm_algebraMap (a : K) :
    letI := normedField K
    letI := spectralNormedField K L
    ‖algebraMap K L a‖ = ‖a‖ := by
  let := normedField K
  exact spectralNorm_extends a

structure LocalFieldStructure (L : Type*) [Field L] where

  rel : ValuativeRel L

  top : TopologicalSpace L

@[instance_reducible]
def finiteExtensionStructure : LocalFieldStructure L :=
  letI := spectralNormedField K L
  haveI := spectralNormedField_isUltrametricDist K L
  { rel := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    top := inferInstance }

theorem finiteExtensionStructure_vle_iff (x y : L) :
    letI := normedField K
    letI := spectralNormedField K L
    letI := (finiteExtensionStructure K L).rel
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

theorem finiteExtensionStructure_valuativeExtension :
    letI := (finiteExtensionStructure K L).rel
    ValuativeExtension K L := by
  let := (finiteExtensionStructure K L).rel
  constructor
  intro a b
  rw [finiteExtensionStructure_vle_iff, spectralNormedField_norm_algebraMap,
    spectralNormedField_norm_algebraMap, normedField_norm_le_norm_iff]

theorem finiteExtensionStructure_isNonarchimedeanLocalField :
    letI := (finiteExtensionStructure K L).rel
    letI := (finiteExtensionStructure K L).top
    IsNonarchimedeanLocalField L := by
  let := normedField K
  have := normedField_isUltrametricDist K
  have := normedField_completeSpace K
  have := normedField_properSpace K
  let := spectralNormedField K L
  have := spectralNormedField_isUltrametricDist K L
  let := (finiteExtensionStructure K L).rel
  have hc : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := ?_, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
      (fun {s} => (NormedField.toValued (K := L)).is_topological_valuation s)
  · let : NormedSpace K L := spectralNorm.normedSpace K L
    have : ProperSpace L := FiniteDimensional.proper K L
    infer_instance
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := L))]
    infer_instance

theorem exists_isNonarchimedeanLocalField_valuativeExtension :
    ∃ (_ : ValuativeRel L) (_ : TopologicalSpace L),
      IsNonarchimedeanLocalField L ∧ ValuativeExtension K L :=
  ⟨(finiteExtensionStructure K L).rel, (finiteExtensionStructure K L).top,
    finiteExtensionStructure_isNonarchimedeanLocalField K L,
    finiteExtensionStructure_valuativeExtension K L⟩

end Extension

end GroundTheory.LocalField
end
end

section

namespace GroundTheory.LocalField

section Completion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

def openFiniteIndex : Set (Subgroup G) :=
  {H | IsOpen (H : Set G) ∧ H.FiniteIndex}


variable {G} in
def quotientMapOfLE {H H' : Subgroup G} (h : H ≤ H') : G ⧸ H →* G ⧸ H' :=
  QuotientGroup.map H H' (MonoidHom.id G) h


def openCompletion : Subgroup (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) where
  carrier := {a | ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H'}
  one_mem' := fun H H' h => by simp
  mul_mem' := fun ha hb H H' h => by simp [map_mul, ha H H' h, hb H H' h]
  inv_mem' := fun ha H H' h => by simp [map_inv, ha H H' h]

namespace openCompletion

variable {G}






theorem discreteTopology_quotient (H : openFiniteIndex G) : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
  QuotientGroup.discreteTopology H.2.1

end openCompletion

end Completion

end GroundTheory.LocalField
end
