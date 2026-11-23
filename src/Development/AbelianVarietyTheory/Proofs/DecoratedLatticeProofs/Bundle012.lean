module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.Klein

private theorem ultra_add_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K} {C : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x + y‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

private theorem mul_le_of {K : Type*} [NormedField K] {x y : K} {C D : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ D) : ‖x * y‖ ≤ C * D := by
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

private theorem cubic_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x k₂ k₁ k₀ : K} {ρ : ℝ}
    (h2 : ‖(2 : K)‖ = 1) (hρ : 1 ≤ ρ) (hx : ‖x‖ ≤ ρ) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1) :
    ‖2 * 2 * (x * x * x) + k₂ * (x * x) + k₁ * x + k₀‖ ≤ ρ * ρ * ρ := by
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  refine ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_
  · simpa using mul_le_of (mul_le_of h2.le h2.le) (mul_le_of (mul_le_of hx hx) hx)
  · exact (mul_le_of hk₂ (mul_le_of hx hx)).trans (by nlinarith)
  · exact (mul_le_of hk₁ hx).trans (by nlinarith)
  · exact hk₀.trans (by nlinarith)

private theorem le_of_mul_self_le_mul_self' {x y : ℝ} (h : x * x ≤ y * y) (hy : 0 ≤ y) : x ≤ y :=
  (abs_le_of_sq_le_sq' (by simpa only [sq] using h) hy).2

theorem chord_norm_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {a b A B X k₂ k₁ k₀ : K}
    (h2 : ‖(2 : K)‖ = 1) (ha : 1 < ‖a‖) (hb : ‖b‖ ≤ 1) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1)
    (hA : A ^ 2 = 4 * a ^ 3 + k₂ * a ^ 2 + k₁ * a + k₀)
    (hB : B ^ 2 = 4 * b ^ 3 + k₂ * b ^ 2 + k₁ * b + k₀)
    (hX : 4 * (a - b) ^ 2 * X = (A - B) ^ 2 - (4 * (a + b) + k₂) * (a - b) ^ 2) : ‖X‖ ≤ 1 := by
  set ρ := ‖a‖ with hρ
  have haa : ‖a‖ ≤ ρ := le_rfl
  have hab : ‖a - b‖ = ρ := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; linarith),
      norm_neg, max_eq_left (by linarith)]
  have hA' : ‖A‖ * ‖A‖ ≤ ρ * ρ * ρ := by
    rw [← norm_mul, show A * A = 2 * 2 * (a * a * a) + k₂ * (a * a) + k₁ * a + k₀ by
      linear_combination hA]
    exact cubic_le h2 ha.le haa hk₂ hk₁ hk₀
  have hB' : ‖B‖ * ‖B‖ ≤ 1 * 1 * 1 := by
    rw [← norm_mul, show B * B = 2 * 2 * (b * b * b) + k₂ * (b * b) + k₁ * b + k₀ by
      linear_combination hB]
    exact cubic_le h2 le_rfl hb hk₂ hk₁ hk₀
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  have hρρ : ρ ≤ ρ * ρ := by nlinarith
  have hA1 : ‖A‖ ≤ ρ * ρ := by
    exact le_of_mul_self_le_mul_self' (hA'.trans (by nlinarith)) (by linarith)
  have hB1 : ‖B‖ ≤ 1 := by
    exact le_of_mul_self_le_mul_self' (hB'.trans (by norm_num)) (by linarith)
  have hN : 2 * 2 * ((a - b) * (a - b)) * X =
      2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A) := by
    linear_combination hX + hA + hB
  have hs : ‖a + b‖ ≤ ρ := ultra_add_le haa (by linarith)
  have hn : ‖2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A)‖
      ≤ ρ * ρ := by
    refine ultra_add_le (ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_) ?_
    · simpa using mul_le_of (mul_le_of (mul_le_of h2.le h2.le) hb) (mul_le_of haa hs)
    · exact (mul_le_of (mul_le_of (mul_le_of h2.le hk₂) hb) haa).trans (by linarith)
    · exact (mul_le_of hk₁ hs).trans (by linarith)
    · exact (mul_le_of h2.le hk₀).trans (by linarith)
    · exact (mul_le_of (mul_le_of h2.le hB1) ((norm_neg A).le.trans hA1)).trans (by linarith)
  rw [← hN, norm_mul, norm_mul, norm_mul, norm_mul, h2, hab] at hn
  by_contra hc
  push_neg at hc
  nlinarith

theorem norm_two_of_ne {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hp
  have e : (2 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := by
    rw [map_natCast]; norm_num
  rw [e, norm_algebraMap', h]

variable {p : ℕ} [Fact p.Prime]

theorem Red.neg {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (h : Red ι L r z) : Red ι L r (-z) :=
  ⟨fun h' => h.1 (by simpa using h'), by rw [L.weierstrassP_neg]; exact h.2⟩

theorem Red.add_lattice {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z ω : ℂ} (h : Red ι L r z)
    (hω : ω ∈ L.lattice) : Red ι L r (z + ω) :=
  ⟨fun h' => h.1 ((L.lattice.add_mem_iff_left hω).1 h'), by
    have e : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
    rw [e]; exact h.2⟩

theorem Red.add_of_not {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r u w : ℂ} (hg : Good ι L r)
    (hu : ¬ Red ι L r u) (hw : Red ι L r w) : Red ι L r (u + w) := by
  by_cases hL : u ∈ L.lattice
  · rw [add_comm]; exact hw.add_lattice hL
  have ha : 1 < ‖ι (L.weierstrassP u - r)‖ := not_le.1 fun h => hu ⟨hL, h⟩
  have hne : L.weierstrassP u ≠ L.weierstrassP w := fun h => by
    rw [h] at ha; exact absurd hw.2 (not_le.2 ha)
  refine ⟨fun h => hu ?_, ?_⟩
  · have := hw.neg.add_lattice h
    rwa [show -w + (u + w) = u by ring] at this
  obtain ⟨hp, hk₂, hk₁, hk₀, -⟩ := hg
  have hs := (GlobalTheory.weierstrassP_add L hL hw.1 hne).1
  have e1 := L.derivWeierstrassP_sq u hL
  have e2 := L.derivWeierstrassP_sq w hw.1
  have hd := sub_ne_zero.2 hne
  have key : ∀ x y : ℂ, y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ →
      ι y ^ 2 = 4 * ι (x - r) ^ 3 + ι (12 * r) * ι (x - r) ^ 2 + ι (12 * r ^ 2 - L.g₂) * ι (x - r)
        + ι (4 * r ^ 3 - L.g₂ * r - L.g₃) := fun x y h => by
    have : y ^ 2 = 4 * (x - r) ^ 3 + (12 * r) * (x - r) ^ 2 + (12 * r ^ 2 - L.g₂) * (x - r)
        + (4 * r ^ 3 - L.g₂ * r - L.g₃) := by linear_combination h
    rw [← map_pow, this, map_add (f := _), map_add (f := _), map_add (f := _), map_mul ι 4, map_mul ι (12 * r),
      map_mul ι _ (x - r), map_pow, map_pow, map_ofNat]
  refine chord_norm_le_one (norm_two_of_ne hp) ha hw.2 hk₂ hk₁ hk₀ (key _ _ e1) (key _ _ e2) ?_
  have : 4 * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 * (L.weierstrassP (u + w) - r)
      = (L.derivWeierstrassP u - L.derivWeierstrassP w) ^ 2
        - (4 * ((L.weierstrassP u - r) + (L.weierstrassP w - r)) + 12 * r)
          * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 := by
    rw [hs]; field_simp; ring
  have := congrArg ι this
  simpa only [map_mul, map_sub, map_add (f := _), map_pow, map_ofNat] using this

theorem not_red_addSubgroup : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → (∀ z, Red ι L r z → Red ι L r (-z)) ∧ (∀ z, Red ι L r z → ∀ ω ∈ L.lattice, Red ι L r (z + ω)) ∧ (∀ u w, ¬ Red ι L r u → Red ι L r w → Red ι L r (u + w)) ∧ ∃ G : AddSubgroup ℂ, (∀ z, z ∈ G ↔ ¬ Red ι L r z) ∧ ∀ ω ∈ L.lattice, ω ∈ G := by
  intro p _ ι L r hg
  refine ⟨fun z h => h.neg, fun z h ω hω => h.add_lattice hω, fun u w hu hw => Red.add_of_not hg hu hw, ?_⟩
  have hneg : ∀ {z : ℂ}, ¬ Red ι L r z → ¬ Red ι L r (-z) := fun hz h => hz (by simpa using h.neg)
  refine ⟨{ carrier := {z | ¬ Red ι L r z}
            add_mem' := fun {u v} hu hv h => hu ?_
            zero_mem' := not_red_of_mem ι L r L.lattice.zero_mem
            neg_mem' := hneg }, fun z => Iff.rfl, fun ω hω => not_red_of_mem ι L r hω⟩
  have := Red.add_of_not hg (hneg hv) h
  rwa [show -v + (u + v) = u by ring] at this

end GlobalTheory.Klein
end

section

open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac

open Filter Topology

noncomputable section
namespace GlobalTheory.LocFlat.CFac.Span

theorem isLocallyConstant_indicator_one {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem indicator_one_mem_SB {Z : Type} [TopologicalSpace Z] {W : Set Z} (hc : IsCompact W)
    (hW : IsClopen W) : W.indicator (1 : Z → ℂ) ∈ SB Z :=
  ⟨isLocallyConstant_indicator_one hW, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩

def S (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : Submodule ℂ (X × Y → ℂ) :=
  Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodFn q.1.1 q.2.1)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def IsBox (r : Set X × Set Y) : Prop := IsCompact r.1 ∧ IsClopen r.1 ∧ IsCompact r.2 ∧ IsClopen r.2

theorem IsBox.inter {r s : Set X × Set Y} (hr : IsBox r) (hs : IsBox s) :
    IsBox (r.1 ∩ s.1, r.2 ∩ s.2) :=
  ⟨hr.1.inter_right hs.2.1.isClosed, hr.2.1.inter hs.2.1, hr.2.2.1.inter_right hs.2.2.2.isClosed,
    hr.2.2.2.inter hs.2.2.2⟩

theorem box_mem {r : Set X × Set Y} (hr : IsBox r) :
    (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) ∈ S X Y := by
  have : (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) = prodFn (r.1.indicator 1) (r.2.indicator 1) := by
    ext ⟨x, y⟩
    by_cases hx : x ∈ r.1 <;> by_cases hy : y ∈ r.2 <;> simp [prodFn, Set.indicator, hx, hy]
  rw [this]
  exact Submodule.subset_span ⟨(⟨_, indicator_one_mem_SB hr.1 hr.2.1⟩,
    ⟨_, indicator_one_mem_SB hr.2.2.1 hr.2.2.2⟩), rfl⟩

def U (L : List (Set X × Set Y)) : Set (X × Y) := ⋃ r ∈ L, r.1 ×ˢ r.2

theorem U_cons (r : Set X × Set Y) (L : List (Set X × Set Y)) : U (r :: L) = r.1 ×ˢ r.2 ∪ U L := by
  simp [U]

theorem inter_U (r : Set X × Set Y) (L : List (Set X × Set Y)) :
    r.1 ×ˢ r.2 ∩ U L = U (L.map fun s => (r.1 ∩ s.1, r.2 ∩ s.2)) := by
  ext p
  simp only [U, Set.mem_inter_iff, Set.mem_iUnion, List.mem_map, Set.mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, s, hs, h3, h4⟩
    exact ⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
    exact ⟨⟨h1, h2⟩, s, hs, h3, h4⟩

theorem U_mem : ∀ (n : ℕ) (L : List (Set X × Set Y)), L.length ≤ n → (∀ r ∈ L, IsBox r) →
    (U L).indicator (1 : X × Y → ℂ) ∈ S X Y := by
  intro n
  induction n with
  | zero =>
    intro L hL _
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hL)]
    simp [U]
    exact Submodule.zero_mem _
  | succ n ih =>
    intro L hL hB
    cases L with
    | nil => simp [U]; exact Submodule.zero_mem _
    | cons r L =>
      have key := Set.indicator_union_add_inter (f := (1 : X × Y → ℂ)) (r.1 ×ˢ r.2) (U L)
      have hL' : L.length ≤ n := by simp at hL; omega
      rw [U_cons, eq_sub_of_add_eq key, inter_U]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (box_mem (hB r (by simp)))
        (ih L hL' fun s hs => hB s (by simp [hs]))) (ih _ (by simpa using hL') ?_)
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      exact (hB r (by simp)).inter (hB t (by simp [ht]))

theorem F_mem (F : X × Y → ℂ) : ∀ L : List (Set X × Set Y),
    (∀ r ∈ L, IsBox r ∧ ∃ c : ℂ, ∀ p ∈ r.1 ×ˢ r.2, F p = c) → (U L).indicator F ∈ S X Y := by
  intro L
  induction L with
  | nil => intro _; simp [U]; exact Submodule.zero_mem _
  | cons r L ih =>
    intro hL
    obtain ⟨hB, c, hc⟩ := hL r (by simp)
    have key := Set.indicator_union_add_inter (f := F) (r.1 ×ˢ r.2) (U L)
    have hA : (r.1 ×ˢ r.2).indicator F = c • (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) := by
      ext p
      simp only [Pi.smul_apply]
      by_cases hp : p ∈ r.1 ×ˢ r.2
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp [hc p hp]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp
    have hI : (r.1 ×ˢ r.2 ∩ U L).indicator F = c • (r.1 ×ˢ r.2 ∩ U L).indicator (1 : X × Y → ℂ) := by
      ext p
      simp only [Pi.smul_apply]
      by_cases hp : p ∈ r.1 ×ˢ r.2 ∩ U L
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp [hc p hp.1]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp
    rw [U_cons, eq_sub_of_add_eq key, hA, hI, inter_U]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ c (box_mem hB))
      (ih fun s hs => hL s (by simp [hs]))) (Submodule.smul_mem _ c (U_mem _ _ le_rfl ?_))
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact hB.inter (hL t (by simp [ht])).1

theorem exists_compact_clopen [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {x : X} {O : Set X} (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ O := by
  obtain ⟨K, hK, hxK, hKO⟩ := exists_compact_subset hO hx
  obtain ⟨V, hV, hxV, hVK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (X := X)).isOpen_iff.1
    isOpen_interior x hxK
  exact ⟨V, hK.of_isClosed_subset hV.isClosed (hVK.trans interior_subset), hV, hxV,
    (hVK.trans interior_subset).trans hKO⟩

theorem mem_S [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (F : X × Y → ℂ) (hF : F ∈ SB (X × Y)) : F ∈ S X Y := by
  have hbox : ∀ p : X × Y, ∃ r : Set X × Set Y, IsBox r ∧ p ∈ r.1 ×ˢ r.2 ∧
      ∀ q ∈ r.1 ×ˢ r.2, F q = F p := by
    intro p
    have hO : IsOpen {q | F q = F p} := hF.1.isOpen_fiber _
    obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ := isOpen_prod_iff.1 hO p.1 p.2 rfl
    obtain ⟨U₁, hU1, hU2, hU3, hU4⟩ := exists_compact_clopen hu hpu
    obtain ⟨V₁, hV1, hV2, hV3, hV4⟩ := exists_compact_clopen hv hpv
    exact ⟨(U₁, V₁), ⟨hU1, hU2, hV1, hV2⟩, ⟨hU3, hV3⟩, fun q hq => huv (Set.prod_mono hU4 hV4 hq)⟩
  choose R hRb hRp hRc using hbox
  obtain ⟨t, -, ht⟩ := hF.2.isCompact.elim_nhds_subcover (fun p => (R p).1 ×ˢ (R p).2)
    fun p _ => ((hRb p).2.1.isOpen.prod (hRb p).2.2.2.isOpen).mem_nhds (hRp p)
  have hsub : tsupport F ⊆ U (t.toList.map R) := by
    intro q hq
    have := ht hq
    simp only [Set.mem_iUnion] at this
    obtain ⟨p, hp, hq'⟩ := this
    simp only [U, Set.mem_iUnion]
    exact ⟨R p, List.mem_map.2 ⟨p, Finset.mem_toList.2 hp, rfl⟩, hq'⟩
  have heq : (U (t.toList.map R)).indicator F = F :=
    Set.indicator_eq_self.2 ((subset_tsupport F).trans hsub)
  rw [← heq]
  refine F_mem F _ ?_
  intro r hr
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hr
  exact ⟨hRb p, F p, hRc p⟩

theorem span_prodSB_eq_top : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y],
    Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2) = ⊤ := by
  intro X Y _ _ _ _ _ _ _ _
  have hmap : (Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2)).map
      (SB (X × Y)).subtype = S X Y := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [eq_top_iff]
  rintro F -
  have h := mem_S F.1 F.2
  rw [← hmap] at h
  obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 h
  have : G = F := Subtype.ext hGF
  rwa [← this]

end GlobalTheory.LocFlat.CFac.Span
end
end

section

open Matrix

namespace GlobalTheory.Core.Rk.Exh

theorem exists_orthonormal_of_isLocalRing (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O)
    (hs : ∀ x, s (s x) = x) (hτ : ∃ τ : O, τ + s τ = 1)
    (hn : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u)
    (n : ℕ) (Q : Matrix (Fin n) (Fin n) O) (hQ : Formalism.UG.cT s Q = Q) (hu : IsUnit Q) :
    ∃ a : GL (Fin n) O, Formalism.UG.cT s a.1 * Q * a.1 = 1 := by
  obtain ⟨P, hP, h⟩ := UnramifiedHermitian.exists_eq_transpose_mul_map_of_isUnit_or s hs
    (fun x _ => IsLocalRing.isUnit_or_isUnit_one_sub_self x) hτ
    (fun u h1 h2 => (hn u h2 h1).imp fun x hx => by rw [mul_comm, hx])
    (G := Q) (fun a b => congrFun (congrFun hQ b) a) ((Matrix.isUnit_iff_isUnit_det Q).1 hu)
  obtain ⟨R, hR, h'⟩ := UnramifiedHermitian.exists_congr_symm s (G := 1) (H := Q) hP
    (by rw [Matrix.mul_one, h])
  have hR' : IsUnit (R.map s) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hR.map s
  refine ⟨hR'.unit, ?_⟩
  rw [IsUnit.unit_spec, h']
  congr 2
  ext i j
  exact hs _

end GlobalTheory.Core.Rk.Exh
end

section

open scoped ContDiff Topology

namespace GlobalTheory

theorem contDiff_of_class_tendstoLocallyUniformly : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  intro E _ _ A _ v c hc P hP
  have key : ∀ φ, P φ → Differentiable ℝ φ ∧ ∃ (α χ : A → E → ℂ), (∀ a, ContDiff ℝ ∞ (α a)) ∧
      (∀ a, P (χ a)) ∧ fderiv ℝ φ =
        fun y => ∑ a, (α a y * φ y + χ a y) • ((c a).smulRight (1 : ℂ)) := by
    intro φ hφ
    obtain ⟨g, hg, hlim, hd⟩ := hP φ hφ
    choose α hα χ hχ hlim' using hd
    have h := GlobalTheory.T.differentiableAt_limit_of_directional_derivs_converge v c hc φ g (fun a y => α a y * φ y + χ a y) hg hlim hlim'
    refine ⟨fun y => (h y).1, α, χ, hα, hχ, ?_⟩
    funext y
    ext x
    conv_lhs => rw [← hc x]

    simp only [map_sum, map_smul, (h y).2, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  have main : ∀ n : ℕ, ∀ φ, P φ → ContDiff ℝ n φ := by
    intro n
    induction n with
    | zero =>
      intro φ hφ
      simpa using (key φ hφ).1.continuous
    | succ n ih =>
      intro φ hφ
      obtain ⟨hd, α, χ, hα, hχ, hf⟩ := key φ hφ
      have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) φ := by
        rw [contDiff_succ_iff_fderiv]
        refine ⟨hd, by simp, ?_⟩
        rw [hf]
        refine ContDiff.sum fun a _ => ?_
        have h1 : ContDiff ℝ n (α a) := (hα a).of_le (by exact_mod_cast le_top)
        exact ((h1.mul (ih φ hφ)).add (ih _ (hχ a))).smul contDiff_const
      exact_mod_cast this
  intro φ hφ
  exact contDiff_infty.2 fun n => main n φ hφ

end GlobalTheory
end

section

open ValuativeRel GlobalTheory.SplitWeil Matrix

theorem _root_.GlobalTheory.T.matrix_integral_of_addChar_trace_dual : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ x : Matrix Y Y' k, (∀ b : Matrix Y Y' k, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → ψk (∑ r, ∑ q, b r q * u r q) = 1) → ψk (∑ r, ∑ q, b r q * x r q) = 1) → ∀ r q, x r q ∈ 𝒪[k] := by
  first | exact @GlobalTheory.CharDualMat.integral_of_dual | exact GlobalTheory.CharDualMat.integral_of_dual | (intros; apply GlobalTheory.CharDualMat.integral_of_dual <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin

theorem _root_.GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  first | exact @GlobalTheory.unipotent_upper_inv_bounded | exact GlobalTheory.unipotent_upper_inv_bounded | (intros; apply GlobalTheory.unipotent_upper_inv_bounded <;> assumption)
end

end

section

@[expose] public section

open scoped ContDiff Topology


theorem _root_.GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  first | exact @GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | exact GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | (intros; apply GlobalTheory.contDiff_of_class_tendstoLocallyUniformly <;> assumption)

end
end
