module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountPowSuccInert
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle005
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle002
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

scoped instance starO : StarRing (𝓞 K) where
  star := conjO K
  star_involutive := L3.conjO_conjO
  star_mul a b := by
    show conjO K (a * b) = conjO K b * conjO K a
    rw [map_mul, mul_comm]
  star_add := map_add (conjO K)

theorem star_def (a : 𝓞 K) : star a = conjO K a := rfl

scoped instance starQ [hF : Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    StarRing (𝓞 K ⧸ extP K 𝔭 ^ k) where
  star := NormLifting.conjQ _ (conjO_mem_pow hF.out 𝔭 k)
  star_involutive a := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    show NormLifting.conjQ _ _ (NormLifting.conjQ _ _ _) = _
    rw [NormLifting.conjQ_mk, NormLifting.conjQ_mk, L3.conjO_conjO]
  star_mul a b := by
    show NormLifting.conjQ _ _ (a * b) = NormLifting.conjQ _ _ b * NormLifting.conjQ _ _ a
    rw [map_mul, mul_comm]
  star_add := map_add _

theorem star_mk [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    star (Ideal.Quotient.mk (extP K 𝔭 ^ k) a) = Ideal.Quotient.mk (extP K 𝔭 ^ k) (star a) := NormLifting.conjQ_mk _ _ a

theorem absNorm_extP_eq_sq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  have h := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 K) 𝔭
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K, MeanB.finrank_eq_two hK hF] at h
  exact h

theorem absNorm_extP_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  have h1 : Ideal.absNorm (extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
    rw [map_pow, absNorm_extP_eq_sq hK hF h𝔭, ← pow_mul]
  rw [← h1, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem finite_quot {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := by
  have h0 : extP K 𝔭 ^ k ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact map_ne_bot_of_isMaximal h𝔭)
  first
  | exact Ideal.finiteQuotientOfFreeOfNeBot _ h0
  | exact (Ideal.absNorm_ne_zero_iff _).mp (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0)

def piQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) →+* (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ k))

theorem piQ_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    piQ K 𝔭 k (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

theorem piQ_surjective (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Function.Surjective (piQ K 𝔭 k) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem piQ_star [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :
    piQ K 𝔭 k (star a) = star (piQ K 𝔭 k a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [star_mk, piQ_mk, piQ_mk, star_mk]

theorem mk_mem_ker_piQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) a ∈ RingHom.ker (piQ K 𝔭 k) ↔ a ∈ extP K 𝔭 ^ k := by
  rw [RingHom.mem_ker, piQ_mk, Ideal.Quotient.eq_zero_iff_mem]

theorem card_ker_piQ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Nat.card (RingHom.ker (piQ K 𝔭 k)) = Ideal.absNorm 𝔭 ^ 2 := by
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  have hA := absNorm_extP_pow hK hF h𝔭 (k + 1)
  have hB := absNorm_extP_pow hK hF h𝔭 k
  have hC : Nat.card ((𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) ⧸ RingHom.ker (piQ K 𝔭 k)) =
      Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) :=
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (piQ_surjective (K := K) 𝔭 k)).toEquiv
  have hmul : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) = Nat.card (RingHom.ker (piQ K 𝔭 k)) *
      Nat.card ((𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) ⧸ RingHom.ker (piQ K 𝔭 k)) := by
    first
    | exact Submodule.card_eq_card_quotient_mul_card _
    | (rw [mul_comm]; exact Submodule.card_eq_card_quotient_mul_card _)
    | (rw [mul_comm]; exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (RingHom.ker (piQ K 𝔭 k)).toAddSubgroup)
    | exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (RingHom.ker (piQ K 𝔭 k)).toAddSubgroup
  rw [hC, hA, hB] at hmul
  have hN : 0 < Ideal.absNorm 𝔭 ^ (2 * k) :=
    pow_pos (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact ne_bot h𝔭)) _
  have e : Ideal.absNorm 𝔭 ^ (2 * (k + 1)) = Ideal.absNorm 𝔭 ^ 2 * Ideal.absNorm 𝔭 ^ (2 * k) := by
    ring
  rw [e] at hmul
  exact (Nat.eq_of_mul_eq_mul_right hN hmul).symm

def idQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k j : ℕ) :
    Ideal (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (extP K 𝔭 ^ j).map (Ideal.Quotient.mk _)

theorem mem_idQ {𝔭 : Ideal (𝓞 F)} {k j : ℕ} {a : 𝓞 K ⧸ extP K 𝔭 ^ k} :
    a ∈ idQ K 𝔭 k j ↔ ∃ z ∈ extP K 𝔭 ^ j, Ideal.Quotient.mk _ z = a := by
  show a ∈ (extP K 𝔭 ^ j).map (Ideal.Quotient.mk _) ↔ _
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]

theorem mk_mem_idQ {𝔭 : Ideal (𝓞 F)} {k j : ℕ} (hjk : j ≤ k) {z : 𝓞 K} :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) z ∈ idQ K 𝔭 k j ↔ z ∈ extP K 𝔭 ^ j := by
  rw [mem_idQ]
  constructor
  · rintro ⟨z', hz', he⟩
    rw [Ideal.Quotient.eq] at he
    have h1 : z' - z ∈ extP K 𝔭 ^ j := Ideal.pow_le_pow_right hjk he
    have h2 : z = z' - (z' - z) := by ring
    rw [h2]
    exact Ideal.sub_mem _ hz' h1
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem star_mem_idQ [hF : Fact (IsFixF K F)] {𝔭 : Ideal (𝓞 F)} {k j : ℕ}
    {a : 𝓞 K ⧸ extP K 𝔭 ^ k} (ha : a ∈ idQ K 𝔭 k j) : star a ∈ idQ K 𝔭 k j := by
  obtain ⟨z, hz, rfl⟩ := mem_idQ.mp ha
  rw [star_mk]
  exact mem_idQ.mpr ⟨star z, conjO_mem_pow hF.out 𝔭 j z hz, rfl⟩

theorem mul_eq_zero_idQ {𝔭 : Ideal (𝓞 F)} {k j : ℕ} (hjk : k ≤ 2 * j)
    {a b : 𝓞 K ⧸ extP K 𝔭 ^ k} (ha : a ∈ idQ K 𝔭 k j) (hb : b ∈ idQ K 𝔭 k j) : a * b = 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_idQ.mp ha
  obtain ⟨y, hy, rfl⟩ := mem_idQ.mp hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have h1 : x * y ∈ extP K 𝔭 ^ (j + j) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hx hy
  exact Ideal.pow_le_pow_right (by omega) h1

theorem ker_piQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) : RingHom.ker (piQ K 𝔭 k) = idQ K 𝔭 (k + 1) k := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [mk_mem_ker_piQ, mk_mem_idQ (Nat.le_succ k)]

end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem map_mem_extP {𝔭 : Ideal (𝓞 F)} {k : ℕ} {s : 𝓞 F} (hs : s ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) s ∈ extP K 𝔭 ^ k := by
  rw [← Ideal.mem_comap, MeanB.comap_extP_pow]
  exact hs

theorem mem_extP_of_mul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) {k : ℕ}
    {z : 𝓞 K} (hz : algebraMap (𝓞 F) (𝓞 K) t * z ∈ extP K 𝔭 ^ k) : z ∈ extP K 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : z = algebraMap (𝓞 F) (𝓞 K) u * (algebraMap (𝓞 F) (𝓞 K) t * z) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) * z := by
    rw [map_sub, map_mul, map_one]
    ring
  rw [e]
  exact sub_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_right _ _ (map_mem_extP hu))

theorem conjO_mem_extP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K}
    (hz : z ∈ extP K 𝔭 ^ k) : conjO K z ∈ extP K 𝔭 ^ k := by
  obtain ⟨z', hz', e⟩ := MeanB.star_mem_extP hF 𝔭 k hz
  have : conjO K z = z' := RingOfIntegers.ext e.symm
  rw [this]
  exact hz'

theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def IsGen (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : V) : Prop :=
  e ∈ L ∧ e ≠ 0 ∧ ∀ x ∈ L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 F) (𝓞 K) t • x = a • e

theorem exists_isGen {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L)
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ e, IsGen L 𝔭 e := by
  obtain ⟨b, hb, hloc⟩ := LocalSpans.exists_basis_locF hL h𝔭
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  refine ⟨b i0, hb i0, b.ne_zero i0, fun x hx => ?_⟩
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hloc]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, hm⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).1 hx'
  have hr : Set.range b = {b i0} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      rw [Subsingleton.elim i i0]
      rfl
    · rintro rfl
      exact ⟨i0, rfl⟩
  rw [hr, Submodule.mem_span_singleton] at hm
  obtain ⟨a, ha⟩ := hm
  exact ⟨t, ht, a, ha.symm⟩

theorem discrIdeal_le_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V} (he : IsGen L 𝔭 e)
    {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) (j : ℕ) :
    discrIdeal h L ≤ extP K 𝔭 ^ j ↔ n ∈ 𝔭 ^ j := by
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  constructor
  · intro hle
    rw [← MeanB.comap_extP_pow (K := K), Ideal.mem_comap]
    apply hle
    refine Ideal.subset_span ⟨fun _ => e, fun _ => he.1, ?_⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply, hn]
    rfl
  · intro hnj
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, hz⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply] at hz
    obtain ⟨t, ht, a, ha⟩ := he.2.2 (x i0) (hx i0)
    apply mem_extP_of_mul h𝔭 ht
    apply mem_extP_of_mul h𝔭 ht
    have : algebraMap (𝓞 F) (𝓞 K) t * (algebraMap (𝓞 F) (𝓞 K) t * z) =
        conjO K a * a * algebraMap (𝓞 F) (𝓞 K) n := by
      apply RingOfIntegers.coe_injective
      have e1 : h (algebraMap (𝓞 F) (𝓞 K) t • x i0) (algebraMap (𝓞 F) (𝓞 K) t • x i0) =
          h (a • e) (a • e) := by rw [ha]
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right,
        Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hn, ← hz,
        MeanB.algebraMap_comp, MeanB.star_algebraMap hF] at e1
      simp only [map_mul]
      rw [MeanB.algebraMap_comp, MeanB.algebraMap_comp]
      change _ = star (algebraMap (𝓞 K) K a) * _ * _
      rw [e1]
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (map_mem_extP hnj)

theorem vd_spec (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V}
    (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) :
    n ∈ 𝔭 ^ vd h L 𝔭 ∧ n ∉ 𝔭 ^ (vd h L 𝔭 + 1) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply he.2.1
    apply LocF.aniso_of_totPosDef hd
    rw [hn]
    simp
  have hset : {j : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ j} = {j : ℕ | n ∈ 𝔭 ^ j} := by
    ext j
    exact discrIdeal_le_iff hF h1 h𝔭 he hn j
  have hinf : (⨅ j : ℕ, 𝔭 ^ j) = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top
  obtain ⟨j0, hj0⟩ : ∃ j0, n ∉ 𝔭 ^ j0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hn0
    have : n ∈ (⨅ j : ℕ, 𝔭 ^ j) := (Submodule.mem_iInf _).2 hcon
    rwa [hinf] at this
  have hbdd : BddAbove {j : ℕ | n ∈ 𝔭 ^ j} := by
    refine ⟨j0, fun j hj => ?_⟩
    by_contra hlt
    exact hj0 (Ideal.pow_le_pow_right (not_le.1 hlt).le hj)
  have hne : {j : ℕ | n ∈ 𝔭 ^ j}.Nonempty := ⟨0, by simp⟩
  unfold vd
  rw [hset]
  refine ⟨Nat.sSup_mem hne hbdd, fun hcon => ?_⟩
  have := le_csSup hbdd (show sSup {j : ℕ | n ∈ 𝔭 ^ j} + 1 ∈ {j : ℕ | n ∈ 𝔭 ^ j} from hcon)
  omega

end Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
end
end
