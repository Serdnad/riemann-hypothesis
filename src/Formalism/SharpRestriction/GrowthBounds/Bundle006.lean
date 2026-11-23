module

public import Formalism.SharpRestriction.GrowthBounds.Bundle005
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.LocalToGlobal.CharacterGerms.GeOfPowEqOne
public import Formalism.LocalToGlobal.CharacterGerms.Bundle015
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def ee (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rs (j : Fin 2) (c : C) : MvPowerSeries (Fin 2) C →+* MvPowerSeries (Fin 2) C :=
  MvPowerSeries.rescale (fun i => if i = j then c else 1)

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

def pw (n : ℕ) (δ : κ → PowerSeries C) : κ → PowerSeries C :=
  fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (δ i)

end SelfConjCharts

open SelfConjCharts

def PowerSeriesFrobeniusCongruence : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C), IntS V f → ∀ μ : σ →₀ ℕ,
    V.MM (MvPowerSeries.coeff (V.l • μ) (f ^ V.l) - MvPowerSeries.coeff μ f ^ V.l)

def RootsOfUnityProductCongruence : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (ζ : C), ζ ^ V.l = 1 → ∀ (j : Fin 2) (f : MvPowerSeries (Fin 2) C), IntS V f →
    ∀ μ, V.MM (MvPowerSeries.coeff μ (∏ k ∈ Finset.range V.l, rs j (ζ ^ k) f - f ^ V.l))

def ExpLowOrderTruncation : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (F : MvPowerSeries (Fin 2) C) (m : ℕ), 1 ≤ m →
    (∀ i j, j < m → MvPowerSeries.coeff (ee i j) F = 0) →
    ∀ i j, j < 2 * m → MvPowerSeries.coeff (ee i j) (mvExp F) =
      MvPowerSeries.coeff (ee i j) (1 : MvPowerSeries (Fin 2) C) + MvPowerSeries.coeff (ee i j) F

def GaugeLeadingTermLinear : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ),
    (∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → MvPowerSeries.coeff e X.h = 0) →
    ∀ x c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (x i) = 0) → ∀ m : ℕ, 1 ≤ m →
    (∀ i j, j < m → PowerSeries.coeff j (c i) = 0) →
    (∀ n j, j < m → MvPowerSeries.coeff (ee n j) (HH X x c) = 0) ∧
      ∀ n, MvPowerSeries.coeff (ee n m) (HH X x c) =
        -PowerSeries.coeff n (alongCv x (X.sg fun i => PowerSeries.coeff m (c i)))

def GaugeRescalingSymmetry : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C), (∀ i, PowerSeries.constantCoeff (x i) = 0) →
    (∀ i, PowerSeries.constantCoeff (z i) = 0) → ∀ c : C,
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z)

def IntegralUnitFamilies : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), Basic X V → BiInt X V → ∀ ζ : C, ζ ^ V.l = 1 → ∀ (n : ℕ), 0 < n →
    ∀ γ δ c : κ → PowerSeries C, IsCv V γ → IsCv V δ → IsCv V c → NormRel X V.l n ζ γ δ →
    IntS V (mvExp (∑ k ∈ Finset.range V.l, HH X (rc (ζ ^ k) γ) c - HH X (pw n δ) c)) ∧
      IntS V (mvExp (∑ k ∈ Finset.range V.l, HH X c (rc (ζ ^ k) γ) - HH X c (pw n δ)))

def GenericPointUnitCongruence : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), Basic X V → BiInt X V → ∀ ζ : C, ζ ^ V.l = 1 → ∀ (n : ℕ), 0 < n →
    ∀ z ε δ : κ → PowerSeries C, IsCv V z → IsCv V ε → IsCv V δ → NormRel X V.l n ζ z ε →
    (∀ i, V.MM (PowerSeries.coeff 1 (δ i))) → ∀ N : ℕ, 0 < N → ∀ i j, i ≤ N →
    V.MM (MvPowerSeries.coeff (ee i j)
      (mvExp (∑ k ∈ Finset.range V.l, HH X (pw N δ) (rc (ζ ^ k) z) - HH X (pw N δ) (pw n ε)) - 1))

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

theorem subst_tyS_Fs {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l fun s => (l : C) * a (s + 1)) =
      ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) := by
  rw [← tyS_Vpow hl]
  apply tyS_eq hl
  · intro s

    rw [map_sum]
    simp only [PowerSeries.coeff_rescale, coeff_tyS_pow hl]
    rw [← Finset.sum_mul]
    cases s with
    | zero =>
      simp only [pow_zero, pow_one]
      rw [hζ.geom_sum_eq_zero (by omega), zero_mul]
      simp
    | succ s =>
      have h1 : ∀ k, (ζ ^ k) ^ (l ^ (s + 1)) = 1 := by
        intro k
        rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
      simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      simp
  · intro m hm

    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [PowerSeries.coeff_rescale, coeff_tyS_of_ne _ m hm, mul_zero]

theorem rescale_sum_smul {ι : Type} [Fintype ι] (a : C) (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.rescale a (∑ c, u c • f c) = ∑ c, u c • PowerSeries.rescale a (f c) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem subst_pow_sum_smul {n : ℕ} (hn : 0 < n) {ι : Type} [Fintype ι] (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (∑ c, u c • f c) =
      ∑ c, u c • PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (f c) := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ n) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hn.ne'])

  rw [← PowerSeries.coe_substAlgHom hS, map_sum]
  simp only [map_smul]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem coeff_one_alongCv_lg (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : κ) :
    PowerSeries.coeff 1 (alongCv γ (X.lg i)) = PowerSeries.coeff 1 (γ i) := by
  rw [coeff_alongCv_low le_rfl (fun j m hm => by
      have : m = 0 := by omega
      subst this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ j]) (hB.lg0 i)]
  rw [Finset.sum_eq_single i]
  · rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_pos rfl, one_mul]
  · intro j _ hj
    rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_neg, zero_mul]
    intro h
    exact hj (Finsupp.single_left_injective one_ne_zero h)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coeff_one_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.coeff 1 (tyS l a) = a 0 := by
  have h := coeff_tyS_pow hl a 0
  rwa [pow_zero] at h

theorem coeff_one_of_mem (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {g : Fin 2} {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {x : ℕ → I g ⊕ JJ I g → C}
    (h1 : ∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) (i : κ) :
    PowerSeries.coeff 1 (γ i) = ∑ c : I g, X.u g c i * x 0 (Sum.inl c) := by

  rw [← coeff_one_alongCv_lg X hB hγ i, h1 i, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_smul, coeff_one_tyS V.l_prime.two_le, smul_eq_mul]

end SelfConjCharts

open SelfConjCharts in
theorem r1sRestB_holds : OtherGroupCurvesClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g q
  have hl2 := V.l_prime.two_le
  set g' : Fin 2 := 1 - g with hg'
  obtain ⟨x, hx, hx0, -⟩ := (H g').t4 (X.ty g' q) (fun c => if c = q then 1 else 0)
    (fun c => by split_ifs <;> simp [VF.Ge.zero, VF.Ge.one])
    (fun c hc => by
      rw [if_neg]
      rintro rfl
      exact hc rfl)
  have hF := (H g').Fm x hx
  obtain ⟨z, -, hz, -, hz1, -⟩ := id hx
  obtain ⟨ε, -, hε, -, hε1, -⟩ := hF
  refine ⟨z, ε, fun q' => Fs V.l x 0 (Sum.inl q'), hz, hε, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hε1 i, hz1 i, subst_pow_sum_smul (by omega)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum]
    congr 1
    exact subst_tyS_Fs hl2 hζ (fun s => x s (Sum.inl c))
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hz i).1) hz1 i, hx0]
    simp only [Sum.elim_inl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hε i).1) hε1 i]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · intro q'
    exact (H g').t2 _ ((H g').Fm x hx) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) _

end Formalism.L2.FormalSeriesBounds
end
end
