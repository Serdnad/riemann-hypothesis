module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.FinNormSurj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

noncomputable section

namespace Formalism.IndefR.LocBrg

section HS

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))

def newtonSq (u : L) : ℕ → L
  | 0 => 1
  | k + 1 => newtonSq u k - (newtonSq u k * newtonSq u k - u) / (2 * newtonSq u k)

theorem pow_small {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1) (δ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ N : ℕ, γ ^ N < δ := by
  rcases eq_or_ne γ 0 with h0 | h0
  · exact ⟨1, by rw [h0, pow_one]; exact zero_lt_iff.mpr δ.ne_zero⟩
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp h0
  obtain ⟨d, hd⟩ := WithZero.ne_zero_iff_exists.mp δ.ne_zero
  rw [← hd]
  have hg : g < 1 := by exact_mod_cast hγ
  have ha : Multiplicative.toAdd g < 0 := by
    have := Multiplicative.toAdd_lt.mpr hg
    simpa using this
  have hn : 1 - Multiplicative.toAdd d ≤ ((Int.toNat (1 - Multiplicative.toAdd d) : ℕ) : ℤ) :=
    Int.self_le_toNat _
  have hn0 : (0 : ℤ) ≤ ((Int.toNat (1 - Multiplicative.toAdd d) : ℕ) : ℤ) := Nat.cast_nonneg _
  refine ⟨Int.toNat (1 - Multiplicative.toAdd d), ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt, toAdd_pow, nsmul_eq_mul]
  nlinarith

variable (u : L)

theorem newton_step (k : ℕ) (hs : vv (newtonSq u k - 1) < 1) (h2 : vv (2 : L) = 1) :
    vv (newtonSq u k) = 1 ∧
      newtonSq u (k + 1) * newtonSq u (k + 1) - u =
        (newtonSq u k * newtonSq u k - u) ^ 2 / (4 * newtonSq u k ^ 2) ∧
      vv (newtonSq u (k + 1) - newtonSq u k) = vv (newtonSq u k * newtonSq u k - u) := by
  set x := newtonSq u k with hx
  have hx1 : vv x = 1 := by
    have hxe : x = (x - 1) + 1 := by ring
    have hlt : vv (x - 1) < vv (1 : L) := by rwa [Valuation.map_one]
    rw [hxe, Valuation.map_add_eq_of_lt_right (v := vv) hlt, Valuation.map_one]
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hx1
    exact zero_ne_one hx1
  have h20 : (2 : L) ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at h2
    exact zero_ne_one h2
  have hnext : newtonSq u (k + 1) = x - (x * x - u) / (2 * x) := rfl
  have h40 : (4 : L) ≠ 0 := by
    rw [show (4 : L) = 2 * 2 by norm_num]
    exact mul_ne_zero h20 h20
  refine ⟨hx1, ?_, ?_⟩
  · rw [hnext]
    field_simp
    ring
  · rw [hnext, show x - (x * x - u) / (2 * x) - x = -((x * x - u) / (2 * x)) by ring, Valuation.map_neg,
      Valuation.map_div, Valuation.map_mul, h2, hx1, one_mul, div_one]

theorem newton_bound (h2 : vv (2 : L) = 1) (hu : vv (u - 1) < 1) (k : ℕ) :
    vv (newtonSq u k - 1) < 1 ∧ vv (newtonSq u k * newtonSq u k - u) ≤ vv (u - 1) ^ (k + 1) := by
  induction k with
  | zero =>
    refine ⟨by simp [newtonSq], ?_⟩
    show vv (1 * 1 - u) ≤ vv (u - 1) ^ (0 + 1)
    rw [one_mul, pow_one, Valuation.map_sub_swap]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨hx1, hsq, hdiff⟩ := newton_step u k ih1 h2
    have h4 : vv (4 * newtonSq u k ^ 2) = 1 := by
      rw [Valuation.map_mul, Valuation.map_pow, hx1, one_pow, mul_one,
        show (4 : L) = 2 * 2 by norm_num, Valuation.map_mul, h2, one_mul]
    have hlt : vv (u - 1) ^ (k + 1) < 1 := by
      first
      | exact pow_lt_one₀ zero_le' hu (Nat.succ_ne_zero k)
      | exact pow_lt_one' hu (Nat.succ_ne_zero k)
    constructor
    · have he : newtonSq u (k + 1) - 1 = (newtonSq u (k + 1) - newtonSq u k) + (newtonSq u k - 1) := by
        ring
      rw [he]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih1)
      rw [hdiff]
      exact lt_of_le_of_lt ih2 hlt
    · rw [hsq, Valuation.map_div, Valuation.map_pow, h4, div_one]
      calc vv (newtonSq u k * newtonSq u k - u) ^ 2 ≤ (vv (u - 1) ^ (k + 1)) ^ 2 := by
            first
            | exact pow_le_pow_left' ih2 2
            | exact pow_le_pow_left₀ zero_le' ih2 2
        _ = vv (u - 1) ^ ((k + 1) * 2) := by rw [← pow_mul]
        _ ≤ vv (u - 1) ^ (k + 1 + 1) := by
            first
            | exact pow_le_pow_right_of_le_one' hu.le (by omega)
            | exact pow_le_pow_right_of_le_one₀ zero_le' hu.le (by omega)

end HS

section HS2

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))

variable (u : L)

theorem pow_anti {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≤ 1) {a b : ℕ} (hab : a ≤ b) : γ ^ b ≤ γ ^ a := by
  first
  | exact pow_le_pow_right_of_le_one' hγ hab
  | exact pow_le_pow_right_of_le_one₀ zero_le' hγ hab

theorem newton_cauchy_bound (h2 : vv (2 : L) = 1) (hu : vv (u - 1) < 1) (n m : ℕ) (hnm : n ≤ m) :
    vv (newtonSq u m - newtonSq u n) ≤ vv (u - 1) ^ (n + 1) := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have he : newtonSq u (m + 1) - newtonSq u n =
        (newtonSq u (m + 1) - newtonSq u m) + (newtonSq u m - newtonSq u n) := by ring
    rw [he]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ih)
    obtain ⟨h1, -⟩ := newton_bound u h2 hu m
    obtain ⟨-, -, hdiff⟩ := newton_step u m h1 h2
    rw [hdiff]
    exact le_trans (newton_bound u h2 hu m).2 (pow_anti hu.le (by omega))

theorem newton_cauchy (h2 : vv (2 : L) = 1) (hu : vv (u - 1) < 1) : CauchySeq (newtonSq u) := by
  rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
  intro γ _
  obtain ⟨N, hN⟩ := pow_small hu (Units.mk0 _ (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ))
  rw [Units.val_mk0] at hN
  refine ⟨N, fun m hm n hn => ?_⟩
  show Valued.v.restrict (newtonSq u n - newtonSq u m) < (γ : _)
  rw [Valuation.restrict_lt_iff_lt_embedding]
  rcases le_total m n with hmn | hnm
  · calc vv (newtonSq u n - newtonSq u m) ≤ vv (u - 1) ^ (m + 1) := newton_cauchy_bound u h2 hu m n hmn
      _ ≤ vv (u - 1) ^ N := pow_anti hu.le (by omega)
      _ < _ := hN
  · rw [Valuation.map_sub_swap]
    calc vv (newtonSq u m - newtonSq u n) ≤ vv (u - 1) ^ (n + 1) := newton_cauchy_bound u h2 hu n m hnm
      _ ≤ vv (u - 1) ^ N := pow_anti hu.le (by omega)
      _ < _ := hN

end HS2

theorem henselSqrt : HenselSqrt := by
  intro L _ _ _ h2 u hu
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete (newton_cauchy u h2 hu)
  have hsq : Filter.Tendsto (fun k => newtonSq u k * newtonSq u k) Filter.atTop (nhds (s * s)) := hs.mul hs
  refine ⟨s, ?_, ?_⟩
  · by_contra hne
    have hne' : s * s - u ≠ 0 := sub_ne_zero.mpr hne
    have hv0 : Valued.v (s * s - u) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne'
    have hr0 : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict (s * s - u) ≠ 0 := by
      intro h
      apply hv0
      rw [← Valuation.embedding_restrict, h, map_zero]
    have h1 := hsq.eventually_mem (Valued.mem_nhds.mpr ⟨Units.mk0 _ hr0, subset_rfl⟩)
    obtain ⟨N, hN⟩ := pow_small hu (Units.mk0 _ hv0)
    rw [Units.val_mk0] at hN
    obtain ⟨m, hm1, hm2⟩ := (h1.and (Filter.eventually_ge_atTop N)).exists
    have hm1' : Valued.v (newtonSq u m * newtonSq u m - s * s) < Valued.v (s * s - u) := by
      have h5 := hm1
      simp only [Set.mem_setOf_eq, Units.val_mk0] at h5
      exact (Valuation.restrict_lt_iff _).mp h5
    have hb := (newton_bound u h2 hu m).2
    have h3 : Valued.v (newtonSq u m * newtonSq u m - u) < Valued.v (s * s - u) :=
      lt_of_le_of_lt (hb.trans (pow_anti hu.le (by omega))) hN
    have he : s * s - u = -((newtonSq u m * newtonSq u m) - s * s) + (newtonSq u m * newtonSq u m - u) := by
      ring
    have h4 : Valued.v (-((newtonSq u m * newtonSq u m) - s * s) + (newtonSq u m * newtonSq u m - u)) <
        Valued.v (s * s - u) := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ h3)
      rw [Valuation.map_neg]
      exact hm1'
    rw [← he] at h4
    exact lt_irrefl _ h4
  · have h1 := hs.eventually_mem (Valued.mem_nhds.mpr ⟨1, subset_rfl⟩)
    obtain ⟨m, hm⟩ := h1.exists
    have hm' : Valued.v (newtonSq u m - s) < 1 := by
      have h5 := hm
      simp only [Set.mem_setOf_eq, Units.val_one] at h5
      exact (Valuation.restrict_lt_one_iff _).mp h5
    have hb := (newton_bound u h2 hu m).1
    have he : s - 1 = -(newtonSq u m - s) + (newtonSq u m - 1) := by ring
    rw [he]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ hb)
    rw [Valuation.map_neg]
    exact hm'

end Formalism.IndefR.LocBrg
end
end

section

noncomputable section

namespace Formalism.IndefR.LocBrg

theorem finNormSurj : FinNormSurj := by
  intro k _ _ τ hτ hnt c hc hc0
  classical
  have hτu : ∀ x : kˣ, Units.map τ.toMonoidHom (Units.map τ.toMonoidHom x) = x := by
    intro x; ext; simp [hτ]
  let T : kˣ →* kˣ := Units.map τ.toMonoidHom
  let N : kˣ →* kˣ :=
    { toFun := fun x => T x * x
      map_one' := by simp
      map_mul' := by intro x y; simp only [map_mul]; exact mul_mul_mul_comm _ _ _ _ }
  let ψ : kˣ →* kˣ :=
    { toFun := fun x => x * (T x)⁻¹
      map_one' := by simp
      map_mul' := by intro x y; simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _ }
  have hTT : ∀ x, T (T x) = x := hτu
  have hT : ∀ x : kˣ, ((T x : kˣ) : k) = τ (x : k) := fun x => rfl
  have hψv : ∀ y : kˣ, ((ψ y : kˣ) : k) = (y : k) * (τ (y : k))⁻¹ := fun y => by
    show ((y * (T y)⁻¹ : kˣ) : k) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hT]
  have hkerψ : ∀ x, x ∈ ψ.ker ↔ T x = x := by
    intro x
    rw [MonoidHom.mem_ker]
    show x * (T x)⁻¹ = 1 ↔ T x = x
    rw [mul_inv_eq_one, eq_comm]
  have hrangeψ : ψ.range = N.ker := by
    ext x
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      show T (y * (T y)⁻¹) * (y * (T y)⁻¹) = 1
      rw [map_mul, map_inv, hTT]
      group
    · intro hx
      have hx' : T x * x = 1 := hx
      have hTx : (τ (x : k)) * (x : k) = 1 := by
        have := congrArg (fun u : kˣ => (u : k)) hx'
        simp only [Units.val_mul, Units.val_one, hT] at this
        exact this
      by_cases hm : (x : k) = -1
      · obtain ⟨θ, hθ⟩ := hnt
        have hy0 : θ - τ θ ≠ 0 := fun h => hθ (sub_eq_zero.1 h).symm
        refine ⟨Units.mk0 _ hy0, ?_⟩
        ext
        rw [hψv, Units.val_mk0]
        rw [map_sub, hτ, hm]
        have : τ θ - θ = -(θ - τ θ) := by ring
        rw [this, inv_neg, mul_neg, mul_inv_cancel₀ hy0]
      · have hy0 : (1 : k) + x ≠ 0 := by
          intro h; apply hm; linear_combination h
        refine ⟨Units.mk0 _ hy0, ?_⟩
        ext
        rw [hψv, Units.val_mk0]
        have hx0 : (x : k) ≠ 0 := x.ne_zero
        have hτx : τ (x : k) = (x : k)⁻¹ := eq_inv_of_mul_eq_one_left hTx
        rw [map_add (f := _), map_one, hτx]
        have h1 : (1 : k) + (x : k)⁻¹ = (1 + (x : k)) * (x : k)⁻¹ := by field_simp; ring
        rw [h1, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
  have hle : N.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hkerψ]
    show T (T x * x) = T x * x
    rw [map_mul, hTT, mul_comm]
  have hcardN := Subgroup.card_mul_index N.ker
  rw [Subgroup.index_ker] at hcardN
  have hcardψ := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hrangeψ] at hcardψ
  have hpos : 0 < Nat.card N.ker := Nat.card_pos
  have heq : Nat.card N.range = Nat.card ψ.ker := by
    have h := hcardN.trans hcardψ.symm
    rw [mul_comm (Nat.card ψ.ker)] at h
    exact (Nat.eq_of_mul_eq_mul_left hpos h)
  have hEq : N.range = ψ.ker := Subgroup.eq_of_le_of_card_ge hle heq.ge
  have hcu : Units.mk0 c hc0 ∈ ψ.ker := by
    rw [hkerψ]; ext; rw [hT, Units.val_mk0]; exact hc
  rw [← hEq] at hcu
  obtain ⟨x, hx⟩ := hcu
  refine ⟨(x : k), ?_⟩
  have := congrArg (fun u : kˣ => (u : k)) hx
  simp only [Units.val_mk0] at this
  rw [show ((N x : kˣ) : k) = τ (x : k) * (x : k) from rfl] at this
  exact this

end Formalism.IndefR.LocBrg
end
end
