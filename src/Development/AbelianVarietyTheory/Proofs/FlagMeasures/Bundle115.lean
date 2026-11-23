module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle102
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Mathlib.LinearAlgebra.PID
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007

@[expose] public section

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem isChar_trace_of_mul {M V : Type} [Group M] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : M → Module.End ℂ V) (hT : ∀ a b, T (a * b) = T a * T b) :
    IsChar (fun m => LinearMap.trace ℂ V (T m)) := by
  have hmem : ∀ m v, T m v ∈ LinearMap.range (T 1) := fun m v =>
    ⟨T m v, by rw [← Module.End.mul_apply, ← hT, one_mul]⟩
  let ρ : Representation ℂ M (LinearMap.range (T 1)) :=
    { toFun := fun m => (T m).restrict (fun v _ => hmem m v)
      map_one' := by
        refine LinearMap.ext ?_
        rintro ⟨_, v, rfl⟩
        refine Subtype.ext ?_
        show T 1 (T 1 v) = T 1 v
        rw [← Module.End.mul_apply, ← hT, one_mul]
      map_mul' := fun a b => by
        refine LinearMap.ext fun v => Subtype.ext ?_
        show T (a * b) v = T a (T b v)
        rw [hT]; rfl }
  refine ⟨FDRep.of ρ, fun m => ?_⟩
  exact LinearMap.trace_restrict_eq_of_forall_mem _ (T m) (hmem m) (fun v _ => hmem m v)

theorem sum_fibre_one {P M : Type} [Group P] [Fintype P] [Group M] (π : P →* M) (hπ : Function.Surjective π)
    (m : M) : (∑ x : P, if π x = m then (1 : ℂ) else 0) = (Nat.card π.ker : ℂ) := by
  obtain ⟨x₀, rfl⟩ := hπ m
  rw [← Equiv.sum_comp (Equiv.mulLeft x₀)]
  simp only [Equiv.coe_mulLeft, map_mul, mul_eq_left]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [MonoidHom.mem_ker]

theorem isChar_fibre_mean : ∀ (P M : Type) [Group P] [Fintype P] [Group M] [Fintype M] (π : P →* M) (χ : P → ℂ),
    Function.Surjective π → IsChar χ →
    IsChar (fun m : M => (Nat.card π.ker : ℂ)⁻¹ * ∑ x : P, if π x = m then χ x else 0) := by
  intro P M _ _ _ _ π χ hπ ⟨V, hV⟩
  have hc : (Nat.card π.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let S : M → Module.End ℂ V := fun m => ∑ x : P, if π x = m then V.ρ x else 0
  have hS : ∀ a b, S a * S b = (Nat.card π.ker : ℂ) • S (a * b) := by
    intro a b
    rw [← sum_fibre_one π hπ a, Finset.sum_smul]
    simp only [S]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : π x = a
    · rw [if_pos hx, if_pos hx, one_smul, Finset.mul_sum,
        ← Equiv.sum_comp (Equiv.mulLeft x) (fun y => if π y = a * b then V.ρ y else 0)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Equiv.coe_mulLeft, map_mul, hx, mul_right_inj]
      split_ifs <;> simp
    · rw [if_neg hx, if_neg hx, zero_mul, zero_smul]
  have h := isChar_trace_of_mul (fun m => (Nat.card π.ker : ℂ)⁻¹ • S m) (fun a b => by
    rw [smul_mul_smul_comm, hS, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one])
  convert h using 2 with m
  rw [map_smul, smul_eq_mul]
  congr 1
  simp only [S]

  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [← hV]; rfl
  · simp

end GlobalTheory.GLm
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, IsIntLat h M → ∃ M', IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → IsUnimodular h M → IsMaxLat h M ∧ badP h M = ∅ ∧ lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), IsOrthoLattice h M n → Submodule.IsLattice K M ∧ IsUnimodular h M ∧ Module.finrank K V = n) := by
  first
  | exact @GlobalTheory.Mass.MaxExists.main
  | intro K V _ _ _ _ _ _ _ _ h hK hS hN
    have result := GlobalTheory.Mass.MaxExists.main K V h hK hS hN
    exact ⟨result.1, fun M hL hU => result.2.1 M hL.toIsLattice hU, result.2.2⟩
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DoubledFlag


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.DoubledFlag.sum_range_double {M : Type} [AddCommMonoid M] (a : ℕ) (f : ℕ → M) :
    ∑ s ∈ range (2 * a + 1), f s = ∑ i : Fin a, (f i + f (2 * a - i)) + f a := by
  rw [show 2 * a + 1 = (a + 1) + a by ring, Finset.sum_range_add, Finset.sum_range_succ,
    Fin.sum_univ_eq_sum_range (fun i => f i + f (2 * a - i)), Finset.sum_add_distrib,
    ← Finset.sum_range_reflect (fun x => f (a + 1 + x)) a]
  have h : ∀ x ∈ range a, f (a + 1 + (a - 1 - x)) = f (2 * a - x) := fun x hx => by
    rw [Finset.mem_range] at hx; congr 1; omega
  rw [Finset.sum_congr rfl h]
  abel


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq : ∀ (n a : ℕ) (j : Fin a → ℕ) (D : ℕ → ℝ) (ν : ℕ → ℕ), (∀ i, 1 ≤ j i) → (∀ s, 0 < D s) → D 0 = 1 → ν 0 = 0 → (∀ i : Fin a, ν (i + 1) = ν i + j i) → 2 * ν a ≤ n → (∀ s, s ≤ a → D (2 * a + 1 - s) = D s ∧ ν (2 * a + 1 - s) + ν s = n) → ∑ s ∈ Finset.range (2 * a + 1), (ν (s + 1) - ν s) * ν s = _root_.GlobalTheory.FlagMeas.dimN n j ∧ _root_.GlobalTheory.Count.layerProd n 1 j (fun i : Fin a => (D (i + 1) / D i) ^ (-(1 : ℝ) / j i)) id = (∏ s ∈ Finset.range (2 * a + 1), D s ^ ν (s + 1) / D (s + 1) ^ ν s)⁻¹ := by
  intro n a j D ν hj hD hD0 hν0 hν hna hsym
  have hJ : ν a = ∑ i, j i := by
    have h1 : ∀ m, m ≤ a → ν m = ∑ i ∈ range m, if h : i < a then j ⟨i, h⟩ else 0 := by
      intro m hm
      induction m with
      | zero => simp [hν0]
      | succ m ih =>
        rw [Finset.sum_range_succ, ← ih (by omega), dite_eq_left (by omega)]
        exact hν ⟨m, by omega⟩
    rw [h1 a le_rfl, ← Fin.sum_univ_eq_sum_range (fun i => if h : i < a then j ⟨i, h⟩ else 0)]
    simp
  have hmid : ν (a + 1) + ν a = n := by
    have h := (hsym a le_rfl).2
    rwa [show 2 * a + 1 - a = a + 1 by omega] at h
  have hlow : ∀ i : Fin a, (ν (i + 1) - ν i) * ν i = j i * ν i := by
    intro i; rw [hν i, Nat.add_sub_cancel_left]
  have hhigh : ∀ i : Fin a, (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i) + j i * ν (i + 1)
      = j i * n := by
    intro i
    have hi := i.isLt
    have h1 := (hsym i (by omega)).2
    have h2 := (hsym (i + 1) (by omega)).2
    have h3 := hν i
    rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
    rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
    rw [show ν (2 * a - i + 1) - ν (2 * a - i) = j i by omega, ← mul_add, h2]
  have hsq : ν a * ν a = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
    have hsplit : ∀ i k : Fin a, j i * j k = ((if i < k then j i * j k else 0) +
        (if k < i then j k * j i else 0)) + (if i = k then j i ^ 2 else 0) := by
      intro i k
      rcases lt_trichotomy i k with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h; simp [sq]
      · simp [h, h.ne', not_lt.2 h.le]; ring
    rw [hJ, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsplit i k]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_filter, Finset.mem_univ, if_true]
    rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
    ring
  refine ⟨?_, ?_⟩
  · rw [_root_.GlobalTheory.DoubledFlag.sum_range_double]
    have hF : ∑ i : Fin a, ((ν (i + 1) - ν i) * ν i + (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i))
        + ∑ i, j i ^ 2 = n * ν a := by
      rw [← Finset.sum_add_distrib, hJ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := hhigh i
      rw [hν i] at h
      rw [hlow i]
      nlinarith
    unfold _root_.GlobalTheory.FlagMeas.dimN
    rw [← hJ]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * ν a := ⟨n - 2 * ν a, by omega⟩
    rw [show ν (a + 1) - ν a = m by omega, show m + 2 * ν a - 2 * ν a = m by omega]
    nlinarith
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ → ℝ, D = fun s => Real.exp (d s) :=
      ⟨fun s => Real.log (D s), funext fun s => (Real.exp_log (hD s)).symm⟩
    have hd0 : d 0 = 0 := by simpa using hD0
    have hdsym : ∀ s, s ≤ a → d (2 * a + 1 - s) = d s := fun s hs => by
      simpa using (hsym s hs).1
    have hc : ∀ i : Fin a, (Real.exp (d (i + 1)) / Real.exp (d i)) ^ (-(1 : ℝ) / j i)
        = Real.exp ((d i - d (i + 1)) / j i) := by
      intro i
      rw [← Real.exp_sub, ← Real.exp_mul]
      congr 1
      ring
    have htail : ∀ i : Fin a, ∑ k ∈ univ.filter (fun k => i < k), (j k : ℝ) = ν a - ν ((i : ℕ) + 1) := by
      intro i
      have hi := i.isLt
      have e : ∀ k : Fin a, (j k : ℝ) = ν ((k : ℕ) + 1) - ν k := fun k => by
        rw [hν k]; push_cast; ring
      simp only [e, Finset.sum_filter, Fin.lt_iff_val_lt_val]
      rw [Fin.sum_univ_eq_sum_range (fun x => if (i : ℕ) < x then (ν (x + 1) : ℝ) - ν x else 0) a,
        ← Finset.sum_filter,
        show (range a).filter (fun x => (i : ℕ) < x) = Ico ((i : ℕ) + 1) a by
          ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega,
        Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_range_sub (fun x => (ν x : ℝ)),
        Finset.sum_range_sub (fun x => (ν x : ℝ))]
      ring
    simp only [hc]
    unfold _root_.GlobalTheory.Count.layerProd
    simp only [id, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add, ← Real.exp_sum, ← Real.exp_neg,
      pow_one, mul_one]
    rw [Real.exp_eq_exp, ← hJ, _root_.GlobalTheory.DoubledFlag.sum_range_double, eq_neg_iff_add_eq_zero, ← add_assoc,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr (s₁ := (univ : Finset (Fin a))) rfl (g := fun i : Fin a =>
        (2 * (ν ((i : ℕ) + 1) : ℝ) * d ((i : ℕ) + 1) - n * d ((i : ℕ) + 1)) - (2 * (ν i : ℝ) * d i - n * d i)) ?_,
      Fin.sum_univ_eq_sum_range (fun x => (2 * (ν (x + 1) : ℝ) * d (x + 1) - n * d (x + 1)) - (2 * (ν x : ℝ) * d x - n * d x)),
      Finset.sum_range_sub (fun x => 2 * (ν x : ℝ) * d x - n * d x)]
    · have hm : (ν (a + 1) : ℝ) = n - ν a := by rw [eq_sub_iff_add_eq]; exact_mod_cast hmid
      have hda : d (a + 1) = d a := by rw [← hdsym a le_rfl]; congr 1; omega
      rw [hm, hda, hν0, hd0]
      push_cast
      ring
    · intro i _
      have hi := i.isLt
      have hji : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
      have h1 := (hsym i (by omega)).2
      have h2 := (hsym (i + 1) (by omega)).2
      rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
      rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
      have e1 : (ν (2 * a - i + 1) : ℝ) = n - ν i := by rw [eq_sub_iff_add_eq]; exact_mod_cast h1
      have e2 : (ν (2 * a - i) : ℝ) = n - ν ((i : ℕ) + 1) := by rw [eq_sub_iff_add_eq]; exact_mod_cast h2
      have e3 : (ν ((i : ℕ) + 1) : ℝ) = ν i + j i := by exact_mod_cast hν i
      have f1 : d (2 * a - i + 1) = d i := by rw [← hdsym i (by omega)]; congr 1; omega
      have f2 : d (2 * a - i) = d ((i : ℕ) + 1) := by rw [← hdsym (i + 1) (by omega)]; congr 1; omega
      rw [Finset.sum_congr rfl (g := fun k => 4 * (d i - d ((i : ℕ) + 1)) * (j k : ℝ))
          fun k _ => by push_cast; field_simp; ring, ← Finset.mul_sum, htail i, e1, e2, f1, f2, e3]
      push_cast [Nat.cast_sub hna]
      field_simp
      ring

end GlobalTheory.DoubledFlag
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SphRatio

theorem sphV_succ (i : ℕ) :
    sphV (i + 1) = sphV i * (2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) := by
  unfold sphV
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem sphV_pos (i : ℕ) : 0 < sphV i := by
  unfold sphV
  exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity

theorem log_factor_le (n m : ℕ) (a : ℝ) (hn : 18 ≤ n) (ha : a ≤ m) (hm : (n : ℝ) / 2 ≤ m) :
    Real.log (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ)) ≤
      Real.log (2 * Real.pi) - a * Real.log (n / (2 * Real.pi * Real.exp 1)) := by
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  have hn' : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by linarith
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hc : 2 * Real.pi * Real.exp 1 ≤ n := by
    have h1 := Real.pi_lt_d2
    have h2 := Real.exp_one_lt_d9
    nlinarith
  have hL : 0 ≤ Real.log (n / (2 * Real.pi * Real.exp 1)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have h1 : (m : ℝ) ^ m / m.factorial ≤ Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp _ hm0.le m
  have h2 : 2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) ≤
      (2 * Real.pi) * ((n / (2 * Real.pi * Real.exp 1))⁻¹) ^ m := by
    have h3 : Real.pi * Real.exp 1 / m ≤ (n / (2 * Real.pi * Real.exp 1))⁻¹ := by
      rw [inv_div, div_le_div_iff₀ hm0 (by linarith)]
      have : 0 < Real.pi * Real.exp 1 := by positivity
      nlinarith
    calc 2 * Real.pi ^ (m + 1) / (m.factorial : ℝ)
        = (2 * Real.pi) * ((Real.pi / m) ^ m * ((m : ℝ) ^ m / m.factorial)) := by
          rw [div_pow, pow_succ]; field_simp
      _ ≤ (2 * Real.pi) * ((Real.pi / m) ^ m * Real.exp 1 ^ m) := by gcongr
      _ = (2 * Real.pi) * (Real.pi * Real.exp 1 / m) ^ m := by
          rw [← mul_pow]; congr 2; ring
      _ ≤ _ := by gcongr
  refine (Real.log_le_log (by positivity) h2).trans ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv]
  nlinarith

theorem log_ratio_add_le (n q : ℕ) (a : ℝ) (hn : 18 ≤ n) (ha : a ≤ q) (hq : (n : ℝ) / 2 ≤ q)
    (j : ℕ) : Real.log (sphV (q + j) / sphV q) ≤
      j * (Real.log (2 * Real.pi) - a * Real.log (n / (2 * Real.pi * Real.exp 1))) := by
  induction j with
  | zero => simp [(sphV_pos q).ne']
  | succ j ih =>
    have hpi := Real.pi_pos
    have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h := log_factor_le n (q + j) a hn (by push_cast; linarith) (by push_cast; linarith)
    have h1 := sphV_pos (q + j)
    have h2 := sphV_pos q
    rw [← add_assoc, sphV_succ, mul_div_right_comm,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    linarith

theorem log_sphV_ratio_le : ∀ (n p j : ℕ), 18 ≤ n → j ≤ p → p ≤ n → (n : ℝ) - 2 * Real.sqrt n ≤ (p : ℝ) - j → (n : ℝ) / 2 ≤ (p : ℝ) - j → Real.log (sphV p / sphV (p - j)) ≤ j * Real.log (2 * Real.pi) - j * ((n : ℝ) - 2 * Real.sqrt n) * Real.log (n / (2 * Real.pi * Real.exp 1)) := by
  intro n p j hn hj _ ha hq
  have hc : ((p - j : ℕ) : ℝ) = (p : ℝ) - j := Nat.cast_sub hj
  have h := log_ratio_add_le n (p - j) _ hn (hc ▸ ha) (hc ▸ hq) j
  rw [Nat.sub_add_cancel hj] at h
  linarith

end GlobalTheory.SphRatio
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.FlagMeas.measurable_detOn_comp {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ}
    (f : X → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f) (V : Submodule ℂ (Fin n → ℂ)) :
    Measurable fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V := by
  classical
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  let P := Submodule.linearProjOfIsCompl V W hW
  let b := Module.finBasis ℂ V
  let g : X → ℂ := fun x =>
    (Matrix.of fun i k => b.repr (P (f x *ᵥ (b k : Fin n → ℂ))) i).det
  have hg : Continuous g := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i k => ?_
    have hL : Continuous fun v : Fin n → ℂ => b.repr (P v) i :=
      (((Finsupp.lapply i).comp b.repr.toLinearMap).comp P).continuous_of_finiteDimensional
    exact hL.comp (hf.matrix_mulVec continuous_const)
  have hS : IsClosed {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := by
    simp only [Set.setOf_forall]
    refine isClosed_biInter fun y _ => ?_
    exact V.closed_of_finiteDimensional.preimage (hf.matrix_mulVec continuous_const)
  have heq : (fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V) =
      fun x => if x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} then ‖g x‖ else 0 := by
    funext x
    unfold _root_.GlobalTheory.FlagMeas.detOn
    by_cases h : ∀ y ∈ V, (toLin' (f x)) y ∈ V
    · have h' : x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun y hy => by
        simpa [Matrix.toLin'_apply] using h y hy
      rw [dite_eq_left h, if_pos h', ← LinearMap.det_toMatrix b]
      congr 2
      ext i k
      rw [LinearMap.toMatrix_apply, Matrix.of_apply]
      congr 2
      have hm : f x *ᵥ (b k : Fin n → ℂ) = ((toLin' (f x)).restrict h (b k) : Fin n → ℂ) := by
        simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
      rw [hm]
      exact (Submodule.projectionOnto_apply_left hW _).symm
    · have h' : x ∉ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun hx => h fun y hy => by
        simpa [Matrix.toLin'_apply] using hx y hy
      rw [dite_eq_right h, if_neg h']
  rw [heq]
  exact Measurable.ite hS.measurableSet hg.norm.measurable measurable_const


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.FlagMeas.measurable_locSize_uMat (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (i : Fin a) :
    Measurable fun g : _root_.Formalism.REAL.UJ ε => _root_.GlobalTheory.FlagMeas.locSize j W (_root_.Formalism.MainNotions.S.uMat g) i := by
  have hc : Continuous fun g : _root_.Formalism.REAL.UJ ε => _root_.Formalism.MainNotions.S.uMat g := by
    unfold _root_.Formalism.MainNotions.S.uMat
    exact Units.continuous_val.comp continuous_subtype_val
  unfold _root_.GlobalTheory.FlagMeas.locSize
  exact ((_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _).div
    (_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _)).pow_const _

end GlobalTheory.FlagMeas
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem covol_prod_le_tsum_slices : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂] [MeasurableMul G₂] (μ₁ : Measure G₁) (μ₂ : Measure G₂) [SigmaFinite μ₁] [SigmaFinite μ₂] [μ₂.IsMulLeftInvariant] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (A : Set (G₁ × G₂)) (ι : Type) [Countable ι] (x : ι → G₂) (Γc Ac : ι → Set G₁), MeasurableSet (K : Set G₂) → (∀ c, ∀ g ∈ Γc c, ∃ γ ∈ Γ, γ.1 = g ∧ (x c)⁻¹ * γ.2 * x c ∈ K) → (∀ y ∈ A, ∃ c, ∃ γ ∈ Γ, ∃ k ∈ K, γ.2 * y.2 = x c * k ∧ γ.1 * y.1 ∈ Ac c) → μ₂ K ≠ ⊤ → covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤ μ₂ K * ∑' c, covol (Γc c) μ₁ (Ac c) := by
  intro G₁ G₂ _ _ _ _ _ μ₁ μ₂ _ _ _ Γ K A ι _ x Γc Ac hK hΓ hA hfin
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hb => ?_
  obtain ⟨ε', hε', hsum⟩ := ENNReal.exists_pos_sum_of_countable (ε := (ε : ENNReal))
    (by exact_mod_cast hε.ne') ι
  have key : ∀ c, ∃ D : Set G₁, MeasurableSet D ∧
      μ₂ K * μ₁ D ≤ μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c ∧
      (D = Set.univ ∨ ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D) := by
    intro c
    by_cases h0 : μ₂ K = 0
    · exact ⟨Set.univ, MeasurableSet.univ, by simp [h0], Or.inl rfl⟩
    · have hc : μ₂ K * covol (Γc c) μ₁ (Ac c) ≠ ⊤ :=
        ne_top_of_le_ne_top hb.ne (by
          gcongr
          exact le_tsum (fun i => covol (Γc i) μ₁ (Ac i)) c)
      have hlt : μ₂ K * covol (Γc c) μ₁ (Ac c) < μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c :=
        ENNReal.lt_add_right hc (by exact_mod_cast (hε' c).ne')
      have h2 : μ₂ K * covol (Γc c) μ₁ (Ac c) = ⨅ (D : Set G₁) (_ : MeasurableSet D)
          (_ : ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D), μ₂ K * μ₁ D := by
        simp only [covol, ENNReal.mul_iInf_of_ne h0 hfin]
      rw [h2] at hlt
      simp only [iInf_lt_iff] at hlt
      obtain ⟨D, hD, hcov, hlt⟩ := hlt
      rw [← h2] at hlt
      exact ⟨D, hD, hlt.le, Or.inr hcov⟩
  choose D hDm hDle hDcov using key
  have hKm : ∀ c, MeasurableSet ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)) := fun c =>
    measurable_const_mul _ hK
  have h1 : covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤
      (μ₁.prod μ₂) (⋃ c, D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂))) := by
    refine iInf_le_of_le _ (iInf_le_of_le (MeasurableSet.iUnion fun c => (hDm c).prod (hKm c))
      (iInf_le_of_le ?_ le_rfl))
    intro y hy
    obtain ⟨c, γ, hγ, k, hk, h2, h1⟩ := hA y hy
    rcases hDcov c with hu | hcov
    · refine ⟨γ, hγ, Set.mem_iUnion.2 ⟨c, by simp [hu], ?_⟩⟩
      simpa [h2] using hk
    · obtain ⟨g, hg, hgD⟩ := hcov _ h1
      obtain ⟨δ, hδ, rfl, hδK⟩ := hΓ c g hg
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, Set.mem_iUnion.2 ⟨c, by simpa [mul_assoc] using hgD, ?_⟩⟩
      have := K.mul_mem hδK hk
      simpa [mul_assoc, h2] using this
  refine h1.trans ((measure_iUnion_le _).trans ?_)
  calc ∑' c, (μ₁.prod μ₂) (D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)))
      ≤ ∑' c, (μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c) := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        rw [Measure.prod_prod, measure_preimage_mul, mul_comm]
        exact hDle c
    _ ≤ _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        exact add_le_add le_rfl hsum.le

end GlobalTheory.FlagMeas
end
