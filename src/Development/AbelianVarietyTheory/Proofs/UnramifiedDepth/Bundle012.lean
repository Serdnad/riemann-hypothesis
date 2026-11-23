module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle005
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.RingTheory.Valuation.Basic
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainLemmaMultivariatePowerSeriesCoordinateForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle002

@[expose] public section

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

namespace GlobalTheory

namespace RadiiIdentities

theorem sub_one_pos {l : ℕ} (hl : 2 ≤ l) : (0 : ℝ) < (l : ℝ) - 1 := by
  have : (2 : ℝ) ≤ l := by exact_mod_cast hl
  linarith

theorem sq_sub_one_eq (l : ℕ) : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) := by
  ring

theorem exponent_integral : Formalism.L2.FormalSeriesBounds.EInt := by
  intro l i hl hi
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have hsq : ((l : ℝ) ^ 2 - 1) ≠ 0 := by
    rw [sq_sub_one_eq]
    have : (0 : ℝ) < (l : ℝ) + 1 := by linarith
    positivity
  constructor
  · simp only [gam, rho]
    field_simp
  · obtain ⟨k, rfl⟩ := hi
    have hk : (2 * k + 1 - 1) / 2 = k := by omega
    have hne : ((l : ℝ) ^ 2) ≠ 1 := by
      intro h
      apply hsq
      rw [h]
      ring
    simp only [expE, hk, Ereal, rho]
    push_cast
    rw [geom_sum_eq hne]
    field_simp
    ring

theorem radii_sum : I1 := by
  intro l i hl
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have h2 : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hpow : ((l : ℝ) ^ i) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [r1, r2]
    field_simp
    ring
  · simp only [Ereal, rho]
    rw [sq_sub_one_eq]
    field_simp
    ring

theorem slope_identity : I2 := by
  intro l i hl hi
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have h2 : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hsq : ((l : ℝ) ^ 2 - 1) = ((l : ℝ) - 1) * ((l : ℝ) + 1) := sq_sub_one_eq l
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hli : (l : ℝ) ≤ (l : ℝ) ^ i := by
    calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi
  refine ⟨?_, ?_⟩
  · simp only [Ereal, rho, gam]
    rw [hsq]
    field_simp
    ring
  · simp only [gam]
    rw [hsq, sub_nonneg, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith

theorem val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    calc (0 : WithTop ℝ) ≤ min (v (k : C)) (v 1) := by
          rw [AddValuation.map_one]
          exact le_min ih le_rfl
      _ ≤ v ((k : C) + 1) := AddValuation.map_add v _ _

theorem val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact_mod_cast val_natCast_nonneg v k
  · push_cast
    rw [AddValuation.map_neg]
    exact val_natCast_nonneg v k

theorem val_other_prime : ValOther := by
  intro C _ v l hl hvl p hp hpl
  refine le_antisymm ?_ (val_natCast_nonneg v p)
  by_contra hlt
  rw [not_le] at hlt
  have hcop : Nat.Coprime l p := (Nat.coprime_primes hl hp).2 (Ne.symm hpl)
  have hbez : ((1 : ℤ) : C) = ((l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p : ℤ) := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    simp
  push_cast at hbez
  have hA : (0 : WithTop ℝ) < v ((l : C) * (Nat.gcdA l p : C)) := by
    rw [AddValuation.map_mul, hvl]
    exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1))
      (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have hB : (0 : WithTop ℝ) < v ((p : C) * (Nat.gcdB l p : C)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have hsum := AddValuation.map_add v ((l : C) * (Nat.gcdA l p : C)) ((p : C) * (Nat.gcdB l p : C))
  rw [← hbez, AddValuation.map_one] at hsum
  exact absurd (lt_of_lt_of_le (lt_min hA hB) hsum) (lt_irrefl 0)

theorem weight_forms_agree : WeightConditionIff := by
  intro C _ v l i n0 h1
  have e1 : rho l + 1 / (2 * (l : ℝ) ^ i) - 1 / (8 * (l : ℝ) ^ i) =
      rho l + ((l : ℝ) ^ i)⁻¹ / 2 - ((l : ℝ) ^ i)⁻¹ / 8 := by ring
  have e2 : rho l + 1 / 2 - 1 / (8 * (l : ℝ) ^ i) = rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8 := by ring
  simp only [HM1, WeightCond, r1, r2, del, e1, e2]

theorem binomial_differences : F5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y s
    have hf : (s.factorial : ℚ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
    have key : (s.factorial : ℤ) * Ring.choose y s = ∏ j ∈ Finset.range s, (y - (j : ℤ)) := by
      rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
        Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
    rw [eq_div_iff hf, mul_comm]
    exact_mod_cast key
  · intro y s
    rw [Ring.choose_succ_succ]
    ring
  · intro y
    simp
  · intro s
    cases s with
    | zero => simp
    | succ k => simp [Ring.choose_zero_succ]

end RadiiIdentities


open RadiiIdentities in
theorem radii_valuation_differences :
    Formalism.L2.FormalSeriesBounds.EInt ∧ I1 ∧ I2 ∧ ValOther ∧ WeightConditionIff ∧ F5 :=
  ⟨exponent_integral, radii_sum, slope_identity, val_other_prime, weight_forms_agree,
    binomial_differences⟩

end GlobalTheory
end

section

open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory

private lemma sum_range_succ_choose_mul_eq_add_shift {C : Type} [Field C] (f : ℕ → C) (y : ℕ) :
    ∑ s ∈ Finset.range (y + 1 + 1), ((y + 1).choose s : C) * f s =
      ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * f s +
        ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * f (s + 1) := by
  rw [Finset.sum_range_succ' (fun s => ((y + 1).choose s : C) * f s)]
  simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun s => (y.choose s : C) * f s),
    Finset.sum_range_succ (fun s => (y.choose (s + 1) : C) * f (s + 1)), Nat.choose_succ_self]
  simp
  ring

theorem _root_.GlobalTheory.newtonBound_pos_and_newtonStep : _root_.Formalism.L2.FormalSeriesBounds.NewtonBoundPositive ∧ _root_.Formalism.L2.FormalSeriesBounds.P7 := by
  refine ⟨?_, ?_⟩
  · unfold _root_.Formalism.L2.FormalSeriesBounds.NewtonBoundPositive
    intro l hl i n0 s hi hn hs
    unfold _root_.Formalism.L2.FormalSeriesBounds.S0 at hs
    have hl' : (5:ℝ) ≤ l := by exact_mod_cast hl
    have hN : (1:ℝ) ≤ n0 := by exact_mod_cast hn
    have hi' : (1:ℝ) ≤ i := by exact_mod_cast hi
    have hlogl : 1 ≤ Real.log l := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hlbN1 : 0 ≤ Real.logb l ((n0:ℝ) + 1) := Real.logb_nonneg (by linarith) (by linarith)
    have hsK : 64 * (n0:ℝ) ^ 2 * ((i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1)) ≤ (s:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hs)
    have hN2 : 0 < 64 * (n0:ℝ) ^ 2 := by positivity
    set t : ℝ := (s:ℝ) / (64 * (n0:ℝ) ^ 2) with ht
    have hst : (s:ℝ) = t * 64 * (n0:ℝ) ^ 2 := by rw [ht]; field_simp
    have htK : (i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1) ≤ t := by
      rw [ht, le_div_iff₀ hN2]; linarith
    have ht0 : 0 < t := by linarith
    have hlogs : Real.logb l s = Real.logb l t + Real.logb l 64 + 2 * Real.logb l n0 := by
      rw [hst, Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by norm_num),
        Real.logb_pow]
      push_cast
      ring
    have hlbt : Real.logb l t ≤ t - 1 := by
      have h1 := Real.log_le_sub_one_of_pos ht0
      have h2 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    have hlb64 : Real.logb l 64 ≤ 3 := by
      have h3 : Real.logb l ((l:ℝ) ^ 3) = 3 := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by linarith)]
        norm_num
      rw [← h3]
      apply Real.logb_le_logb_of_le (by linarith) (by norm_num)
      have hcube : (5:ℝ) ^ 3 ≤ (l:ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hl' 3
      linarith
    have hlbN : Real.logb l n0 ≤ Real.logb l ((n0:ℝ) + 1) :=
      Real.logb_le_logb_of_le (by linarith) (by linarith) (by linarith)
    have key : 3 * Real.logb l n0 + 2 * Real.logb l s + i + 3 < 8 * t := by
      rw [hlogs]
      nlinarith
    have hs8 : (s:ℝ) / 8 = 8 * t * (n0:ℝ) ^ 2 := by rw [hst]; ring
    rw [hs8]
    have hpos : 0 < (n0:ℝ) ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left key hpos]
  · unfold _root_.Formalism.L2.FormalSeriesBounds.P7
    intro C _ v S a hS ha0 hpos Y0
    by_contra hcon
    push_neg at hcon
    have hadd : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x + y) := fun x y hx hy =>
      lt_of_lt_of_le (lt_min hx hy) (v.map_add x y)
    have hsub : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x - y) := fun x y hx hy => by
      rw [sub_eq_add_neg]
      exact hadd _ _ hx (by rwa [v.map_neg])
    have hnat : ∀ (c : ℕ) (x : C), 0 < v x → 0 < v ((c : C) * x) := fun c x hx => by
      rw [v.map_mul]
      have h := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v (c : ℤ)
      rw [Int.cast_natCast] at h
      exact lt_of_lt_of_le hx (le_add_of_nonneg_left h)
    have hsum : ∀ (s : Finset ℕ) (f : ℕ → C), (∀ j ∈ s, 0 < v (f j)) → 0 < v (∑ j ∈ s, f j) := by
      intro s f hf
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact hadd _ _ (hf j (Finset.mem_insert_self _ _))
          (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))
    set B : ℕ → ℕ → C := fun k y => ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * a (s + k) with hB
    have hpascal : ∀ k y, B (k + 1) y = B k (y + 1) - B k y := by
      intro k y
      simp only [hB]
      rw [sum_range_succ_choose_mul_eq_add_shift (fun s => a (s + k)) y]
      have : ∀ s, a (s + 1 + k) = a (s + (k + 1)) := fun s => by rw [add_assoc, add_comm 1 k]
      simp only [this]
      ring
    have hup : ∀ k, k < S → ∀ y, Y0 ≤ y → y + k < Y0 + S → 0 < v (B k y) := by
      intro k
      induction k with
      | zero =>
        intro _ y h1 h2
        simpa [hB] using hcon y h1 (by omega)
      | succ k ih =>
        intro hk y h1 h2
        rw [hpascal]
        exact hsub _ _ (ih (by omega) (y + 1) (by omega) (by omega)) (ih (by omega) y h1 (by omega))
    have hbig : ∀ k, S ≤ k → ∀ y, 0 < v (B k y) := fun k hk y =>
      hsum _ _ fun s _ => hnat _ _ (hpos _ (by omega))
    have hdown : ∀ d, d ≤ Y0 → ∀ k, 0 < v (B k (Y0 - d)) := by
      intro d
      induction d with
      | zero =>
        intro _ k
        by_cases hk : k < S
        · exact hup k hk Y0 le_rfl (by simpa using hk)
        · exact hbig k (by omega) _
      | succ d ih =>
        intro hd
        have hy : Y0 - d = Y0 - (d + 1) + 1 := by omega
        have main : ∀ m k, S ≤ k + m → 0 < v (B k (Y0 - (d + 1))) := by
          intro m
          induction m with
          | zero => intro k hk; exact hbig k (by omega) _
          | succ m ihm =>
            intro k hk
            have e := hpascal k (Y0 - (d + 1))
            have : B k (Y0 - (d + 1)) = B k (Y0 - (d + 1) + 1) - B (k + 1) (Y0 - (d + 1)) := by
              rw [e]; ring
            rw [this, ← hy]
            exact hsub _ _ (ih (by omega) k) (ihm (k + 1) (by omega))
        exact fun k => main S k (by omega)
    have h0 := hdown Y0 le_rfl 0
    simp [hB, ha0] at h0

end GlobalTheory
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

namespace GlobalTheory.LegendreFacts

open GlobalTheory.LegendreBounds

theorem mfact_eq_prod {σ : Type} [Fintype σ] (A : σ →₀ ℕ) :
    mfact A = ∏ j, (A j).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype A _ (fun _ => Nat.factorial_zero)

theorem capNat_mul (n0 x : ℕ) :
    capNat n0 x * ∏ c ∈ Finset.range n0, c.factorial
      = ∏ c ∈ Finset.range n0, (x + c).factorial := by
  unfold capNat
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro c _
  exact Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.le_add_left c x))

theorem capelli_bound : F3 := by
  intro l hl n0 n x hn hn0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have : Fact l.Prime := ⟨hl⟩
  constructor
  · have hP : (∏ c ∈ Finset.range n0, c.factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero c)
    have hC : capNat n0 x ≠ 0 := by
      intro h0
      have h := capNat_mul n0 x
      rw [h0, zero_mul] at h
      exact (Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero (x + c))) h.symm
    have hv : padicValNat l (capNat n0 x) + padicValNat l (∏ c ∈ Finset.range n0, c.factorial)
        = padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial) := by
      rw [← (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hC hP, capNat_mul]
    have hvR : (padicValNat l (capNat n0 x) : ℝ)
        = (padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial) : ℝ)
          - (padicValNat l (∏ c ∈ Finset.range n0, c.factorial) : ℝ) := by
      rw [← hv]
      push_cast
      ring
    have h := ((legendre_bounds l hl).2.2) n0 x
    rw [hvR]
    exact h
  · have hlogn : 0 ≤ Real.logb l n := Real.logb_nonneg hl1 (by exact_mod_cast hn)
    have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn0
    rcases Nat.eq_zero_or_pos n0 with h0 | hpos
    · subst h0
      have : (0 : ℝ) ≤ (n : ℝ) * (Real.logb l n + 1) := by positivity
      simpa using this
    · have hpos' : (0 : ℝ) < n0 := by exact_mod_cast hpos
      have hlog0 : 0 ≤ Real.logb l n0 := Real.logb_nonneg hl1 (by exact_mod_cast hpos)
      have hle : Real.logb l n0 ≤ Real.logb l n := Real.logb_le_logb_of_le hl1 hpos' hnn
      have : (n0 : ℝ) * (Real.logb l n0 + 1) ≤ n * (Real.logb l n + 1) :=
        mul_le_mul hnn (by linarith) (by linarith) (by positivity)
      linarith

end GlobalTheory.LegendreFacts
end

section

open ReciprocityTheory.PGsh

theorem _root_.GlobalTheory.T.determinantPairing_quotient_valuation_lower_bound : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (i n₀ s : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), 1 ≤ s → 1 ≤ n₀ →
    (∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (AddMonoidAlgebra.coeff Q A)) →
    (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (3 * Real.logb l n₀ + 2 * Real.logb l s + i + 3) : ℝ) : WithTop ℝ) ≤
      v ((∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) / (∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A))) := by
  first | exact @GlobalTheory.DetPairingBound.main | exact GlobalTheory.DetPairingBound.main | (intros; apply GlobalTheory.DetPairingBound.main <;> assumption)
end

section

open ReciprocityTheory.PGsh

theorem _root_.GlobalTheory.T.chainLemma_multivariatePowerSeries_coordinate_form : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 3 ≤ l → ∀ (d M s₀ : ℕ) (good : Set (Fin d)) (Gs : ℕ → Finset (Fin d)) (al : Fin d → ℕ → Fin d → C) (π : ℕ → Fin d → Fin M → C)
    (t : Fin d → MvPowerSeries (Fin M) C), (∀ s c, c ∈ Gs s → c ∈ good) → (∀ s s' c, s ≤ s₀ → s' ≤ s₀ → c ∈ Gs s → c ∈ Gs s' → s = s') →
    (∀ c e, al c 0 e = if c = e then 1 else 0) → (∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ c ∈ good, al c 1 = 0 ∧ ∀ (n : ℕ) e, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ s < s₀, ∀ c ∈ Gs s, ∀ e, e ∉ Gs (s + 1) → 0 ≤ v (al c 2 e)) →
    (∀ c j, 0 ≤ v (π 0 c j)) → (∀ c, c ∉ Gs 0 → π 0 c = 0) →
    (∀ s e j, π (s + 1) e j = ∑ c ∈ Gs s, (l : C) * al c 2 e * π s c j ^ (l ^ 2)) →
    (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ e, lgSum l al t e = ∑ j, MvPowerSeries.C (R := C) (π 0 e j) * MvPowerSeries.X j) →
    (∀ s ≤ s₀, ∀ c ∈ Gs s, OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c - ∑ j, MvPowerSeries.C (R := C) ((-1) ^ s * ((l : C) ^ (∑ u ∈ Finset.range s, (l ^ 2) ^ u))⁻¹ * π s c j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s)) (1 + 1 / ((l : ℝ) ^ 2 - 1))) ∧
    ∀ c, (∀ s ≤ s₀, c ∉ Gs s) → OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c) (1 + 1 / ((l : ℝ) ^ 2 - 1))) := by
  first | exact @GlobalTheory.ChainCoord.chain | exact GlobalTheory.ChainCoord.chain | (intros; apply GlobalTheory.ChainCoord.chain <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem dmonOf_mul_congr_of_congr :
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) := by
  intro R _ d F I ι _ u f f' g h mo
  have hsub : ∀ (m : ι →₀ ℕ) (a b : PS R 1 d),
      DmonOf F u m (a - b) = DmonOf F u m a - DmonOf F u m b := fun m a b => by
    have e := ExpCong.along_add (fun l => Dof F (u l)) (fun l => GE.dof_add F (u l))
      (ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (a - b) b
    rw [sub_add_cancel, ← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along,
      ← ExpCong.dmonOf_eq_along] at e
    rw [e, add_sub_cancel_right]
  have key := ExpCong.along_mul_mem (fun l => Dof F (u l)) (constantCoeff : PS R 1 d →+* R)
    (fun a => GE.dof_add F (u a)) (fun a => GE.dof_mul F (u a)) Set.univ I.toAddSubgroup
    (fun s _ j hj => I.mul_mem_left s hj)
    (ExpCong.grouped (Finset.univ : Finset ι).toList mo).reverse g (f - f')
    (fun _ _ => Set.mem_univ _)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F u mo v hv
      rw [hm', hsub, map_sub]
      exact h m')
  rw [← ExpCong.dmonOf_eq_along, show g * (f - f') = f * g - f' * g by ring, hsub, map_sub] at key
  exact key

end GlobalTheory
end
end
