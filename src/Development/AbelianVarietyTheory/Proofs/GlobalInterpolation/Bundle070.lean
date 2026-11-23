module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle066
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero

variable {E : Type} [Field E] [NumberField E]

theorem isUnit_reduction_of_valuation_eq_one (P : HeightOneSpectrum (𝓞 E)) {b : E} (hb : P.valuation E b = 1) :
    IsUnit (redP P b) := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have h1 : IntAt P b := (IntegralPowerExpansion.intAt_iff_val P b).2 hb.le
  have h2 : IntAt P b⁻¹ := (IntegralPowerExpansion.intAt_iff_val P _).2 (by rw [map_inv₀, hb, inv_one])
  have h3 := reduction_mul h1 h2
  have h4 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [mul_inv_cancel₀ hb0, h4] at h3
  exact IsUnit.of_mul_eq_one _ h3.symm

theorem exists_isUnit_reduction_div_pow {P : HeightOneSpectrum (𝓞 E)} (hP : GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {a : E} (ha : a ≠ 0) :
    ∃ z : ℤ, IsUnit (redP P (a / (qOf P : E) ^ z)) := by
  have hv : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  refine ⟨-WithZero.log (P.valuation E a), isUnit_reduction_of_valuation_eq_one P ?_⟩
  rw [map_div₀, map_zpow₀, IntegralPowerExpansion.val_q hP, ← WithZero.exp_zsmul]
  simp only [smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one, mul_neg, neg_mul]
  rw [WithZero.exp_log hv, div_self hv]

theorem locChar_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), cq ≠ 0 → a ≠ 0 →
      LocE.locChar (qOf P) cq χ a ≠ 0 := by
  intro E _ _ K _ P hP cq χ a hcq ha
  have h : IsUnit (redP P (a / (qOf P : E) ^ LocE.vP P (qOf P) a)) :=
    Classical.epsilon_spec (exists_isUnit_reduction_div_pow hP ha)
  unfold LocE.locChar LocE.unitV
  rw [dite_eq_left h]
  exact mul_ne_zero (zpow_ne_zero _ hcq) (Units.ne_zero _)

end GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero
end

section

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient

open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.Proof.IntegralPowerExpansion

variable {E : Type} [Field E] [NumberField E]

theorem intAt_int (P : HeightOneSpectrum (𝓞 E)) (n : ℤ) : IntAt P (n : E) := by
  simpa using IntAt.coe P (n : 𝓞 E)

theorem q_dvd_of_intAt {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) {n : ℤ}
    (h : IntAt P ((qOf P : E)⁻¹ * n)) : (qOf P : ℤ) ∣ n := by
  by_contra hn
  have hpr : Prime (qOf P : ℤ) := Nat.prime_iff_prime_int.1 hP.1
  obtain ⟨x, y, hxy⟩ := (hpr.coprime_iff_not_dvd).2 hn
  have hq := q_ne_zero hP
  have h1 : IntAt P ((qOf P : E)⁻¹) := by
    have e : (qOf P : E)⁻¹ = x + y * ((qOf P : E)⁻¹ * n) := by
      have := congrArg (Int.cast : ℤ → E) hxy
      push_cast at this
      field_simp
      linear_combination -this
    rw [e]
    exact (intAt_int P x).add ((intAt_int P y).mul h)
  rw [intAt_iff_val, map_inv₀, val_q hP, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem q_pow_dvd_of_intAt {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) (k : ℕ) {n : ℤ}
    (h : IntAt P (((qOf P : E) ^ k)⁻¹ * n)) : (qOf P : ℤ) ^ k ∣ n := by
  have hq := q_ne_zero hP
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have h1 : IntAt P ((qOf P : E)⁻¹ * n) := by
      have e : (qOf P : E)⁻¹ * n = (((qOf P : ℤ) ^ k : ℤ) : E) * (((qOf P : E) ^ (k + 1))⁻¹ * n) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact (intAt_int P _).mul h
    obtain ⟨m, rfl⟩ := q_dvd_of_intAt hP h1
    have e : ((qOf P : E) ^ (k + 1))⁻¹ * (((qOf P : ℤ) * m : ℤ) : E) = ((qOf P : E) ^ k)⁻¹ * m := by
      push_cast
      field_simp
      ring
    rw [e] at h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h)

theorem valsQ_reps : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ,
    (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B,
      IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧
    ∀ a : E, IntAt P ((qOf P : E) ^ A * a) →
      ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s)) := by
  intro E _ _ P hP A B
  classical
  have hq := q_ne_zero hP
  constructor
  · intro a ha b hb h
    unfold LocE.valsQ at ha hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
    rw [Finset.mem_range] at hi hj
    have h1 : IntAt P (((qOf P : E) ^ (A + B))⁻¹ * (((i : ℤ) - j : ℤ) : E)) := by
      convert h using 1
      push_cast
      field_simp
      ring
    have h2 := q_pow_dvd_of_intAt hP _ h1
    have hi' : (i : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast hi
    have hj' : (j : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast hj
    have h3 : (i : ℤ) - j = 0 := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
    have h4 : i = j := by omega
    rw [h4]
  · intro a ha
    obtain ⟨k, u, hu, e⟩ := exists_int_add_q_pow_mul hP (A + B) ha
    have hpos : (0 : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast pow_pos hP.1.pos (A + B)
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg k hpos.ne')
    have hlt : i < qOf P ^ (A + B) := by
      have := Int.emod_lt_of_pos k hpos
      rw [hi] at this
      exact_mod_cast this
    have hk : (k : E) = i + (qOf P : E) ^ (A + B) * ((k / (qOf P : ℤ) ^ (A + B) : ℤ) : E) := by
      have := Int.emod_add_mul_ediv k ((qOf P : ℤ) ^ (A + B))
      rw [hi] at this
      have h5 := congrArg (Int.cast : ℤ → E) this
      rw [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_natCast] at h5
      exact h5.symm
    unfold LocE.valsQ
    refine ⟨_, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hlt, rfl⟩, ?_⟩
    have h6 := (intAt_int P (k / (qOf P : ℤ) ^ (A + B))).add hu
    generalize ((k / (qOf P : ℤ) ^ (A + B) : ℤ) : E) = m at hk h6
    have ea : a = ((qOf P : E) ^ A)⁻¹ * (i + (qOf P : E) ^ (A + B) * (m + u)) := by
      rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hq), e, hk]
      ring
    convert h6 using 1
    rw [ea]
    field_simp
    ring

end GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient
end

section

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.norm_psi0_add_zsum_le : ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  first | exact @GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed | exact GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed | (intros; apply GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem lA_le_pow_seven {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (hV : Val C cD ch L) :
    lA L ≤ L.sc.x ^ (7 : ℝ) := by
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hk : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ) := by
    have h1 := hV.ranks.2.2.1.2
    have h2 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by
      have := D.R.two_le_m
      have := D.R.m_le_f
      unfold Ranks.n
      omega
    exact_mod_cast this
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact hV.host.2.2.1
  have hd' : L.sc.x ^ (-1 : ℝ) ≤ L.de2 :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) hd
  have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hdp := L.thickDensity_pos
  unfold lA
  rw [div_le_iff₀ (by positivity)]
  have e7 : L.sc.x ^ (7 : ℝ) * L.sc.x ^ (-1 : ℝ) = L.sc.x ^ (5 : ℝ) * L.sc.x ^ (1 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  calc (D.R.k : ℝ) * L.sc.x ^ L.sc.eps ≤ (2 * L.sc.x ^ (5 : ℝ)) * L.sc.x ^ (1 : ℝ) := by gcongr
    _ = L.sc.x ^ (7 : ℝ) * (2 * L.sc.x ^ (-1 : ℝ)) := by
        rw [mul_assoc, ← e7]; ring
    _ ≤ L.sc.x ^ (7 : ℝ) * ((D.R.m : ℝ) * L.de2) := by gcongr

theorem nN_div_m_le {C : FC} (hCt : C.Ct = 401) {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (hV : Val C cD ch L) :
    (D.R.n : ℝ) * D.R.N D.R.m / D.R.m ≤ 4 * L.sc.x ^ (404 : ℝ) := by
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hn : (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (3 : ℝ) := by
    have h1 := hV.ranks.n_le'
    have h2 : L.sc.x ^ ((9 : ℝ) / 4) ≤ L.sc.x ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    linarith
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ (401 : ℝ) := by
    have h := L.t_win.2
    rwa [hV.Ct_eq, hCt] at h
  have hm2 := D.R.two_le_m
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hN : D.R.N D.R.m ≤ 2 * D.R.t * D.R.m := by
    have h := D.R.rank_add_five_le
    have h1 : D.R.k + 1 ≤ D.R.t := by omega
    unfold Ranks.N
    nlinarith
  have hN' : (D.R.N D.R.m : ℝ) ≤ 2 * D.R.t * D.R.m := by exact_mod_cast hN
  rw [div_le_iff₀ hm]
  have e : L.sc.x ^ (404 : ℝ) = L.sc.x ^ (3 : ℝ) * L.sc.x ^ (401 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  calc (D.R.n : ℝ) * D.R.N D.R.m ≤ (2 * L.sc.x ^ (3 : ℝ)) * (2 * D.R.t * D.R.m) := by gcongr
    _ ≤ (2 * L.sc.x ^ (3 : ℝ)) * (2 * L.sc.x ^ (401 : ℝ) * D.R.m) := by gcongr
    _ = 4 * L.sc.x ^ (404 : ℝ) * D.R.m := by rw [e]; ring

theorem szRow_windowLength : SzRow (fun C D L => (∀ l : ℕ, 11 ≤ l → ∃ j : ℕ, lA L ≤ ((l : ℝ) - 1) ^ j ∧ 2 * j + 2 ≤ D.host.Lw) ∧ ((D.host.Lw : ℝ) ≤ C.P.CLw * Real.log L.sc.x) ∧ ((L.j0 : ℝ) ≤ C.P.Cj0 * Real.log L.sc.x)) := by
  intro eps h0 h1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (60 / eps + 34), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog : 60 / eps + 34 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hq : 0 < 60 / eps := by positivity
  have hLw : D.host.Lw = Lwv L.sc := hV.host.2.2.2.2.2.1
  have hCt : C.Ct = 401 := by
    have h := hC.1
    unfold FC.Fixed at h
    tauto
  refine ⟨fun l hl => ⟨⌈7 * Real.log L.sc.x⌉₊, ?_, ?_⟩, ?_, ?_⟩
  · have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
    have he1 : Real.exp 1 ≤ (l : ℝ) - 1 := by
      have := Real.exp_one_lt_d9
      linarith
    calc lA L ≤ L.sc.x ^ (7 : ℝ) := lA_le_pow_seven hV
      _ = Real.exp (7 * Real.log L.sc.x) := by rw [Real.rpow_def_of_pos hx0, mul_comm]
      _ ≤ Real.exp ((⌈7 * Real.log L.sc.x⌉₊ : ℕ) * 1) := by
          rw [mul_one]; exact Real.exp_le_exp.2 (Nat.le_ceil _)
      _ = Real.exp 1 ^ ⌈7 * Real.log L.sc.x⌉₊ := Real.exp_nat_mul _ _
      _ ≤ ((l : ℝ) - 1) ^ ⌈7 * Real.log L.sc.x⌉₊ := by gcongr
  · have : ⌈7 * Real.log L.sc.x⌉₊ ≤ ⌈(405 : ℝ) * Real.log L.sc.x⌉₊ := Nat.ceil_mono (by linarith)
    rw [hLw, Lwv]; omega
  · rw [hLw, hC.2.2.1, Lwv, he]
    have a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1 := Nat.ceil_lt_add_one (by positivity)
    have a3 : 60 / eps = 2 * (30 / eps) := by ring
    push_cast
    linarith
  · rw [hV.logFiveDepth_eq, hC.2.2.2.1]
    have hb := nN_div_m_le hCt hV
    have hm2 := D.R.two_le_m
    have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
    have hn : (0 : ℝ) < D.R.n := by
      have : 0 < D.R.n := by
        have := D.R.two_le_m
        have := D.R.m_le_f
        unfold Ranks.n
        omega
      exact_mod_cast this
    have hN : (0 : ℝ) < D.R.N D.R.m := by
      have h := D.R.m_add_three_le_k
      have : 0 < D.R.N D.R.m := by unfold Ranks.N; omega
      exact_mod_cast this
    have hy : 0 < (D.R.n : ℝ) * D.R.N D.R.m / D.R.m := by positivity
    have l4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have l2 := Real.log_two_gt_d9
    have l2' := Real.log_two_lt_d9
    have l5 : Real.log 4 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
    have hl : Real.log ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ Real.log 4 + 404 * Real.log L.sc.x := by
      refine (Real.log_le_log hy hb).trans (le_of_eq ?_)
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
    have hlb : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ 400 * Real.log L.sc.x := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    have a1 : (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 400 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : ((⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ : ℕ) : ℝ) ≤ (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) := by
      exact_mod_cast Nat.ceil_mono hlb
    linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_exact : SzRow (fun C D L => (∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t → (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + (⌊L.sc.b' / L.sc.x⌋ : ℤ)) ∧ (∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ 2 * L.Sc) ∧ (∀ τ (hk : 2 ≤ D.R.k), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = (D.hc τ).v ⟨D.R.k - 2, by omega⟩ - 1 / 2) ∧ (∀ τ (hm : 0 < D.R.m), |((((D.hc τ).e ⟨D.R.m - 1, by omega⟩ - (D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ)) : ℝ) - h0 L / 2| ≤ 2) ∧ (∀ τ (j : ℕ) (h : j + 1 < D.R.m), h0 L ≤ (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) ∧ (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) ≤ h0 L + 1) ∧ (∀ τ (j : Fin D.R.m), |((((D.hc τ).e j - (D.hc τ).b j : ℚ)) : ℝ) - h0 L / 2| ≤ 2) ∧ (∀ j : Fin D.R.m, UpperTheory.MUQ (fun τ => D.host.emb (D.eTau τ : D.R.GG)) (fun τ => (D.hc τ).e j)) ∧ (D.div.etaF = C.P.CetaF * L.sc.x ^ (-C.P.CF)) ∧ (D.host.pde % 15 = 1 ∧ D.host.pde' % 15 = 1) ∧ (∀ i, D.host.pde ≠ D.host.g i ∧ D.host.pde' ≠ D.host.g i) ∧ (Real.log (Ideal.absNorm D.host.ccK) ≤ L.sc.L) ∧ ((Ideal.absNorm D.host.ccK : ℝ) ≤ C.P.CccK * D.host.d)) := by
  intro eps _ _ C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => ?_⟩⟩⟩
  obtain ⟨hv, hu, ⟨b1, hb, htop, -, -⟩, hpar⟩ := hV.hc
  have hm2 := D.R.two_le_m
  have hm0 : (D.R.m : ℝ) ≠ 0 := by
    have : D.R.m ≠ 0 := by omega
    exact_mod_cast this
  have hh0 : h0 L = (h0v L.sc ch : ℝ) := by
    unfold h0
    rw [hV.eta_eq]
    field_simp
  have hcen : ∀ τ (j : Fin D.R.m), |((((D.hc τ).e j - (D.hc τ).b j : ℚ)) : ℝ) - h0 L / 2| ≤ 2 := by
    intro τ j
    rw [(hb τ j).2, hh0]
    push_cast
    simp
  have hcc : D.host.ccK = ⊤ := hV.host.2.2.2.2.2.2.1
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  refine ⟨?_, ?_, ?_, fun τ hm => hcen τ _, ?_, hcen, hpar, ?_, D.host.pde_mod, D.host.pde_ne_g, ?_, ?_⟩
  · intro τ t hm ht
    rw [(hb τ ⟨0, hm⟩).1, htop τ t ht]
    push_cast
    simp
  · intro τ h0 ht
    rw [(hu τ (by omega) ht).1, hv τ ⟨0, h0⟩, L.Sc_eq, hV.Del_eq]
    have hD : (1 : ℝ) ≤ (Delv L.sc cD : ℝ) := by
      have : 0 < Delv L.sc cD := Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by linarith) _)
      exact_mod_cast this
    have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
      have : 1 ≤ D.R.k := by omega
      exact_mod_cast this
    simp only [Nat.sub_zero]
    push_cast
    nlinarith
  · intro τ hk ht
    rw [(hu τ (by omega) ht).2, hv τ ⟨D.R.k - 2, by omega⟩]
    simp
    norm_num
  · intro τ j h
    rw [(hb τ ⟨j + 1, h⟩).1, (hb τ ⟨j, by omega⟩).1, hh0]
    push_cast
    constructor <;> nlinarith
  · rw [hV.etaF_eq, hC.2.2.2.2.2.2.2.2.2.2.2.1]
  · rw [hcc, Ideal.absNorm_top]
    simp only [Nat.cast_one, Real.log_one]
    unfold Scale.L
    positivity
  · rw [hcc, Ideal.absNorm_top, hC.2.2.2.2.2.2.1]
    have : 1 ≤ D.host.d := D.host.hyp.2.1.one_le
    simp only [Nat.cast_one, one_mul]
    exact_mod_cast this

end GlobalTheory.EX
end

section

noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)

instance mulActPP {q : ℕ} {F : Type} [Field F] (Lc : LocF q F) (n : ℕ) : MulAction (GL (Fin n) Lc.K) (LocF.PP Lc n) where
  smul := LevModel.actPP
  one_smul p := LevModel.isAct_unique (LevModel.isAct_actPP 1 p) (fun x => by simp)
  mul_smul g h p := LevModel.isAct_unique (LevModel.isAct_actPP (g * h) p) (fun x => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have h1 := LevModel.isAct_actPP g (LevModel.actPP h p) (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) x)
    have h2 := LevModel.isAct_actPP h p x
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

def valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) : Subring K :=
  (Q.valuation K).valuationSubring.toSubring

theorem mem_valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ valO Q ↔ Q.valuation K x ≤ 1 :=
  Iff.rfl

def unitGL (K : Type) [Field K] [StarRing K] (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K)ᴴ * (g : Matrix (Fin n) (Fin n) K) = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (g : Matrix (Fin n) (Fin n) K), hg,
      Matrix.one_mul, hh]
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K)ᴴ := by
      rw [← Matrix.one_mul ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ← hg, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [h1, Matrix.conjTranspose_conjTranspose, ← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]

structure Ar (D : D7) (T : ℕ) [Fact T.Prime] where
  Lc : LocF T (ZMod T)
  [st : StarRing Lc.K]
  j : Lc.K →+* D.what₂.LL
  j_star : ∀ x, D.what₂.embLL (j (star x)) = starRingEnd ℂ (D.what₂.embLL (j x))
  seen : D.what₂.places.Pl → Bool
  int_on : ∀ w, D.what₂.places.resChar w = T → ∀ x, j (if seen w then x else star x) ∈ Ow D w ↔ x ∈ Lc.O
  Γ : ∀ n, Subgroup (GL (Fin n) Lc.K)
  unit : ∀ n, Γ n ≤ unitGL Lc.K n
  int_off : ∀ n, ∀ g ∈ Γ n, ∀ w, D.what₂.places.resChar w ≠ T → ∀ a b, j ((g : Matrix (Fin n) (Fin n) Lc.K) a b) ∈ Ow D w
  free : ∀ n, ∀ g ∈ Γ n, ∀ p : LocF.PP Lc n, g • p = p → g = 1
  fin : ∀ n, Finite (MulAction.orbitRel.Quotient (Γ n) (LocF.PP Lc n))

attribute [instance] Ar.st

end GlobalTheory.LvT.Inh
end
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem _root_.GlobalTheory.T.levelChainTransition_isExt_kernel_sum : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (M' : PtModel X (i + 1)) (K : KerPt M M') (φ : Fn X i) (Φ : M.Pt → M.Val), K.TgtEq → M.IsExt φ Φ → M'.IsExt (KT X i φ) (fun p' => ∑ c, X.C.wt i c • K.k (M.rep c) p' (Φ (M.rep c))) := by
  first | exact @GlobalTheory.LvT.isExt_KT | exact GlobalTheory.LvT.isExt_KT | (intros; apply GlobalTheory.LvT.isExt_KT <;> assumption)
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem _root_.GlobalTheory.T.mem_forms_iff_exists_equivariant_extension : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (φ : Fn X i), φ ∈ X.fm.Fi i ↔ ∃ Φ, M.IsExt φ Φ := by
  first | exact @GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt | exact GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt | (intros; apply GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt <;> assumption)
end
