module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.Proof.IntegralPowerExpansion

open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram depthSub)

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  · intro h
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer a h
    exact ⟨n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem val_q {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) :
    P.valuation E (qOf P : E) = WithZero.exp (-1) := by
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  rw [e, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 : P.intValuation (qOf P : 𝓞 E) < 1 :=
    (P.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have h2 : ¬ P.intValuation (qOf P : 𝓞 E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact hP.2
  have hx : P.intValuation (qOf P : 𝓞 E) ≠ 0 := by
    intro h0
    exact h2 (h0 ▸ zero_le)
  rw [← WithZero.exp_log hx] at h1 h2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  rw [WithZero.exp_le_exp] at h2
  congr 1
  omega

theorem q_ne_zero {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) : (qOf P : E) ≠ 0 :=
  Nat.cast_ne_zero.2 hP.1.ne_zero

theorem exists_int_add_q_mul {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) {u : E} (hu : IntAt P u) :
    ∃ (k : ℤ) (u' : E), IntAt P u' ∧ u = k + (qOf P : E) * u' := by
  obtain ⟨r, s, hs, h⟩ := hu
  haveI : Fact (qOf P).Prime := ⟨hP.1⟩
  have hc : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
    rw [qOf, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1
    (mem_zmultiples_of_prime_card (g' := Ideal.Quotient.mk P.asIdeal r) hc (mk_ne_zero hs))
  have hm : r - k * s ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_intCast, ← hk, zsmul_eq_mul, sub_self]
  have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hs
  have h2 : algebraMap (𝓞 E) E s * (u - k) = algebraMap (𝓞 E) E (r - k * s) := by
    rw [map_sub, map_mul, map_intCast, ← h]; ring
  have h3 : P.valuation E (u - k) < 1 := by
    have := congrArg (P.valuation E) h2
    rw [map_mul, h1, one_mul, HeightOneSpectrum.valuation_of_algebraMap] at this
    rw [this]
    exact (P.intValuation_lt_one_iff_mem _).2 hm
  have hq := q_ne_zero hP
  refine ⟨k, (u - k) / qOf P, ?_, by field_simp; ring⟩
  rw [intAt_iff_val, map_div₀, val_q hP]
  exact div_le_one_of_le₀ (le_exp_neg_one_of_lt_one h3) zero_le

theorem exists_int_add_q_pow_mul {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) (j : ℕ) {u : E}
    (hu : IntAt P u) : ∃ (k : ℤ) (u' : E), IntAt P u' ∧ u = k + (qOf P : E) ^ j * u' := by
  induction j with
  | zero => exact ⟨0, u, hu, by simp⟩
  | succ j ih =>
    obtain ⟨k, u', hu', e⟩ := ih
    obtain ⟨k', u'', hu'', e'⟩ := exists_int_add_q_mul hP hu'
    refine ⟨k + (qOf P : ℤ) ^ j * k', u'', hu'', ?_⟩
    rw [e, e']
    push_cast
    ring

end GlobalTheory.Proof.IntegralPowerExpansion
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.BranchMembers

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

theorem lamTrue_lo (u : Word) (τ : X.Tau) (i : Fin (R.N R.m)) (j : Fin R.k) (h : i.1 = j.1) :
    ((W.lamTrue u R.m τ).w i : ℚ) =
      (W.hc u τ).u j - ((R.k : ℚ) - 1) / 2 + (j.1 : ℚ) - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hi : i.1 < R.k := h ▸ j.2
  have e : (⟨i.1, hi⟩ : Fin R.k) = j := Fin.ext h
  rw [Wts.lamTrue_eq, Wts.lamN_eq W u le_rfl, dite_eq_left hi, e]
  unfold hcToWeightQ rhoVec
  ring

theorem lamTrue_hi (u : Word) (τ : X.Tau) (i : Fin (R.N R.m)) (B ρ : ℕ) (hρ : ρ < R.t + 1)
    (h : i.1 = R.k + B * (R.t + 1) + ρ) :
    ((W.lamTrue u R.m τ).w i : ℚ) =
      -(RowPar.of (W.hc u τ)).eAt B + (R.k : ℚ) / 2 + (2 * (B : ℚ) + 1) * (((R.t : ℚ) + 1) / 2) -
        (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hi : ¬ i.1 < R.k := by omega
  have e1 : (i.1 - R.k) / (R.t + 1) = B := by
    have : i.1 - R.k = B * (R.t + 1) + ρ := by omega
    rw [this]
    exact (divmod (R.t + 1) B ρ hρ).1
  have hB : B < R.m := e1 ▸ R.blk_lt le_rfl i hi
  rw [Wts.lamTrue_eq, Wts.lamN_eq W u le_rfl, dite_eq_right hi, RowPar.eAt_of _ hB]
  simp only [e1]
  unfold wG
  push_cast
  ring

theorem sgTrue_entry (hW : W.Ok) (u : Word) (τ : X.Tau) (i : Fin (R.N R.m - 1)) :
    ((W.sgTrue τ).w i : ℚ) =
      (RowPar.of (W.hc u τ)).sgHC i.1 - RowPar.sh R - ((R.k : ℚ) - 2) / 2 - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) + (i.1 : ℚ) := by
  unfold Wts.sgTrue
  rw [← hW.hc_row u τ, RowPar.sgTrue_eq]
  unfold rhoVec
  have c1 : ((R.N R.m - 1 : ℕ) : ℚ) = (R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 1 := by
    rw [Nat.cast_sub (R.N_pos R.m)]
    unfold Ranks.N
    push_cast
    ring
  rw [c1]
  ring

theorem nonneg_sub_of_lt {a b : ℤ} (h : (b : ℚ) - 1 < a) : 0 ≤ a - b := by
  have : b - 1 < a := by exact_mod_cast h
  omega

theorem interlace (hW : W.Ok) (u : Word) (τ : X.Tau) :
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) := by
  intro i
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hs := sgTrue_entry W hW u τ i
  have hi : i.1 < R.k + R.m * (R.t + 1) - 1 := i.2
  have hS : (Br.iS (N_m_succ R) i).1 = i.1 + 1 := rfl
  have hC : (Br.iC (N_m_succ R) i).1 = i.1 := rfl
  have ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  unfold Br.aBr Br.bBr
  by_cases h1 : i.1 < R.k - 1
  · rw [RowPar.sgHC_lo _ h1, RowPar.vb_lo _ h1] at hs
    have a1 := (W.hc u τ).u_gt_v ⟨i.1, h1⟩
    have a2 := (W.hc u τ).v_gt_u ⟨i.1, h1⟩
    have l1 := lamTrue_lo W u τ _ ⟨i.1 + 1, by omega⟩ hS
    have l2 := lamTrue_lo W u τ _ ⟨i.1, by omega⟩ hC
    simp only at a1 a2 l1 l2
    push_cast at l1
    exact ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt (by linarith)⟩
  · obtain ⟨B, ρ, hρ, hn⟩ : ∃ B ρ, ρ < R.t + 1 ∧ i.1 = R.k - 1 + B * (R.t + 1) + ρ := by
      refine ⟨(i.1 - (R.k - 1)) / (R.t + 1), (i.1 - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (i.1 - (R.k - 1)) (R.t + 1)
      rw [Nat.mul_comm] at this
      omega
    have hBm : B < R.m := by
      apply Nat.lt_of_mul_lt_mul_right (a := R.t + 1)
      omega
    have l1 := lamTrue_hi W u τ _ B ρ hρ (by rw [hS]; omega : (Br.iS (N_m_succ R) i).1 = _)
    rw [hn] at hs
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ0
    · rw [Nat.add_zero, RowPar.sgHC_b] at hs
      push_cast [ck] at hs
      have g1 := RowPar.gap_be (W.hc u τ) hBm
      refine ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt ?_⟩
      rcases B with _ | B
      · have l2 := lamTrue_lo W u τ _ ⟨R.k - 1, by omega⟩ (by rw [hC]; simp only; omega : (Br.iC (N_m_succ R) i).1 = _)
        have a1 := (W.hc u τ).u_last_gt (by omega) hBm
        rw [RowPar.bAt_of _ hBm] at hs
        simp only [ck] at l2
        push_cast at hs
        linarith
      · have l2 := lamTrue_hi W u τ _ B R.t (by omega)
          (by rw [hC, hn, Nat.succ_mul]; omega : (Br.iC (N_m_succ R) i).1 = _)
        have g2 := RowPar.gap_eb (W.hc u τ) hBm
        push_cast at hs
        linarith
    · rw [RowPar.sgHC_e _ B ρ hρ0 (by omega)] at hs
      push_cast [ck] at hs
      have l2 := lamTrue_hi W u τ _ B (ρ - 1) (by omega) (by rw [hC]; omega : (Br.iC (N_m_succ R) i).1 = _)
      exact ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt (by linarith)⟩

theorem members : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.Members :=
  fun _ _ _ W hW u τ => ⟨interlace W hW u τ, members_sameShift W hW u τ⟩

end GlobalTheory.BranchMembers
end

section

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.ExplicitFormulaClosed

theorem exists_open_eq_closed (f : ℂ → ℂ) (T : ℝ)
    (hfin : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T + 1 ∧ f ρ = 0}.Finite) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T ∧ f ρ = 0} =
        {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ f ρ = 0} := by
  have h1 : ∀ᶠ T' in 𝓝[>] T, ∀ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T + 1 ∧ f ρ = 0},
      T < |ρ.im| → T' < |ρ.im| := by
    rw [Filter.eventually_all_finite hfin]
    intro ρ _
    by_cases h : T < |ρ.im|
    · exact ((eventually_lt_nhds h).filter_mono nhdsWithin_le_nhds).mono fun _ h' _ => h'
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' h
  have h2 : ∀ᶠ T' in 𝓝[>] T, T' < T + 1 :=
    (eventually_lt_nhds (by linarith)).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ T' in 𝓝[>] T, T < T' := self_mem_nhdsWithin
  obtain ⟨T', a1, a2, a3⟩ := (h1.and (h2.and h3)).exists
  refine ⟨T', a3.le, a2.le, ?_⟩
  ext ρ
  simp only [Set.mem_setOf_eq, sub_zero] at a1 ⊢
  constructor
  · rintro ⟨b0, b1, b2, b3⟩
    exact ⟨b0, b1, by linarith, b3⟩
  · rintro ⟨b0, b1, b2, b3⟩
    refine ⟨b0, b1, ?_, b3⟩
    by_contra h
    have := a1 ρ ⟨b0, b1, by linarith, b3⟩ (not_le.1 h)
    linarith

theorem explicit_formula_closed : ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.ZeroBand.zeros_band
  refine ⟨C₁ + C₂, fun q _ χ hχ u T hT hu => ?_⟩
  obtain ⟨T', hT1, hT2, hset⟩ := exists_open_eq_closed (DirichletCharacter.LFunction χ) T
    (GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ 0 (T + 1)).1
  have e1 := (h₁ q χ hχ u T hT hu).2
  have e2 := (h₂ q χ hχ u T T' hT hu hT1 hT2).2
  have hz : zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ) =
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ DirichletCharacter.LFunction χ ρ = 0},
        ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ) := by
    rw [← hset]; rfl
  have hF := (GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ DirichletCharacter.LFunction χ ρ = 0} ⊆
      zerosIn χ 0 1 := by
    rintro ρ ⟨b0, b1, b2, b3⟩
    exact ⟨b0, b1, by rw [sub_zero]; exact b2.le, b3⟩
  have hZ : ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧
        DirichletCharacter.LFunction χ ρ = 0},
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ ≤
      zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
    unfold zsumR
    rw [finsum_mem_eq_finite_toFinset_sum _ hF, finsum_mem_eq_finite_toFinset_sum _ (hF.subset hsub)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ρ _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.2 hsub)
        fun ρ _ _ => by positivity)
    rw [mul_one_div]; rfl
  have hZ0 : 0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hB : 0 ≤ Real.log (q * u) := Real.log_nonneg (by nlinarith)
  have key : ∀ P Z Z' : ℂ, ‖P + Z'‖ ≤ ‖P + Z‖ + ‖Z' - Z‖ := by
    intro P Z Z'
    have : P + Z' = (P + Z) + (Z' - Z) := by ring
    rw [this]
    exact norm_add_le _ _
  rw [hz]
  refine (key _ _ _).trans ((add_le_add e1 e2).trans ?_)
  generalize (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧
        DirichletCharacter.LFunction χ ρ = 0},
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) = Z at hZ ⊢
  generalize zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) = Z' at hZ hZ0 ⊢
  generalize u * Real.log (q * u * T) ^ 2 / T = A
  generalize Real.log (q * u) = B at hB ⊢
  have a1 : C₁ * (A + B + Z) ≤ C₁ * (A + B + Z') := mul_le_mul_of_nonneg_left (by linarith) hC₁.le
  have a2 : C₂ * A ≤ C₂ * (A + B + Z') := mul_le_mul_of_nonneg_left (by linarith) hC₂.le
  nlinarith

end GlobalTheory.ExplicitFormulaClosed
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.QNF

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

theorem toLin'_nfMat_eq_sum_nfGen {E : Type} [Field E] [NumberField E] [StarRing E] (q n c : ℕ) (e : Fin c → ℤ) (z : Fin n → E)
    (y : Fin (n + c) → E) :
    Matrix.toLin' (nfMat n c (q : E) e z) y =
      Loc.inX E n c (fun a => y (Fin.castAdd c a)) + ∑ i, y (Fin.natAdd n i) • nfGen q n c e z i := by
  funext p
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Pi.add_apply, Finset.sum_apply]
  congr 1
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · simp [nfMat, Loc.inX]
    · have : ∀ a : Fin n, Fin.natAdd n b ≠ Fin.castAdd c a := fun a h => by
        have := congrArg Fin.val h
        simp at this; omega
      simp [nfMat, Loc.inX, this]
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · have h1 : Fin.castAdd c a ≠ Fin.natAdd n i := fun h => by
        have := congrArg Fin.val h
        simp at this; omega
      have h2 : ¬ (a.1 = n + i.1) := by omega
      by_cases hi : i.1 = 0
      · have h0 : ∀ h, (⟨0, h⟩ : Fin c) = i := fun h => Fin.ext hi.symm
        have h3 : ¬ (a.1 = n) := by omega
        simp [nfMat, nfGen, Loc.inX, Loc.eN, h1, h3, hi, h0]
        ring
      · simp [nfMat, nfGen, Loc.eN, h1, h2, hi]
    · by_cases hb : b = i
      · subst hb
        simp [nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, mul_comm]
      · have : ¬ (b.1 = i.1) := fun h => hb (Fin.ext h)
        simp [nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, hb, this]

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem image_lamYat_nfMat {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (e : Fin (cOf R j) → ℤ)
    (z : Fin (R.N j) → X.E) :
    (Matrix.toLin' (nfMat (R.N j) (cOf R j) ((qOf P : ℕ) : X.E) e z)) ''
        (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = nfLat P (R.N j) (cOf R j) e z := by
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, mem_lamYat hP, nfLat, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun a => x (Fin.castAdd _ a), (mem_localization_standardLattice _ _).2 fun a => hx _, fun b => x (Fin.natAdd _ b),
      fun b => hx _, toLin'_nfMat_eq_sum_nfGen _ _ _ _ _ _⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    refine ⟨Fin.addCases (motive := fun _ => X.E) l s, fun p => ?_, ?_⟩
    · refine Fin.addCases (fun a => ?_) (fun b => ?_) p
      · simpa using (mem_localization_standardLattice _ _).1 hl a
      · simpa using hs b
    · rw [toLin'_nfMat_eq_sum_nfGen]
      simp

theorem pad_mem_lamYat_iff {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (z : Fin (R.N j) → X.E) :
    (fun l : Fin (R.N j + cOf R j) => if h : l.1 < R.N j then z ⟨l.1, h⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P ↔
      z ∈ stdAt X.E (R.N j) P := by
  rw [mem_lamYat hP]
  constructor
  · intro h
    refine (mem_localization_standardLattice _ _).2 fun a => ?_
    simpa using h (Fin.castAdd _ a)
  · intro h l
    by_cases hl : l.1 < R.N j
    · simpa [hl] using (mem_localization_standardLattice _ _).1 h ⟨l.1, hl⟩
    · simpa [hl] using (mem_lamYat (R := R) (j := j) hP 0).1 (zero_mem _) l

theorem nf_iff_matNF : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs →
    ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h ↔ GlobalTheory.QNF.MatNF Pr R j P h := by
  intro X Pr R j P hP h
  unfold NF MatNF
  refine exists_congr fun e => exists_congr fun z => and_congr_right fun _ => and_congr (pad_mem_lamYat_iff hP z).symm ?_
  rw [← image_lamYat_nfMat hP]
  refine Iff.trans ?_ SetLike.ext'_iff.symm
  rw [Submodule.map_coe, Submodule.map_coe]
  rfl

end GlobalTheory.QNF

end
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem valB_of_inc : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT) (v : X.A.vT) (p p₁ : M.Pt), X.fm.seenP w = true → v ∈ V → M.Inc v p p₁ → Co.valB w V p₁ = Co.valB w (V.erase v) p := by
  intro D u X i M Co w V v p p₁ hw hv hI
  obtain ⟨-, hoff, x, -, -, hk, -⟩ := hI
  have key : ∀ v', (if X.fm.seenP w = true ∧ v' ∉ V then ((p₁.2 v').1.L : Set _) else (p₁.2 v').ker) =
      (if X.fm.seenP w = true ∧ v' ∉ V.erase v then ((p.2 v').1.L : Set _) else (p.2 v').ker) := by
    intro v'
    by_cases h : v' = v
    · subst h
      rw [if_neg (fun h => h.2 hv), if_pos ⟨hw, Finset.notMem_erase _ _⟩, hk]
    · rw [hoff v' h]
      have : v' ∈ V.erase v ↔ v' ∈ V := by simp [h]
      simp only [this]
  unfold PtModel.Coord.valB
  simp only [key]

end GlobalTheory.LvT
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem isExt_KT : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (M' : PtModel X (i + 1)) (K : KerPt M M') (φ : Fn X i) (Φ : M.Pt → M.Val), K.TgtEq → M.IsExt φ Φ → M'.IsExt (KT X i φ) (fun p' => ∑ c, X.C.wt i c • K.k (M.rep c) p' (Φ (M.rep c))) := by
  intro D u X i M M' K φ Φ hK hΦ
  refine ⟨fun c' => ?_, fun g' p' => ?_⟩
  · show Formalism.ThetaLiftIndependence.kerOpM (X.C.wt i) (X.C.Kmap i) φ c' = _
    unfold Formalism.ThetaLiftIndependence.kerOpM
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hΦ.1 c, K.Kmap_eq, Submodule.coe_smul]

  · simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hK g']

end GlobalTheory.LvT
end
