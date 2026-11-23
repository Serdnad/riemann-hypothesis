module

public import Formalism.RealPlaceAnalysis.Bundle001
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix

noncomputable section

namespace Formalism.REAL

private lemma inG_iff_star_signed_entries_eq_zero {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0 := by
  unfold inG Jm
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
      Matrix.zero_apply] using this
  · intro h
    ext i j
    simpa only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
      Matrix.zero_apply] using h i j

lemma f1auxiliary_hs_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.star_def, Complex.mul_re]

lemma continuous_hs_real_place_taylor {n : ℕ} : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp (continuous_apply i)).norm.pow 2

lemma f1auxiliary_hs_one (n : ℕ) : hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp only [hs, Matrix.one_apply]
  have key : ∀ i : Fin n, ∑ j, ‖(if i = j then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  simp [key]

theorem ball_open_holds : BallOpen := by
  intro n R hR
  refine ⟨{g | hs g < R}, isOpen_lt continuous_hs_real_place_taylor continuous_const, ?_, fun g hg => hg⟩
  show hs (1 : Matrix (Fin n) (Fin n) ℂ) < R
  rw [f1auxiliary_hs_one]
  exact hR

lemma f1auxiliary_closed {n : ℕ} (ε : Fin n → Bool) : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

lemma f1auxiliary_entry_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ hs g := by
  unfold hs
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2)
          (fun k _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem hermitian_small_ball : HSBall := by
  intro n ε
  refine ⟨fun R => ?_, fun g k hk => ⟨?_, ?_⟩⟩
  · have hcpt : IsCompact (Set.pi Set.univ fun _ : Fin n =>
        Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) (Real.sqrt R)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    refine hcpt.of_isClosed_subset ((f1auxiliary_closed ε).inter (isClosed_le continuous_hs_real_place_taylor continuous_const)) ?_
    rintro g ⟨_, hg⟩ i _ j _
    have h1 := (f1auxiliary_entry_le g i j).trans hg
    simpa using Real.abs_le_sqrt h1
  · have hk1 : k * kᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.1 hk.1
    rw [f1auxiliary_hs_eq, f1auxiliary_hs_eq, conjTranspose_mul]
    congr 1
    rw [show kᴴ * gᴴ * (g * k) = kᴴ * (gᴴ * g * k) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, Matrix.mul_assoc, hk1, Matrix.mul_one]
  · have hk2 : kᴴ * k = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.1 hk.1
    rw [f1auxiliary_hs_eq, f1auxiliary_hs_eq, conjTranspose_mul]
    congr 1
    rw [show gᴴ * kᴴ * (k * g) = gᴴ * (kᴴ * k) * g by simp only [Matrix.mul_assoc], hk2, Matrix.mul_one]

end Formalism.REAL
end
end

section

open Finset

noncomputable section

namespace Formalism.REAL

lemma rho_card_le {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) ≤ n := by
  have h : (univ.filter p).card ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast h

lemma rho_rhoN_bound {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by
  unfold rhoN
  have h1 := rho_card_le (fun b => a < b ∧ ε b ≠ ε a)
  have h2 := rho_card_le (fun b => b < a ∧ ε b ≠ ε a)
  have h3 := Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card
  have h4 := Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card
  constructor <;> linarith

theorem half_sum_roots_standard : RhoStd := by
  intro n ε a
  unfold rhoC rhoN
  have k1 : #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} = #{b | a < b} := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h1 : a < b <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]
  have k2 : #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = #{b | b < a} := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h1 : b < a <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]
  have k3 : #{b | a < b} = n - 1 - (a : ℕ) := by
    rw [show (univ.filter fun b : Fin n => a < b) = Finset.Ioi a by ext b; simp]
    exact Fin.card_Ioi a
  have k4 : #{b | b < a} = (a : ℕ) := by
    rw [show (univ.filter fun b : Fin n => b < a) = Finset.Iio a by ext b; simp]
    exact Fin.card_Iio a
  have ha := a.isLt
  have r1 : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℝ)
      + ((a : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast (show #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} + (a : ℕ) + 1 = n by omega)
  have r2 : ((#{b | b < a ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | b < a ∧ ε b ≠ ε a} : ℕ) : ℝ)
      = ((a : ℕ) : ℝ) := by
    exact_mod_cast (show #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = (a : ℕ) by omega)
  linarith

lemma rho_nsq_root {n : ℕ} (x : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    nsq (x + root a b) = nsq x + 2 * (x a - x b) + 2 := by
  have hs : ∀ i, (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i *
        (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i
      = x i * x i + (2 * x i + 1) * (Pi.single a (1 : ℝ) : Fin n → ℝ) i +
        (1 - 2 * x i) * (Pi.single b (1 : ℝ) : Fin n → ℝ) i := by
    intro i
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [Pi.single_apply, h1, h2, hab, Ne.symm hab] <;> ring
  unfold root nsq dot
  rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [Pi.single_apply] <;> ring

theorem omega_eigenvalue_holds : OmEigen := by
  intro n ε lam a b hab
  have e : lam + rhoN ε - rhoC ε + root a b + rhoC ε = (lam + rhoN ε - rhoC ε + rhoC ε) + root a b := by
    abel
  rw [e, rho_nsq_root _ a b hab]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem unitary_spectral_gap : UGap := by
  intro n ε lam g a b _ _ hg
  obtain ⟨d1, _⟩ := rho_rhoN_bound ε a
  obtain ⟨_, d2⟩ := rho_rhoN_bound ε b
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end Formalism.REAL
end
end

section

open Finset

noncomputable section

namespace Formalism.REAL

lemma casKHW_two_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    2 * rhoC ε a = ∑ b, ((if a < b ∧ ε b = ε a then (1:ℝ) else 0) -
      (if b < a ∧ ε b = ε a then (1:ℝ) else 0)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  unfold rhoC; ring

def casKHW_coef {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a b : Fin n) : ℝ :=
  if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0) else 0

lemma casKHW_term (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V)
    (hG : GlRel E) (hK : KHighest ε E μ w) (a b : Fin n) :
    (if ε a = ε b then E a b * E b a else 0) w = ((casKHW_coef ε μ a b : ℝ) : ℂ) • w := by
  unfold casKHW_coef
  by_cases h : ε a = ε b
  · simp only [h, if_true]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have hne : a ≠ b := ne_of_lt hab
      simp only [hne, if_false, hab, if_true]
      have h1 := congrArg (fun T : Module.End ℂ V => T w) (hG a b b a)
      simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h1
      have h0 : E a b w = 0 := hK.2 a b hab h
      rw [h0, map_zero, sub_zero, hK.1 a, hK.1 b] at h1
      rw [Module.End.mul_apply, h1]
      push_cast
      rw [sub_smul]
    · simp only [if_true, Module.End.mul_apply, hK.1 a, map_smul, smul_smul]
      push_cast; ring_nf
    · have hne : a ≠ b := ne_of_gt hab
      have hnl : ¬ a < b := not_lt_of_gt hab
      simp only [hne, if_false, hnl]
      rw [Module.End.mul_apply, hK.2 b a hab h.symm, map_zero]
      simp
  · simp [h]

lemma casKHW_arith {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    ∑ a, ∑ b, casKHW_coef ε μ a b = nsq (μ + rhoC ε) - nsq (rhoC ε) := by
  have hpt : ∀ a b, casKHW_coef ε μ a b =
      (if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a else 0) -
        (if a < b ∧ ε a = ε b then μ b else 0) := by
    intro a b
    unfold casKHW_coef
    by_cases h : ε a = ε b
    · rcases lt_trichotomy a b with hab | rfl | hab
      · simp [h, hab, ne_of_lt hab]
      · simp
      · simp [h, ne_of_gt hab, not_lt_of_gt hab]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      by_cases hab : a = b
      · exact absurd (congrArg ε hab) h
      · simp [h, h', hab]
  simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e1 : ∑ a : Fin n, ∑ b : Fin n, (if a = b then μ a ^ 2 else 0) = ∑ a, μ a ^ 2 := by
    simp
  have e2 : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε a = ε b then μ b else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) := by
    rw [Finset.sum_comm]
  have e3 : ∀ a, ∑ b : Fin n, (if a < b ∧ ε b = ε a then μ a else 0) -
      ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) = μ a * (2 * rhoC ε a) := by
    intro a
    rw [casKHW_two_rhoC, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [e1, e2, add_sub_assoc, ← Finset.sum_sub_distrib]
  simp_rw [e3]
  unfold nsq dot
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]; ring

theorem compactCasimirOnHighestWeight_holds : CasKHighest := by
  intro V _ _ n ε E μ w hG hK
  unfold CasK
  simp only [LinearMap.sum_apply]
  simp_rw [casKHW_term V n ε E μ w hG hK]
  rw [← casKHW_arith ε μ]
  simp_rw [← Finset.sum_smul]
  push_cast
  rfl

end Formalism.REAL
end
end

section

open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section WDA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}

lemma WDA_sgn_symm (ε : Fin n → Bool) (a b : Fin n) : sgn ε a b = sgn ε b a := by
  unfold sgn; simp only [eq_comm]

lemma WDA_norm (hU : IsUnitary ε E) (a b : Fin n) (x : V) :
    (((‖E a b x‖ ^ 2 : ℝ)) : ℂ) = (sgn ε a b : ℂ) * ⟪x, E b a (E a b x)⟫_ℂ := by
  rw [Complex.ofReal_pow, ← hU a b x (E a b x)]
  exact (inner_self_eq_norm_sq_to_K (E a b x)).symm

lemma WDA_op (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) :
    (2 • CasK ε E - Cas E) = ∑ a, ∑ b, ((sgn ε a b : ℂ)) • (E a b * E b a) := by
  simp only [CasK, Cas, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  unfold sgn
  split_ifs with h
  · simp [two_smul]
  · simp

end WDA

section WDA2

theorem sumOfSquaresIdentity_holds : SumSq := by
  intro V _ _ n ε E w hU
  rw [WDA_op]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    inner_sum, inner_smul_right]
  simp only [Complex.ofReal_sum]
  simp only [WDA_norm hU]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [WDA_sgn_symm]

end WDA2

end Formalism.REAL
end
end
