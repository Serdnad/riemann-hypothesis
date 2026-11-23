module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle018
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.NonsingularNorm
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle009
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle004
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle008
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle020
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle021
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle019
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle011
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Formalism.TorsionNormIteration.InvIntegralOfClass

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem jInv_sub_1728_eq_div (L : PeriodPair) :
    jInv L - 1728 = 1728 * 27 * L.g₃ ^ 2 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  have hD := discNeZero L
  unfold jInv
  field_simp
  ring

theorem jInv_ratio (L : PeriodPair) (h3 : L.g₃ ≠ 0) :
    27 * jInv L / (jInv L - 1728) = L.g₂ ^ 3 / L.g₃ ^ 2 := by
  have hD := discNeZero L
  rw [jInv_sub_1728_eq_div]
  unfold jInv
  field_simp

theorem exists_cm_lattice_equal_invariants (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) :
    ∃ L0 : PeriodPair, HasCMBy d L0 ∧ jInv L0 = jInv L ∧
      L0.g₂ = 27 * jInv L / (jInv L - 1728) ∧ L0.g₃ = 27 * jInv L / (jInv L - 1728) := by
  obtain ⟨c, hc2⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₃ / L.g₂) (n := 2) (by norm_num)
  have hc : c ≠ 0 := by
    rintro rfl
    have : L.g₃ / L.g₂ ≠ 0 := div_ne_zero h3 h2
    apply this
    rw [← hc2]
    norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := homogeneity L c hc
  refine ⟨scalePair L c hc, hasCMByScale d L c hc hCM, jInvScale L c hc, ?_, ?_⟩
  · rw [hg2, jInv_ratio L h3, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]
    field_simp
  · rw [hg3, jInv_ratio L h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc2]
    field_simp

theorem jInv_eq_zero_iff (L : PeriodPair) : jInv L = 0 ↔ L.g₂ = 0 := by
  have hD := discNeZero L
  unfold jInv
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · simpa using h
    · exact absurd h hD
  · intro h
    left
    rw [h]
    norm_num

theorem jInv_eq_iff (L : PeriodPair) : jInv L = 1728 ↔ L.g₃ = 0 := by
  have hD := discNeZero L
  rw [← sub_eq_zero, jInv_sub_1728_eq_div, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · simpa using h
    · exact absurd h hD
  · intro h
    left
    rw [h]
    norm_num

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem cubic_coeff_ind (p : ℂ_[l] → Prop) (T : Cubic ℂ_[l]) (h0 : p 0) (ha : p T.a) (hb : p T.b)
    (hc : p T.c) (hd : p T.d) (i : ℕ) : p (T.toPoly.coeff i) := by
  rcases i with _ | _ | _ | _ | i
  · simpa [Cubic.coeff_eq_d] using hd
  · simpa [Cubic.coeff_eq_c] using hc
  · simpa [Cubic.coeff_eq_b] using hb
  · simpa [Cubic.coeff_eq_a] using ha
  · rw [Cubic.coeff_eq_zero (by omega)]
    exact h0

theorem tor_two (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP0 : P ≠ 0)
    (h2 : P + P = 0) : px _ P ∈ MaximalUnramifiedExtension l ∧ py _ P ∈ MaximalUnramifiedExtension l := by
  have hl2 : ¬ l ∣ 2 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := h.five
    omega
  have hl4 : ¬ l ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := h.five
    omega
  have hE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P 2 hl2 (by rw [two_nsmul]; exact h2) hP0
  obtain ⟨-, hx, hy⟩ := integral_of_not_mem_formalGroup h P hE
  obtain ⟨hpsi, hkap⟩ :=
    Formalism.L2.Th1.E.UnitKap_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] (shortW g2 g3) (good_int h) P hP0 h2 hx hy
  cases P with
  | zero => exact absurd rfl hP0
  | some x y hns =>
    change ‖x‖ ≤ 1 at hx
    change 2 * y + (shortW g2 g3).a₁ * x + (shortW g2 g3).a₃ = 0 at hpsi
    change ‖3 * x ^ 2 + 2 * (shortW g2 g3).a₂ * x + (shortW g2 g3).a₄ - (shortW g2 g3).a₁ * y‖ = 1 at hkap
    change x ∈ MaximalUnramifiedExtension l ∧ y ∈ MaximalUnramifiedExtension l
    have hy0 : y = 0 := by
      simp only [shortW, zero_mul, add_zero] at hpsi
      simpa using hpsi
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    simp only [shortW] at heq hkap
    have n4 : ‖(4 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_natCast_Cl_of_not_dvd (l := l) hl4
    have m4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 4
    refine ⟨?_, hy0 ▸ zero_mem _⟩
    refine hensel_mem l (Cubic.toPoly ⟨1, 0, -g2 / 4, -g3 / 4⟩) ?_ ?_ x hx ?_ ?_
    · exact cubic_coeff_ind (· ∈ MaximalUnramifiedExtension l) _ (zero_mem _) (one_mem _) (zero_mem _)
        (div_mem (neg_mem h.mem2) m4) (div_mem (neg_mem h.mem3) m4)
    · refine cubic_coeff_ind (‖·‖ ≤ 1) _ (by simp) (by simp) (by simp) ?_ ?_
      · simpa [norm_div, n4] using h.norm2
      · simpa [norm_div, n4] using h.norm3
    · simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [hy0] at heq
      linear_combination -heq
    · have : (Cubic.toPoly (⟨1, 0, -g2 / 4, -g3 / 4⟩ : Cubic ℂ_[l])).derivative.eval x
          = 3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y := by
        simp only [Cubic.toPoly, Polynomial.derivative_add, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X_pow, Polynomial.derivative_X,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_natCast,
          map_natCast]
        push_cast
        ring
      rw [this]
      exact hkap

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem inertKur {d l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (x : Om d)
    (hx : ∀ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ → σ x = x) : ι (x : ℂ) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨e, he⟩ := locEmb d l ι
  have hs : (e (algebraMap (KQ d) (Om d) (sqK d))) ^ 2 = -(d : PadicAlgCl l) := by
    have h1 : (algebraMap (KQ d) (Om d) (sqK d)) ^ 2 = -(d : Om d) := by
      apply Subtype.ext
      simpa [sqK] using sqD_sq d
    rw [← map_pow, h1, map_neg, map_natCast]
  have hint : IsIntegral ℚ_[l] (e (algebraMap (KQ d) (Om d) (sqK d))) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ_[l]), Polynomial.monic_X_pow_add_C _ (by norm_num), ?_⟩
    simp [hs]
  have hK := IntermediateField.adjoin.finiteDimensional hint
  have hmem := fixed_mem_Kur _ hK (e x) (fun ρ hρ => by
    obtain ⟨σ, hσ, hc⟩ := locLift ι e he ρ hρ
    rw [← hc, hx σ hσ])
  rw [← he]
  exact kur_le hl hld hs hmem

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem good_lattice (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hg : IsGoodModel l L ι g2 g3) :
    ∃ L' : PeriodPair, LatModel l L' ι g2 g3 ∧ ∀ d, HasCMBy d L → HasCMBy d L' := by
  obtain ⟨-, -, h2, h3, -, lam, hlam, e2, e3⟩ := hg
  have hm : ι.symm lam ≠ 0 := by
    intro h
    apply hlam
    have := congrArg ι h
    simpa using this
  have hc : (ι.symm lam)⁻¹ ≠ 0 := inv_ne_zero hm
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := F.homogeneity L (ι.symm lam)⁻¹ hc
  refine ⟨F.scalePair L (ι.symm lam)⁻¹ hc, ⟨?_, ?_, h2, h3⟩,
    fun d hd => F.hasCMByScale d L _ hc hd⟩
  · rw [hg2, e2]
    simp
  · rw [hg3, e3]
    simp

end ReciprocityTheory.ChartRestriction.L1
end
end
