module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace IsogenyPAux

lemma P_local (L : PeriodPair) (ω : ℂ) (hω : ω ∈ L.lattice) (w : ℂ) :
    L.weierstrassP w = L.weierstrassPExcept 0 (w - ω) + 1 / (w - ω) ^ 2 := by
  have h1 := L.weierstrassPExcept_add (0 : L.lattice) (w - ω)
  have h2 := L.weierstrassP_sub_coe w ⟨ω, hω⟩
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h1 h2
  rw [← h2, ← h1]

lemma analyticAt_P (L : PeriodPair) (a b z : ℂ) (hz : a * z + b ∉ L.lattice) :
    AnalyticAt ℂ (fun w => L.weierstrassP (a * w + b)) z :=
  AnalyticAt.fun_comp (f := fun w : ℂ => a * w + b) (g := L.weierstrassP)
    (L.analyticOnNhd_weierstrassP _ hz) (by fun_prop)

lemma analyticAt_PExcept (L : PeriodPair) (a z : ℂ) :
    AnalyticAt ℂ (fun w => L.weierstrassPExcept 0 (a * (w - z))) z := by
  refine AnalyticAt.fun_comp (f := fun w : ℂ => a * (w - z)) (g := L.weierstrassPExcept 0) ?_
    (by fun_prop)
  simpa using L.analyticAt_weierstrassPExcept 0

lemma eventually_notMem (L : PeriodPair) (α z : ℂ) (hα : α ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, α * w ∉ L.lattice := by
  have h1 : ∀ᶠ w in 𝓝 z, α * w ∈ ((L.lattice : Set ℂ) \ {α * z})ᶜ :=
    ((continuous_const.mul continuous_id).tendsto z).eventually
      (L.compl_lattice_sdiff_singleton_mem_nhds (α * z))
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hne hmem
  refine hw ⟨hmem, ?_⟩
  simpa [hα] using hne

lemma ext_at (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hst : MulStable L α)
    (h1 : ∀ P ∈ T, α * P ∈ L.lattice)
    (h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q)
    (z₀ P' : ℂ) (hP' : P' ∈ T) (hz : z₀ + P' ∈ L.lattice) :
    AnalyticAt ℂ (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) z₀ ∧
    (fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P)) =ᶠ[𝓝[≠] z₀]
      (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) := by
  constructor
  · refine ((analyticAt_const.mul (analyticAt_PExcept L α z₀)).sub (analyticAt_PExcept L 1 z₀)).sub ?_
    refine Finset.analyticAt_fun_sum _ fun P hP => analyticAt_P L 1 P z₀ ?_
    intro hmem
    rw [one_mul] at hmem
    refine (Finset.mem_erase.1 hP).1 (h2 P (Finset.mem_erase.1 hP).2 P' hP' ?_)
    have := L.lattice.sub_mem hmem hz
    simpa using this
  · have hαz : α * z₀ ∈ L.lattice := by
      have := L.lattice.sub_mem (hst _ hz) (h1 P' hP')
      have e : α * (z₀ + P') - α * P' = α * z₀ := by ring
      rwa [e] at this
    filter_upwards [self_mem_nhdsWithin] with w hne
    have hne' : w - z₀ ≠ 0 := sub_ne_zero.2 hne
    rw [← Finset.add_sum_erase T _ hP', P_local L (α * z₀) hαz (α * w),
      P_local L (z₀ + P') hz (w + P')]
    have e1 : α * w - α * z₀ = α * (w - z₀) := by ring
    have e2 : w + P' - (z₀ + P') = w - z₀ := by ring
    rw [e1, e2]
    simp only [one_mul]
    field_simp
    ring

end IsogenyPAux

open IsogenyPAux

theorem isogenyWeierstrassP_of_ellipticNoPole (hN : EllipticNoPole) : IsogenyP := by
  intro L α S hα hst hS z hz
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have h0S : (0 : ℂ) ∉ S := fun h => (hS1 0 h).2 L.lattice.zero_mem
  set T : Finset ℂ := insert 0 S with hT
  have h1 : ∀ P ∈ T, α * P ∈ L.lattice := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    · simp
    · exact (hS1 P hP).1
  have h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q := by
    intro P hP Q hQ hPQ
    rcases Finset.mem_insert.1 hP with rfl | hP <;> rcases Finset.mem_insert.1 hQ with rfl | hQ
    · rfl
    · exact absurd (by simpa using hPQ) (hS1 Q hQ).2
    · exact absurd (by simpa using hPQ) (hS1 P hP).2
    · exact hS2 P hP Q hQ hPQ
  have h3 : ∀ z₀, α * z₀ ∈ L.lattice → ∃ P ∈ T, z₀ + P ∈ L.lattice := by
    intro z₀ hz₀
    by_cases hm : z₀ ∈ L.lattice
    · exact ⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩
    · obtain ⟨P, hP, hPz⟩ := hS3 (-z₀) (by simpa using L.lattice.neg_mem hz₀)
        (fun h => hm (by simpa using L.lattice.neg_mem h))
      refine ⟨P, Finset.mem_insert_of_mem hP, ?_⟩
      have := L.lattice.neg_mem hPz
      have e : -(-z₀ - P) = z₀ + P := by ring
      rwa [e] at this
  set f : ℂ → ℂ := fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P) with hf

  have han : ∀ z₀, α * z₀ ∉ L.lattice → AnalyticAt ℂ f z₀ := by
    intro z₀ hz₀
    have a1 : AnalyticAt ℂ (fun w => L.weierstrassP (α * w)) z₀ := by
      simpa using analyticAt_P L α 0 z₀ (by simpa using hz₀)
    refine (analyticAt_const.mul a1).sub (Finset.analyticAt_fun_sum _ fun P hP => ?_)
    have := analyticAt_P L 1 P z₀ (by
      intro hmem
      rw [one_mul] at hmem
      apply hz₀
      have := L.lattice.sub_mem (hst _ hmem) (h1 P hP)
      have e : α * (z₀ + P) - α * P = α * z₀ := by ring
      rwa [e] at this)
    simpa using this
  have hext : ∀ z₀, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
    intro z₀
    by_cases hz₀ : α * z₀ ∈ L.lattice
    · obtain ⟨P', hP', hzP⟩ := h3 z₀ hz₀
      exact ⟨_, ext_at L α T hα hst h1 h2 z₀ P' hP' hzP⟩
    · exact ⟨f, han z₀ hz₀, EventuallyEq.rfl⟩
  have hmer : ∀ z, MeromorphicAt f z := by
    intro z
    obtain ⟨g, hg, hfg⟩ := hext z
    exact hg.meromorphicAt.congr hfg.symm
  have hord : ∀ z, 0 ≤ meromorphicOrderAt f z := fun z =>
    (hmer z).meromorphicOrderAt_nonneg_iff.2 (hext z)
  have hper : IsPeriodic L f := by
    intro ω hω w
    simp only [hf]
    have e1 : α * (w + ω) = α * w + α * ω := by ring
    rw [e1, L.weierstrassP_add_coe (α * w) ⟨α * ω, hst ω hω⟩]
    congr 1
    refine Finset.sum_congr rfl fun P _ => ?_
    have e2 : w + ω + P = w + P + ω := by ring
    rw [e2, L.weierstrassP_add_coe (w + P) ⟨ω, hω⟩]
  obtain ⟨c, hc⟩ := hN L f hmer hper hord

  have hc0 : c = -∑ P ∈ S, L.weierstrassP P := by
    obtain ⟨ha, he⟩ := ext_at L α T hα hst h1 h2 0 0 (Finset.mem_insert_self _ _) (by simp)
    have hev : (fun _ : ℂ => c) =ᶠ[𝓝[≠] 0] f := by
      filter_upwards [eventually_notMem L α 0 hα] with w hw
      exact (hc w (han w hw).continuousAt).symm
    have := Elliptic.eq_of_eventuallyEq_nhdsNE continuousAt_const ha.continuousAt (hev.trans he)
    rw [this, hT, Finset.erase_insert h0S]
    simp
  have hfz := hc z (han z hz).continuousAt
  rw [hc0] at hfz
  simp only [hf, hT, Finset.sum_insert h0S, add_zero] at hfz
  rw [Finset.sum_sub_distrib]
  linear_combination hfz

end Formalism.L2.Th1.F
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace Cm1

private theorem cmTheta_eq_half_b_add_sqrt_half_I (b : ℤ) (d : ℕ) :
    Formalism.L2.Th1.F.cmTheta b d = (((b : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  unfold Formalism.L2.Th1.F.cmTheta; push_cast; ring

private theorem re_ofReal_add_ofReal_mul_I (u v : ℝ) : ((u : ℂ) + (v : ℂ) * Complex.I).re = u := by simp

private theorem im_ofReal_add_ofReal_mul_I (u v : ℝ) : ((u : ℂ) + (v : ℂ) * Complex.I).im = v := by simp

lemma sqrt_mul_self (d : ℕ) : Real.sqrt d * Real.sqrt d = d :=
  Real.mul_self_sqrt (Nat.cast_nonneg d)

lemma sqrt_mul_selfC (d : ℕ) : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
  rw [← Complex.ofReal_mul, sqrt_mul_self, Complex.ofReal_natCast]

lemma sqrt_pos' (d : ℕ) (hd : 0 < d) : 0 < Real.sqrt d :=
  Real.sqrt_pos.mpr (by exact_mod_cast hd)

lemma conj_theta (b : ℤ) (d : ℕ) :
    conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  rw [cmTheta_eq_half_b_add_sqrt_half_I]
  simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem four_mul_a_mul_c_complex_of_int (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    (4 : ℂ) * (a : ℂ) * (c : ℂ) = (b : ℂ) ^ 2 + (d : ℂ) := by
  have h' := congrArg (fun t : ℤ => (t : ℂ)) h
  push_cast at h'
  linear_combination h'

lemma theta_sq (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d ^ 2 = (b : ℂ) * cmTheta b d - (a : ℂ) * (c : ℂ) := by
  have hs := sqrt_mul_selfC d
  have hc := four_mul_a_mul_c_complex_of_int a b c d h
  unfold Formalism.L2.Th1.F.cmTheta
  linear_combination ((1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq
    - (1 / 4 : ℂ) * hs + (1 / 4 : ℂ) * hc

lemma coord (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (x y : ℝ)
    (h : (x : ℂ) * (a : ℂ) + (y : ℂ) * cmTheta b d = 0) : x = 0 ∧ y = 0 := by
  have hs := sqrt_pos' d hd
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h1 : ((x * a + y * (b / 2) : ℝ) : ℂ) + ((y * (Real.sqrt d / 2) : ℝ) : ℂ) * Complex.I = 0 := by
    rw [cmTheta_eq_half_b_add_sqrt_half_I] at h
    push_cast at h ⊢
    linear_combination h
  have hre : x * a + y * (b / 2) = 0 := by
    have h2 := congrArg Complex.re h1
    rwa [re_ofReal_add_ofReal_mul_I, Complex.zero_re] at h2
  have him : y * (Real.sqrt d / 2) = 0 := by
    have h2 := congrArg Complex.im h1
    rwa [im_ofReal_add_ofReal_mul_I, Complex.zero_im] at h2
  have hy : y = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact h'
    · linarith
  subst hy
  refine ⟨?_, rfl⟩
  have hxa : x * a = 0 := by linarith
  rcases mul_eq_zero.mp hxa with h' | h'
  · exact h'
  · linarith

lemma mem_iff (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (z : ℂ) :
    z ∈ (cmPair a b d ha hd).lattice ↔ ∃ x y : ℤ, (x : ℂ) * (a : ℂ) + (y : ℂ) * cmTheta b d = z := by
  exact PeriodPair.mem_lattice

end Cm1

open Cm1

theorem cm_theta_eq : CmThetaEq := by
  intro a b c d h
  have hs := Formalism.L2.Th1.F.Cm1.sqrt_mul_selfC d
  have hc := _root_.Formalism.L2.Th1.F.Cm1.four_mul_a_mul_c_complex_of_int a b c d h
  refine ⟨Formalism.L2.Th1.F.Cm1.theta_sq a b c d h, ?_, ?_⟩
  · rw [Formalism.L2.Th1.F.Cm1.conj_theta]; unfold cmTheta; ring
  · rw [Formalism.L2.Th1.F.Cm1.conj_theta]; unfold cmTheta
    linear_combination (-(1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq
      + (1 / 4 : ℂ) * hs - (1 / 4 : ℂ) * hc

theorem cm_stable : CmStable := by
  intro a b c d ha hd h m n z hz
  have hsq := Formalism.L2.Th1.F.Cm1.theta_sq a b c d h
  obtain ⟨x, y, rfl⟩ := (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd z).mp hz
  refine (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mpr ⟨m * x - n * y * c, m * y + n * x * a + n * y * b, ?_⟩
  push_cast
  linear_combination (-((n : ℂ) * (y : ℂ))) * hsq

private theorem area_cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    area (cmPair a b d ha hd) = (a : ℝ) * Real.sqrt d / 2 := by
  have key : conj (a : ℂ) * cmTheta b d
      = (((a : ℝ) * b / 2 : ℝ) : ℂ) + (((a : ℝ) * Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
    rw [map_natCast, _root_.Formalism.L2.Th1.F.Cm1.cmTheta_eq_half_b_add_sqrt_half_I]; push_cast; ring
  unfold area
  show |(conj (a : ℂ) * cmTheta b d).im| = _
  rw [key, _root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I]
  exact abs_of_nonneg (by positivity)

private theorem ofReal_add_mul_I_mul_conj (u v u' v' : ℝ) :
    ((u : ℂ) + (v : ℂ) * Complex.I) * conj ((u' : ℂ) + (v' : ℂ) * Complex.I)
      = ((u * u' + v * v' : ℝ) : ℂ) + ((v * u' - u * v' : ℝ) : ℂ) * Complex.I := by
  simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination (-((v : ℂ) * (v' : ℂ))) * Complex.I_sq

private theorem ofReal_add_mul_I_div_ofReal (u v r : ℝ) :
    ((u : ℂ) + (v : ℂ) * Complex.I) / (r : ℂ) = ((u / r : ℝ) : ℂ) + ((v / r : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

private theorem intCast_mul_add_mul_cmTheta_eq (a : ℕ) (b : ℤ) (d : ℕ) (m n : ℤ) :
    (m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d
      = (((m : ℝ) * a + n * b / 2 : ℝ) : ℂ) + (((n : ℝ) * Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  rw [_root_.Formalism.L2.Th1.F.Cm1.cmTheta_eq_half_b_add_sqrt_half_I]; push_cast; ring

private theorem four_mul_a_mul_c_real_of_int (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    (4 : ℝ) * (a : ℝ) * (c : ℝ) = (b : ℝ) ^ 2 + (d : ℝ) := by
  have h' := congrArg (fun t : ℤ => (t : ℝ)) h
  push_cast at h'
  linear_combination h'

private theorem normSq_coords_eq_a_mul_cmForm (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) (m n : ℤ) :
    ((m : ℝ) * a + n * b / 2) * ((m : ℝ) * a + n * b / 2)
      + ((n : ℝ) * Real.sqrt d / 2) * ((n : ℝ) * Real.sqrt d / 2)
      = (a : ℝ) * (cmForm a b c m n : ℝ) := by
  have hsd := Formalism.L2.Th1.F.Cm1.sqrt_mul_self d
  have hr := four_mul_a_mul_c_real_of_int a b c d h
  unfold cmForm
  push_cast
  linear_combination ((n : ℝ) ^ 2 / 4) * hsd - ((n : ℝ) ^ 2 / 4) * hr

theorem cm_norm : CmNorm := by
  intro a b c d ha hd h m n
  have hsd : Real.sqrt d ≠ 0 := (Formalism.L2.Th1.F.Cm1.sqrt_pos' d hd).ne'
  have hA : (a : ℝ) * Real.sqrt d / 2 ≠ 0 :=
    (div_pos (mul_pos (by exact_mod_cast ha) (Formalism.L2.Th1.F.Cm1.sqrt_pos' d hd)) two_pos).ne'
  have hN := normSq_coords_eq_a_mul_cmForm a b c d h m n
  have hnorm : Complex.normSq ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      = (a : ℝ) * (cmForm a b c m n : ℝ) := by
    rw [intCast_mul_add_mul_cmTheta_eq, Complex.normSq_apply, _root_.Formalism.L2.Th1.F.Cm1.re_ofReal_add_ofReal_mul_I, _root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I]; exact hN
  refine ⟨hnorm, ?_, ?_⟩
  · unfold herm
    rw [area_cmPair, intCast_mul_add_mul_cmTheta_eq, ofReal_add_mul_I_mul_conj, ofReal_add_mul_I_div_ofReal]
    apply Complex.ext
    · rw [_root_.Formalism.L2.Th1.F.Cm1.re_ofReal_add_ofReal_mul_I, Complex.ofReal_re, hN, div_eq_div_iff hA hsd]; ring
    · rw [_root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I, Complex.ofReal_im]; ring
  · intro hmn
    have hz : (m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d ≠ 0 := by
      intro h0
      obtain ⟨h1, h2⟩ := Formalism.L2.Th1.F.Cm1.coord a b d ha hd (m : ℝ) (n : ℝ) (by exact_mod_cast h0)
      have hm : m = 0 := by exact_mod_cast h1
      have hn : n = 0 := by exact_mod_cast h2
      exact hmn (by rw [hm, hn])
    have hpos := Complex.normSq_pos.mpr hz
    rw [hnorm] at hpos
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hQ : (0 : ℝ) < (cmForm a b c m n : ℝ) := by
      by_contra hneg
      have hneg' := not_lt.mp hneg
      nlinarith
    have hQ' : (0 : ℤ) < cmForm a b c m n := by exact_mod_cast hQ
    omega

theorem cm_alternating_form : CmAltE := by
  intro a b d ha hd m n m' n'
  have hA : (a : ℝ) * Real.sqrt d / 2 ≠ 0 :=
    (div_pos (mul_pos (by exact_mod_cast ha) (Formalism.L2.Th1.F.Cm1.sqrt_pos' d hd)) two_pos).ne'
  unfold altE herm
  rw [area_cmPair, intCast_mul_add_mul_cmTheta_eq a b d m n, intCast_mul_add_mul_cmTheta_eq a b d m' n', ofReal_add_mul_I_mul_conj, ofReal_add_mul_I_div_ofReal,
    _root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I, div_eq_iff hA]
  push_cast
  ring

end Formalism.L2.Th1.F
end
end
