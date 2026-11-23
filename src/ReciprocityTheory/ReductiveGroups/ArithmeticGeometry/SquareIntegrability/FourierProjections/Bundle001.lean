module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAA
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaPolyTranslate

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem Hf_add_left (x y z : EuclideanSpace ℂ ι) : Hf (x + y) z = Hf x z + Hf y z := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

theorem Hf_add_right (x y z : EuclideanSpace ℂ ι) : Hf z (x + y) = Hf z x + Hf z y := by
  simp only [Hf, PiLp.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem Hf_neg_left (x z : EuclideanSpace ℂ ι) : Hf (-x) z = -Hf x z := by
  simp only [Hf, PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem Hf_conj (x y : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf x y) = Hf y x := by

  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Hf_self (x : EuclideanSpace ℂ ι) : Hf x x = ((‖x‖ : ℝ) : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem conj_eq_sub (z : ℂ) : (starRingEnd ℂ) z = z - 2 * (z.im : ℂ) * I := by
  apply Complex.ext <;> simp
  ring

def Coc (Y : GT ι) (q : ℕ) : Prop :=
  ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
    Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I)

theorem ka_zero {Y : GT ι} {q : ℕ} (hC : Coc Y q) : Y.ka 0 = 1 := by
  have h := hC 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
  have hz : Hf (0 : EuclideanSpace ℂ ι) 0 = 0 := by simp [Hf]
  simp only [add_zero, hz, Complex.zero_im, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one] at h
  have hne : Y.ka 0 ≠ 0 := by
    intro h0
    have h1 := Y.ka_abs 0 (Submodule.zero_mem _)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)

theorem paTh_add {Y : GT ι} {q : ℕ} (hC : Coc Y q) (F : EuclideanSpace ℂ ι → ℂ)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (v : EuclideanSpace ℂ ι) :
    paTh Y q F (v + γ) = Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * paTh Y q F v := by
  simp only [paTh]
  rw [← (Equiv.addLeft (⟨γ, hγ⟩ : lat Y.b)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun δ => ?_
  simp only [Equiv.coe_addLeft, Submodule.coe_add, paU]
  rw [hC γ hγ δ δ.2]
  have hF : v + γ - (γ + (δ : EuclideanSpace ℂ ι)) = v - δ := by abel
  rw [hF]
  have hexp : cexp (-(Real.pi * q * (Hf γ (δ : EuclideanSpace ℂ ι)).im) * I) *
      cexp (q * Real.pi * Hf (v + γ) (γ + (δ : EuclideanSpace ℂ ι)) -
        q * Real.pi * Hf (γ + (δ : EuclideanSpace ℂ ι)) (γ + (δ : EuclideanSpace ℂ ι)) / 2) =
      cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) *
        cexp (q * Real.pi * Hf v (δ : EuclideanSpace ℂ ι) -
          q * Real.pi * Hf (δ : EuclideanSpace ℂ ι) (δ : EuclideanSpace ℂ ι) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_add_left, Hf_add_right, Hf_add_right]
    have hc := conj_eq_sub (Hf γ (δ : EuclideanSpace ℂ ι))
    rw [Hf_conj] at hc
    rw [hc]
    ring
  linear_combination (Y.ka γ * Y.ka δ * F (v - δ)) * hexp

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem paD_add (α : ι →₀ ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paD α (H1 + H2) = paD α H1 + paD α H2 := by
  unfold paD polyDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_add_apply (h1.contDiffAt.of_le (by exact_mod_cast le_top))
    (h2.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp [mul_add]

theorem paD_smul (α : ι →₀ ℕ) (a : ℂ) {H : EuclideanSpace ℂ ι → ℂ}
    (h : ContDiff ℂ (⊤ : ℕ∞) H) : paD α (a • H) = a * paD α H := by
  unfold paD polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply (h.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem paD_zero (α : ι →₀ ℕ) : paD α (0 : EuclideanSpace ℂ ι → ℂ) = 0 := by
  simp [paD, polyDeriv, iteratedFDeriv_fun_zero]

theorem paFact_ne (α : ι →₀ ℕ) : (paFact α : ℂ) ≠ 0 := by
  unfold paFact
  exact Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _)

theorem paJet_add (c : ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paJet c (H1 + H2) = paJet c H1 + paJet c H2 := by
  unfold paJet
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [paD_add α h1 h2, add_div, add_smul]

theorem paJet_smul (c : ℕ) (r : ℂ) {H : EuclideanSpace ℂ ι → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) H) :
    paJet c (r • H) = r • paJet c H := by
  unfold paJet
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [paD_smul α r h, mul_div_assoc, smul_smul]

theorem paJet_zero (c : ℕ) : paJet c (0 : EuclideanSpace ℂ ι → ℂ) = 0 := by
  unfold paJet
  simp [paD_zero]

theorem paJet_mono (c : ℕ) (m : ι →₀ ℕ) :
    paJet c (paMono m) = if m ∈ paS c then paMono m else 0 := by
  unfold paJet
  simp only [paD_mono]
  have e : ∀ α, ((if α = m then (paFact α : ℂ) else 0) / paFact α) • paMono α =
      if α = m then paMono m else 0 := fun α => by
    split_ifs with h
    · subst h
      rw [div_self (paFact_ne α), one_smul]
    · rw [zero_div, zero_smul]
  simp only [e]
  rw [Finset.sum_ite_eq']

theorem gaussianInner_zero_left (q : ℕ) (G : EuclideanSpace ℂ ι → ℂ) : paIP q 0 G = 0 := by
  simp [paIP]

theorem gaussianInner_zero_right (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : paIP q F 0 = 0 := by
  simp [paIP]

theorem gaussianInner_monomial_high {q c : ℕ} (hq : 1 ≤ q) {m : ι →₀ ℕ} (hm : m ∉ paS c)
    {G : EuclideanSpace ℂ ι → ℂ} (hG : G ∈ paPoly c) : paIP q (paMono m) G = 0 := by
  have hmm : paMono m ∈ paPoly (ι := ι) (max c m.degree) :=
    paMono_mem (mem_paS.2 (le_max_right _ _))
  have hup : paPoly (ι := ι) c ≤ paPoly (max c m.degree) := paPoly_mono (le_max_left _ _)
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact gaussianInner_monomial_orthogonal q (by rintro rfl; exact hm hβ)
  | zero => exact gaussianInner_zero_right q _
  | add x y hx hy ihx ihy =>
    rw [gaussianInner_conj_symm q (x + y) (paMono m), gaussianInner_add_left hq (hup hx) (hup hy) hmm, map_add (f := _),
      ← gaussianInner_conj_symm, ← gaussianInner_conj_symm, ihx, ihy, add_zero]
  | smul r x hx ihx =>
    rw [gaussianInner_conj_symm q (r • x) (paMono m), gaussianInner_smul_left, map_mul, ← gaussianInner_conj_symm, ihx, mul_zero]

theorem gaussianInner_polynomial_jet {q c d : ℕ} (hq : 1 ≤ q) {S G : EuclideanSpace ℂ ι → ℂ} (hS : S ∈ paPoly d)
    (hG : G ∈ paPoly c) : paIP q S G = paIP q (paJet c S) G := by
  have hupd : paPoly (ι := ι) d ≤ paPoly (max d c) := paPoly_mono (le_max_left _ _)
  have hupc : paPoly (ι := ι) c ≤ paPoly (max d c) := paPoly_mono (le_max_right _ _)
  induction hS using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [paJet_mono]
    split_ifs with h
    · rfl
    · rw [gaussianInner_monomial_high hq h hG, gaussianInner_zero_left]
  | zero => rw [paJet_zero]
  | add x y hx hy ihx ihy =>
    rw [paJet_add c (paPoly_contDiff hx) (paPoly_contDiff hy),
      gaussianInner_add_left hq (hupd hx) (hupd hy) (hupc hG),
      gaussianInner_add_left hq (hupc (paJet_mem c x)) (hupc (paJet_mem c y)) (hupc hG), ihx, ihy]
  | smul r x hx ihx =>
    rw [paJet_smul c r (paPoly_contDiff hx), gaussianInner_smul_left, gaussianInner_smul_left, ihx]

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end
