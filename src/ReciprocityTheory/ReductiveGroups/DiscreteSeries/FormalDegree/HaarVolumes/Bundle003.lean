module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.GaussA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.GaussB

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.OmegaPQAux

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n P Q : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem Jpq_eq : Formalism.UG.Jpq P Q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext (i | i) (j | j)
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]
  · simp [Formalism.UG.Jpq, Matrix.diagonal_apply]
  · simp [Formalism.UG.Jpq, Matrix.diagonal_apply]
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]

theorem mem_lieU_iff (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ Formalism.BasicNotions.lieU P Q ↔ ∀ i j, star (X j i) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) j +
      Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i * X i j = 0 := by
  show Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔ _
  rw [Jpq_eq]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using hij
  · intro h
    ext i j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h i j

theorem mem_reindex_iff (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.reindex e.symm e.symm Y ∈ Formalism.BasicNotions.lieU P Q ↔
      ∀ a b, star (Y b a) * sg ε b + sg ε a * Y a b = 0 := by
  rw [mem_lieU_iff]
  have hs : ∀ i, Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i = sg ε (e i) := by
    rintro (i | i) <;> simp [sg, he1, he2]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, hs]
  constructor
  · intro h a b
    simpa using h (e.symm a) (e.symm b)
  · intro h i j
    exact h (e i) (e j)

theorem gMat_mem {ε : Fin n → Bool} (s : GCo ε) (a b : Fin n) :
    star (gMat s b a) * sg ε b + sg ε a * gMat s a b = 0 := by
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : ¬ b < a := lt_asymm h
    have h2 : a ≠ b := ne_of_lt h
    have h3 : b ≠ a := ne_of_gt h
    cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]
  · cases ha : ε a <;> simp [gMat, kMat, pmat, sg, ha]
  · have h1 : ¬ a < b := lt_asymm h
    have h2 : a ≠ b := ne_of_gt h
    have h3 : b ≠ a := ne_of_lt h
    cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]

theorem gMat_add {ε : Fin n → Bool} (s t : GCo ε) : gMat (s + t) = gMat s + gMat t := by
  ext a b
  simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> (try simp only [star_add, neg_add, Complex.ofReal_add]) <;> ring

theorem gMat_smul {ε : Fin n → Bool} (c : ℝ) (s : GCo ε) : gMat (c • s) = c • gMat s := by
  ext a b
  simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply]
  split_ifs <;> (try simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, star_mul',
    Complex.star_def, map_mul, Complex.conj_ofReal]) <;> ring

def coordOf {ε : Fin n → Bool} (Y : Matrix (Fin n) (Fin n) ℂ) : GCo ε :=
  ((fun a => (Y a a).im, fun k => Y k.1.1 k.1.2), fun p => Y p.1.1 p.1.2)

theorem coordOf_gMat {ε : Fin n → Bool} (s : GCo ε) : coordOf (gMat s) = s := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [coordOf, gMat, kMat, pmat]
  · funext k
    obtain ⟨⟨a, b⟩, hk⟩ := k
    have h1 : a ≠ b := ne_of_gt hk.1
    have h2 : ¬ a < b := lt_asymm hk.1
    simp [coordOf, gMat, kMat, pmat, h1, h2, hk.1, hk.2]
  · funext q
    obtain ⟨⟨a, b⟩, hq⟩ := q
    have h1 : a ≠ b := ne_of_gt hq.1
    have h2 : ¬ a < b := lt_asymm hq.1
    simp [coordOf, gMat, kMat, pmat, h1, h2, hq.1, hq.2]

theorem gMat_coordOf {ε : Fin n → Bool} (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ a b, star (Y b a) * sg ε b + sg ε a * Y a b = 0) : gMat (coordOf (ε := ε) Y) = Y := by
  ext a b
  have key := hY a b
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : ¬ b < a := lt_asymm h
    have h2 : a ≠ b := ne_of_lt h
    cases ha : ε a <;> cases hb : ε b <;>
      simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>
      first | linear_combination key | linear_combination -key
  · have hre : (Y a a).re = 0 := by
      have hk := congrArg Complex.re key
      cases ha : ε a <;> simp [sg, ha] at hk <;> linarith
    apply Complex.ext <;> simp [gMat, kMat, pmat, coordOf, hre]
  · have h1 : ¬ a < b := lt_asymm h
    have h2 : a ≠ b := ne_of_gt h
    cases ha : ε a <;> cases hb : ε b <;>
      simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>
      first | linear_combination key | linear_combination -key

end ReciprocityTheory.ChartRestriction.DS.OmegaPQAux
end
end

section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem inG_iff_entry {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} :
    inG ε X ↔ ∀ i j, star (X j i) * sg ε j + sg ε i * X i j = 0 := by
  unfold inG Jm sg
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rwa [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply] at this
  · intro h
    ext i j
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply]
    exact h i j

theorem gMat_inG {ε : Fin n → Bool} (s : GCo ε) : inG ε (gMat s) := by
  rw [inG_iff_entry]
  intro i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, sg]
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢
  · apply Complex.ext <;> simp <;> split_ifs <;> simp
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
      split_ifs <;> ring
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢

def gCo (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : GCo ε :=
  ((fun a => (Z a a).im, fun p => Z p.1.1 p.1.2), fun p => Z p.1.1 p.1.2)

theorem gCo_gMat {ε : Fin n → Bool} (s : GCo ε) : gCo ε (gMat s) = s := by
  obtain ⟨⟨w, x⟩, z⟩ := s
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [gCo, gMat, kMat, pmat]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]

theorem gMat_gCo {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    gMat (gCo ε Z) = Z := by
  rw [inG_iff_entry] at hZ
  ext i j
  have hij := hZ i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, gCo, sg] at hij ⊢
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    cases hi : ε i <;> cases hj : ε j <;> simp [h, h1, h2, hi, hj] at hij ⊢ <;>
      first | linear_combination hij | linear_combination -hij
  · apply Complex.ext <;> simp
    · have := congrArg Complex.re hij
      cases hi : ε i <;> simp [hi] at this <;> linarith
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    simp [h, h1, h2.symm]
    split_ifs <;> simp

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end

section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_pos' (M : ℕ) : 0 < volU M := by
  unfold volU
  exact Finset.prod_pos fun i _ => by positivity

theorem volU_skMat_conjTranspose (x : UCo N) : (skMat x)ᴴ = -skMat x := by
  ext a b
  simp only [conjTranspose_apply, Matrix.neg_apply, skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, h.ne', h, not_lt.2 h.le]
  · simp
  · simp [h.ne, h.ne', h, not_lt.2 h.le]

theorem volU_exp_inUJ (x : UCo N) :
    inUJ (fun _ : Fin N => true) (NormedSpace.exp (skMat x)) := by
  have hJ : Jm (fun _ : Fin N => true) = 1 := by simp [Jm]
  unfold inUJ
  rw [hJ, Matrix.mul_one, ← Matrix.exp_conjTranspose, volU_skMat_conjTranspose,
    ← Matrix.exp_add_of_commute (-skMat x) (skMat x) (Commute.refl (skMat x)).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

theorem volU_continuous_skMat : Continuous (skMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [h.ne, h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop
  · simp only [if_true]
    fun_prop
  · simp only [h.ne', h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop

theorem volU_skMat_injective : Function.Injective (skMat (N := N)) := by
  intro x y h
  have h1 : ∀ a b, skMat x a b = skMat y a b := fun a b => by rw [h]
  refine Prod.ext (funext fun a => ?_) (funext fun ab => ?_)
  · simpa [skMat, Complex.I_ne_zero] using h1 a a
  · obtain ⟨⟨a, b⟩, hab⟩ := ab
    simpa [skMat, hab.ne', hab] using h1 a b

theorem volU_skMat_zero : skMat (0 : UCo N) = 0 := by
  ext a b
  simp [skMat]

theorem volU_exp_injOn : ∃ δ > 0, Set.InjOn (fun x : UCo N => NormedSpace.exp (skMat x))
    (Metric.ball 0 δ) := by
  obtain ⟨ℓ, -, -, hℓ⟩ := lcA_exists_log (n := N)
  have hc : Tendsto (skMat (N := N)) (𝓝 0) (𝓝 0) := by
    have := (volU_continuous_skMat (N := N)).tendsto 0
    rwa [volU_skMat_zero] at this
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hc.eventually hℓ)
  refine ⟨δ, hδ, fun x hx y hy hxy => volU_skMat_injective ?_⟩
  have ex := hδ' (Metric.mem_ball.1 hx)
  have ey := hδ' (Metric.mem_ball.1 hy)
  simp only at hxy ex ey
  rw [← ex, ← ey, hxy]

def volUOne (N : ℕ) : TriCo N := (fun _ => 1, 0)

theorem volU_upMat_add (t : TriCo N) : upMat (t + volUOne N) = 1 + upMat t := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [upMat, volUOne, add_comm]
  · simp [upMat, volUOne, h]

theorem volU_qrWt_one : qrWt (volUOne N) = 1 := by
  simp [qrWt, volUOne]

theorem volU_continuous_qrWt : Continuous (qrWt (N := N)) :=
  continuous_finsetProd _ fun j _ => ((continuous_apply j).comp continuous_fst).pow _

theorem volU_ball_sub_triPos {ρ : ℝ} (hρ : ρ ≤ 1) : Metric.ball (volUOne N) ρ ⊆ triPos N := by
  intro t ht j
  rw [Metric.mem_ball, dist_eq_norm] at ht
  have h1 : ‖(t - volUOne N).1 j‖ ≤ ‖t - volUOne N‖ :=
    (norm_le_pi_norm _ j).trans (norm_fst_le _)
  have h2 : (t - volUOne N).1 j = t.1 j - 1 := by simp [volUOne]
  rw [h2, Real.norm_eq_abs] at h1
  linarith [neg_le_abs (t.1 j - 1)]

theorem volU_measurableSet_triPos : MeasurableSet (triPos N) := by
  simp only [triPos, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussE_pow_odd (n : ℕ) : (∏ i ∈ range n, Real.pi ^ (2 * i + 1)) = Real.pi ^ (n ^ 2) := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem gaussE_volU_mul :
    volU N * (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) =
      Real.pi ^ (N ^ 2) := by
  have hX : Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N =
      ∏ i ∈ range N, (Real.pi ^ i * (i.factorial : ℝ) / 2) := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.sum_range_id, Finset.prod_const, Finset.card_range]
  rw [hX, volU, ← Finset.prod_mul_distrib, ← gaussE_pow_odd N]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hf : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
  field_simp
  ring

theorem gaussE_qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N := by
  have hcont : Continuous fun Z : Fin N → Fin N → ℂ => hs (Matrix.of Z) := by
    unfold hs
    simp only [Matrix.of_apply]
    fun_prop
  have h := hC (fun Z => ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))))
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hcont.neg).measurable)
  have hin : ∀ k : UNgrp N, (∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (Matrix.of (qrMap (k, t))))) *
      ENNReal.ofReal (qrWt t)) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
    intro k
    simp only [qrMap, Equiv.apply_symm_apply, gaussB_hs_unitary_mul]
    exact gaussD_tri
  simp only [hin, lintegral_const, measure_univ, mul_one, gaussC_mat] at h
  set X := Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]
    have : 0 < ∏ i ∈ range N, (i.factorial : ℝ) :=
      Finset.prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos i)
    positivity
  have hPpos : 0 < Real.pi ^ (N ^ 2) := pow_pos Real.pi_pos _
  have hCpos : 0 < C := by
    by_contra hc
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hc), zero_mul, ENNReal.ofReal_eq_zero] at h
    linarith
  rw [← ENNReal.ofReal_mul hCpos.le, ENNReal.ofReal_eq_ofReal_iff hPpos.le (by positivity)] at h
  have h2 := gaussE_volU_mul (N := N)
  rw [← hXdef] at h2
  exact mul_right_cancel₀ hXpos.ne' (h.symm.trans h2.symm)

theorem qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N :=
  gaussE_qr_const μ C hC

end ReciprocityTheory.ChartRestriction.DS
end
end
