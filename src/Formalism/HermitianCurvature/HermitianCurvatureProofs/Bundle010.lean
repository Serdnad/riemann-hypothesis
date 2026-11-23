module

public import Formalism.HermitianCurvature.Bundle001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle004
public import Formalism.HermitianCurvature.Bundle002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle005
public import Formalism.HermitianCurvature.StatementLE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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
public import Formalism.DoubleCosetMeasures.Statement
import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Pi
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.S3x9

open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)

end Formalism.FourierDecayAlt.P.S3x9
end

section

namespace Formalism.FourierDecayAlt.P.K

open Matrix Finset Real Formalism.FourierDecayAlt.K

variable {K : Type} [Field K] {n : ℕ}

theorem jointTheoremA : JointTheoremA := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.coarseBound
  refine ⟨2 * C₀, C, ?_⟩
  intro Kx Θ f r e σ hKx hf hΘ hr he hσ hrec
  have hΘ1 : 1 ≤ Θ := by linarith
  have hΘpos : 0 < Θ := by linarith
  have ha0 : 0 ≤ C₀ / Θ := div_nonneg (by linarith) hΘpos.le
  have hq : C₀ / Θ ≤ 1 / 2 := by
    rw [div_le_iff₀ hΘpos]
    linarith
  have ha : (C₀ / Θ) ^ f ≤ 1 / 2 := by
    calc (C₀ / Θ) ^ f ≤ (C₀ / Θ) ^ 1 := pow_le_pow_of_le_one ha0 (by linarith) hf
      _ ≤ 1 / 2 := by rw [pow_one]; exact hq
  have hrp : Θ ^ (-(Kx - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ1 (by linarith)
  have hε0 : 0 ≤ C₀ * Θ ^ (-(Kx - 5 / 2)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hΘpos.le _)
  have hεa : (C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (C₀ / Θ) ^ f := by
    apply pow_le_pow_left₀ hε0
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrp (by linarith)
  exact hC r ((C₀ / Θ) ^ f) ((C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f) e σ (pow_nonneg ha0 _) ha
    (pow_nonneg hε0 _) hεa hr he hσ hrec

end Formalism.FourierDecayAlt.P.K

theorem Formalism.FourierDecayAlt.P.joint_theorem_A' : Formalism.FourierDecayAlt.K.JointTheoremA := Formalism.FourierDecayAlt.P.K.jointTheoremA
end

section

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity

open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB

theorem sum_re_nonneg {α : Type} (Y : Finset α) (κ G : α → α → ℂ) (hκ : PSDOn Y κ) (hG : PSDOn Y G) :
    0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G h h').re := by
  have H := (Matrix.PosSemidef.hadamard hκ hG).re_dotProduct_nonneg (fun _ => (1 : ℂ))
  simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
    star_one, one_mul, mul_one, RCLike.re_to_complex] at H
  convert H using 2
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.sum_coe_sort Y]

variable {E W : Type} [Field E] (D : Data E W)

theorem baseGram_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (sum_re_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le

theorem Wb_mono {n m : ℕ} (h : n ≤ m) : D.Wb n ⊆ D.Wb m := by
  intro x hx
  simp only [Data.Wb, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem estBlockOfSumForm_ok : EstBlockOfSumForm := by
  intro E W _ D C₄ hG hW hSF ε hε i s hs hsi hir w hw hcnt hvol
  obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF ε hε i s hs hsi hir w hw hcnt hvol
  have hsub : D.Wb (D.cnt w + s * D.K) ⊆ D.Wb (D.cnt w + (s + 1) * D.K) :=
    Wb_mono D (by nlinarith)
  have hext : ∀ g : W → ℝ, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K), θ w' * g w' =
      ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * g w' := by
    intro g
    symm
    refine Finset.sum_subset hsub (fun x _ hx => ?_)
    rw [hθ.2.1 x hx, zero_mul]
  refine ⟨θ, ⟨hθ.1, fun a ha => hθ.2.1 a (fun h => ha (hsub h)), ?_⟩, ?_⟩
  · have := hext (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hθ.2.2]
  · intro Y hY κ hκ t₀ S hS
    have h := hb Y hY κ hκ t₀ S hS
    rw [hext]
    have hX : 0 ≤ ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ :=
      Finset.sum_nonneg (fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ _ Y κ hκ))
    exact h.trans (mul_le_mul_of_nonneg_right hMv hX)

end Formalism.FourierDecayAlt.P.BaseGramNonnegativity

theorem Formalism.FourierDecayAlt.P.blockEstimateOfCosetSum : Formalism.FourierDecayAlt.crystallineComparison.EstBlockOfSumForm :=
  Formalism.FourierDecayAlt.P.BaseGramNonnegativity.estBlockOfSumForm_ok
end
end

section

open MeasureTheory Set Finset Function

noncomputable section

namespace Formalism.FourierDecayAlt.P.LatticeSummability

open Formalism.FourierDecayAlt.crystallineComparison

theorem mfac_nonneg (K : ℕ) {L : ℝ} (hL : 0 ≤ L) (a : ℝ) (ha : 0 ≤ a) : 0 ≤ mfac K L a := by
  unfold mfac
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (by positivity)

theorem mfac_anti (K : ℕ) {L : ℝ} (hL : 0 < L) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    mfac K L b' ≤ mfac K L b := by
  unfold mfac
  by_cases hb0 : b = 0
  · rw [if_pos hb0]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hb'0 : b' ≠ 0 := by linarith
    rw [if_neg hb0, if_neg hb'0]
    refine min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hL.le (by linarith)) ?_ K)
    exact div_le_div_of_nonneg_left hL.le hbpos hbb

end Formalism.FourierDecayAlt.P.LatticeSummability
end
end

section

open MeasureTheory Set

noncomputable section

namespace Formalism.FourierDecayAlt.P.MajorantIntegrals

open Formalism.FourierDecayAlt.crystallineComparison

theorem radial_eq (K : ℕ) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : 0 < y) :
    y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y =
      if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K) := by
  rw [Complex.finrank_real_complex]
  simp only [mfac, hy.ne', if_false, smul_eq_mul, show 2 - 1 = 1 from rfl, pow_one]
  split_ifs with hxy
  · rw [min_eq_left (one_le_pow₀ ((one_le_div hy).mpr hxy)), mul_one]
  · push Not at hxy
    have h1 : (x / y) ^ K ≤ 1 :=
      pow_le_one₀ (div_nonneg hx.le hy.le) ((div_le_one hy).mpr hxy.le)
    rw [min_eq_right h1, Real.rpow_sub hy, Real.rpow_one, Real.rpow_natCast, div_pow]
    field_simp

theorem volC : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
  simp [Measure.real, Complex.volume_ball]

theorem majIntegral_ok : MajIntegral := by
  intro K x hK hx
  have hK' : (2 : ℝ) < K := by exact_mod_cast hK
  have hcongr : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y)
      (fun y => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioi 0) :=
    fun y hy => radial_eq K x hx y hy
  have hIoc : IntegrableOn (fun y : ℝ => y) (Ioc 0 x) :=
    (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hIoi : IntegrableOn (fun y : ℝ => x ^ K * y ^ ((1 : ℝ) - K)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx).const_mul _
  have hA : IntegrableOn (fun y : ℝ => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioc 0 x) :=
    hIoc.congr_fun (fun y hy => by simp [hy.2]) measurableSet_Ioc
  have hB : IntegrableOn (fun y : ℝ => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioi x) :=
    hIoi.congr_fun (fun y hy => by simp [not_le.mpr (mem_Ioi.mp hy)]) measurableSet_Ioi
  have hint : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y) (Ioi 0) := by
    refine IntegrableOn.congr_fun ?_ hcongr.symm measurableSet_Ioi
    rw [← Ioc_union_Ioi_eq_Ioi hx.le]
    exact hA.union hB
  refine ⟨(integrable_fun_norm_addHaar volume (f := mfac K x)).mpr hint, ?_⟩
  rw [integral_fun_norm_addHaar volume (mfac K x), setIntegral_congr_fun measurableSet_Ioi hcongr,
    ← Ioc_union_Ioi_eq_Ioi hx.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hA hB,
    setIntegral_congr_fun measurableSet_Ioc (fun y hy => if_pos hy.2),
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => if_neg (not_le.mpr (mem_Ioi.mp hy))),
    ← intervalIntegral.integral_of_le hx.le, integral_id, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) hx, volC, Complex.finrank_real_complex]
  have e : x ^ K * x ^ ((1 : ℝ) - K + 1) = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]
    rw [show (K : ℝ) + (1 - K + 1) = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hK2 : (K : ℝ) - 2 ≠ 0 := by linarith
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  rw [neg_div, mul_neg, ← mul_div_assoc, e]
  have hK4 : (1 : ℝ) - K + 1 = -((K : ℝ) - 2) := by ring
  rw [hK4]
  field_simp
  ring

theorem majIntegralProd_ok : MajIntegralProd := by
  intro f K x hK hx
  have h1 := fun v => (majIntegral_ok K (x v) hK (hx v))
  refine ⟨Integrable.fintype_prod (f := fun v (l : ℂ) => mfac K (x v) ‖l‖)
    (μ := fun _ => volume) (fun v => (h1 v).1), ?_⟩
  have h2 := integral_fintype_prod_volume_eq_prod (ι := Fin f) (E := fun _ => ℂ)
    (fun v (l : ℂ) => mfac K (x v) ‖l‖)
  exact h2.trans (Finset.prod_congr rfl (fun v _ => (h1 v).2))

end Formalism.FourierDecayAlt.P.MajorantIntegrals
end
end

section

open Filter Topology Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.MeanBoundsLimits

open Classical

open Formalism.FourierDecayAlt.crystallineComparison

section Mean

variable {Λ : Type} [AddCommGroup Λ] {LIM : (Λ → ℂ) → ℂ}

theorem bdd_const (c : ℂ) : Bdd (fun _ : Λ => c) := ⟨‖c‖, fun _ => le_rfl⟩

theorem lim_const (hM : IsMean LIM) (c : ℂ) : LIM (fun _ : Λ => c) = c := by
  have e : (fun _ : Λ => c) = c • (fun _ : Λ => (1 : ℂ)) := by funext; simp
  rw [e, hM.2.1 c _ (bdd_const 1), hM.2.2.2.1, mul_one]

theorem lim_real (hM : IsMean LIM) (q : Λ → ℂ) (B : ℝ) (hq : ∀ x, ‖q x‖ ≤ B)
    (hr : ∀ x, (q x).im = 0) : (LIM q).im = 0 ∧ (LIM q).re ≤ B := by
  have hqb : Bdd q := ⟨B, hq⟩
  have hre : ∀ x, |(q x).re| ≤ B := fun x => (Complex.abs_re_le_norm _).trans (hq x)
  have h1 := hM.2.2.1 (q + fun _ => (B : ℂ)) (Bdd_add hqb) (fun x => by
    simp only [Pi.add_apply, Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
      hr x, add_zero]
    exact ⟨by linarith [(abs_le.mp (hre x)).1], trivial⟩)
  rw [hM.1 _ _ hqb (bdd_const _), lim_const hM] at h1
  have hneg : Bdd ((-1 : ℂ) • q) := ⟨B, fun x => by simpa using hq x⟩
  have h2 := hM.2.2.1 ((fun _ => (B : ℂ)) + (-1 : ℂ) • q) (bdd_const_add hneg) (fun x => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.ofReal_re,
      Complex.add_im, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, hr x]
    norm_num
    linarith [(abs_le.mp (hre x)).2])
  rw [hM.1 _ _ (bdd_const _) hneg, lim_const hM, hM.2.1 _ _ hqb] at h2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.add_re, Complex.ofReal_re] at h1 h2
  constructor
  · linarith [h1.2]
  · simp at h2; linarith [h2.1]
where
  Bdd_add {g : Λ → ℂ} (hg : Bdd g) : Bdd (g + fun _ => (B : ℂ)) :=
    Formalism.FourierDecayAlt.P.E2.bdd_add' hg (bdd_const _)
  bdd_const_add {g : Λ → ℂ} (hg : Bdd g) : Bdd ((fun _ => (B : ℂ)) + g) :=
    Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_const _) hg

theorem meanBound_ok : MeanBound := by
  intro Λ _ LIM g B hM hg
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  set z := LIM g with hz
  by_cases z0 : z = 0
  · rw [z0, norm_zero]; exact hB
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr z0
  set u : ℂ := starRingEnd ℂ z / ‖z‖ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self]
    exact norm_ne_zero_iff.mpr z0
  have hgb : Bdd g := ⟨B, hg⟩
  set h := u • g with hh
  have hhb : ∀ x, ‖h x‖ ≤ B := fun x => by
    simp only [hh, Pi.smul_apply, smul_eq_mul, norm_mul, hu1, one_mul]; exact hg x
  have hLh : LIM h = ‖z‖ := by
    rw [hh, hM.2.1 u g hgb, ← hz, hu, div_mul_eq_mul_div, Complex.conj_mul', pow_two,
      mul_div_assoc, div_self hn, mul_one]
  set hr : Λ → ℂ := fun x => ((h x).re : ℂ)
  set hi : Λ → ℂ := fun x => ((h x).im : ℂ)
  have hrb : ∀ x, ‖hr x‖ ≤ B := fun x => by
    simp only [hr, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hhb x)
  have hib : ∀ x, ‖hi x‖ ≤ B := fun x => by
    simp only [hi, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hhb x)
  have hsplit : h = hr + Complex.I • hi := by
    funext x; simp only [hr, hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm Complex.I]; exact (Complex.re_add_im (h x)).symm
  have hL := congrArg LIM hsplit
  rw [hM.1 _ _ ⟨B, hrb⟩ (Formalism.FourierDecayAlt.P.E2.bdd_smul' _ ⟨B, hib⟩), hM.2.1 _ _ ⟨B, hib⟩, hLh] at hL
  have R := lim_real hM hr B hrb (fun x => by simp [hr])
  have I := lim_real hM hi B hib (fun x => by simp [hi])
  have := congrArg Complex.re hL
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, I.1, zero_sub, neg_zero, add_zero] at this
  linarith [R.2]

end Mean

theorem bdd_inner {f : ℕ} {Λ : AddSubgroup (V f)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (p q : V f → H) (B : ℝ) (hp : ∀ x, ‖p x‖ ≤ B) (hq : ∀ x, ‖q x‖ ≤ B)
    (σ : V f) : Bdd (fun x : Λ => inner ℂ (p x) (q ((x : V f) + σ))) :=
  ⟨B * B, fun x => (norm_inner_le_norm _ _).trans
    (mul_le_mul (hp _) (hq _) (norm_nonneg _) ((norm_nonneg _).trans (hp x)))⟩

theorem lim_of_tendsto {f : ℕ} {Λ : AddSubgroup (V f)} {LIM : (Λ → ℂ) → ℂ}
    (hM : IsMeanInf Λ LIM) (F : V f → ℂ) (L : ℂ) (hF : Bdd (fun x : Λ => F x))
    (ht : Tendsto F (atInfAll f) (𝓝 L)) : LIM (fun x : Λ => F x) = L := by
  have hD : Bdd (fun x : Λ => F x - L) := by
    obtain ⟨b, hb⟩ := hF
    exact ⟨b + ‖L‖, fun x => (norm_sub_le _ _).trans (by linarith [hb x])⟩
  have h0 : LIM (fun x : Λ => F x - L) = 0 := by
    apply hM.2 _ hD
    have := (ht.comp (tendsto_comap (f := fun x : Λ => (x : V f)))).sub_const L
    simpa [Function.comp_def] using this
  have e : (fun x : Λ => F x) = (fun x : Λ => F x - L) + (fun _ => L) := by funext; simp
  rw [e, hM.1.1 _ _ hD (bdd_const L), h0, lim_const hM.1, zero_add]

theorem meanSplit_ok : MeanSplit := by
  intro f Λ LIM H _ _ a r Nh B hM hb haa har hra
  have hpa : ∀ x, ‖a x‖ ≤ B := fun x => (hb x).1
  have hpr : ∀ x, ‖r x‖ ≤ B := fun x => (hb x).2
  constructor
  · intro σ hσ
    have e : (fun x : Λ => inner ℂ (a x + r x) (a ((x : V f) + σ) + r ((x : V f) + σ))) =
        (fun x : Λ => inner ℂ (a x) (a ((x : V f) + σ))) +
        (fun x : Λ => inner ℂ (a x) (r ((x : V f) + σ))) +
        ((fun x : Λ => inner ℂ (r x) (a ((x : V f) + σ))) +
         (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ)))) := by
      funext x; simp only [Pi.add_apply, inner_add_left, inner_add_right]; ring
    rw [e, hM.1.1 _ _ (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ))
        (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner r a B hpr hpa σ) (bdd_inner r r B hpr hpr σ)),
      hM.1.1 _ _ (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ),
      hM.1.1 _ _ (bdd_inner r a B hpr hpa σ) (bdd_inner r r B hpr hpr σ),
      lim_of_tendsto hM (fun x => inner ℂ (a x) (a (x + σ))) (Nh σ) (bdd_inner a a B hpa hpa σ)
        (haa σ hσ),
      lim_of_tendsto hM (fun x => inner ℂ (a x) (r (x + σ))) 0 (bdd_inner a r B hpa hpr σ)
        (har σ hσ),
      lim_of_tendsto hM (fun x => inner ℂ (r x) (a (x + σ))) 0 (bdd_inner r a B hpr hpa σ)
        (hra σ hσ)]
    ring
  · intro S c hS
    have hS' : ∀ σ ∈ S, σ ∈ Λ := hS
    have hpd := Formalism.FourierDecayAlt.P.mean_matrix_posDef Λ H LIM hM.1.1 hM.1.2.1
      (fun g hg hpos => (hM.1.2.2.1 g hg hpos).1) hM.1.2.2.2.2 (fun x => r x) B (fun x => hpr x)
      (S.subtype (fun x => x ∈ Λ)) (fun σ => c σ)
    have eq : (∑ σ ∈ S, ∑ σ' ∈ S, (LIM fun x : Λ => inner ℂ (r x) (r ((x : V f) + (σ - σ')))) *
        c σ * starRingEnd ℂ (c σ')) =
        ∑ σ ∈ S.subtype (fun x => x ∈ Λ), ∑ σ' ∈ S.subtype (fun x => x ∈ Λ),
          (LIM fun x : Λ => inner ℂ (r x) (r ((x + (σ - σ') : Λ) : V f))) * c σ *
            starRingEnd ℂ (c σ') := by
      rw [← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']
      refine Finset.sum_congr rfl (fun σ' _ => ?_)
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub]
    beta_reduce
    rw [eq]
    exact hpd

end Formalism.FourierDecayAlt.P.MeanBoundsLimits

theorem Formalism.FourierDecayAlt.P.mean_bound_estimate : Formalism.FourierDecayAlt.crystallineComparison.MeanBound := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanBound_ok
theorem Formalism.FourierDecayAlt.P.mean_split_identity : Formalism.FourierDecayAlt.crystallineComparison.MeanSplit := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanSplit_ok
end
end

section

namespace Formalism.FourierDecayAlt.P.LEx2.A3
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

def DsMeas : Prop := ∀ (B : Base) (S : Step B), S.Meas → S.I4 → ∀ Y ∈ S.J, ∀ (p : ℕ) k, Measurable fun ω => S.ds Y p ω k

theorem meas_iterDeriv {Ω : Type} [MeasurableSpace Ω] (F : ℝ → Ω → ℂ)
    (hsm : ∀ ω, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => F s ω)) (hm : ∀ s, Measurable (F s)) :
    ∀ (p : ℕ) (s : ℝ), Measurable (fun ω => iteratedDeriv p (fun s => F s ω) s) := by
  intro p
  induction p with
  | zero => intro s; simpa using hm s
  | succ p ih =>
    intro s
    have hlim : ∀ ω, Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) atTop
        (𝓝 (iteratedDeriv (p + 1) (fun s => F s ω) s)) := by
      intro ω
      have hd : Differentiable ℝ (iteratedDeriv p (fun s => F s ω)) :=
        (hsm ω).differentiable_iteratedDeriv p (by exact_mod_cast WithTop.coe_lt_top _)
      have h1 := (hd s).hasDerivAt.tendsto_slope_zero
      rw [iteratedDeriv_succ]
      refine h1.comp ?_
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall (fun n => by
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact this.ne')
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) ω => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) ?_ ?_
    · intro n
      exact ((ih _).sub (ih _)).const_smul (((1 : ℝ) / ((n : ℝ) + 1))⁻¹)
    · exact tendsto_pi_nhds.2 hlim

theorem dsMeas : DsMeas := by
  intro B S hMeas hI4 Y hY p k
  obtain ⟨c, hc⟩ := hI4 Y hY
  have := meas_iterDeriv (fun s ω => S.gs Y s ω k) (fun ω => by
      have : (fun s : ℝ => S.gs Y s ω k) = fun s : ℝ => ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * c q ω k := by
        funext s; exact hc s ω k
      rw [this]
      apply ContDiff.sum
      intro q _
      exact (Complex.ofRealCLM.contDiff.pow q).mul contDiff_const)
    (fun s => (hMeas.2.2 Y hY).2 s k) p 0
  exact this

end
end Formalism.FourierDecayAlt.P.LEx2.A3
end
