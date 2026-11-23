module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.HfEqInner

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory


open NumberField in
theorem _root_.GlobalTheory.hermC_emb_eq_map_herm {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) = τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm G u v) :=
  (_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_herm τ G u v).symm


open NumberField in
theorem _root_.GlobalTheory.re_map_xi_eq_zero {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : E →+* ℂ) : (τ X.ξ0).re = 0 := by
  have h := congrArg τ X.ξ0_im
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg] at h
  have h2 := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at h2
  linarith


open NumberField in
theorem _root_.GlobalTheory.c_eq_two_mul_abs_im {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : X.Ψ) : X.c τ = 2 * |(τ.1 X.ξ0).im| := by
  have hre := _root_.GlobalTheory.re_map_xi_eq_zero X τ.1
  have hz : τ.1 X.ξ0 = ((τ.1 X.ξ0).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.c
  conv_lhs => rw [hz]
  simp [Complex.norm_real]

end GlobalTheory
end

section

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

private theorem ext_ballVolume : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.BallVolume := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.BallVolume
  intro D rr hr
  exact _root_.GlobalTheory.volume_ball_of_finrank_eq_two_mul (by simp) 0 hr

private theorem ext_gHadamard : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.GHadamard := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.GHadamard
  intro n M
  simpa [Real.norm_eq_abs, sq_abs] using _root_.GlobalTheory.Hadamard.norm_det_le_prod_col M

private theorem ext_cauchyBinetMax' : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.CauchyBinetMax := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.CauchyBinetMax
  intro i N r M hM hr
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.exists_two_rpow_le_norm_minor M hM (r := r) (by simpa using hr)
  refine ⟨_root_.GlobalTheory.subsetEnum S, ?_, hS⟩
  unfold _root_.GlobalTheory.subsetEnum
  exact (Finset.orderEmbOfFin _ _).strictMono

private theorem ext_detPerturbation : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbation := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbation
  intro 𝕜 _ i κ _ w σ₀ ε Δmax hΔ
  classical
  set f := (Matrix.detRowAlternating : (Fin i → 𝕜) [⋀^Fin i]→ₗ[𝕜] 𝕜).toMultilinearMap with hf
  have hD : ∀ cols : Fin i → Fin i → 𝕜, (Matrix.of fun a j => cols j a).det = f cols := by
    intro cols
    rw [show (Matrix.of fun a j => cols j a) = (Matrix.of cols).transpose from rfl, Matrix.det_transpose]
    rfl
  have hΔ0 : 0 ≤ Δmax := (norm_nonneg _).trans (hΔ σ₀)
  set coef : Fin i → Option κ → 𝕜 := fun j o => Option.elim o 1 (ε j) with hcoef
  set pick : Fin i → Option κ → κ := fun j o => Option.elim o (σ₀ j) id with hpick
  have hcol : (fun j => w (σ₀ j) + ∑ k, ε j k • w k) = fun j => ∑ o, coef j o • w (pick j o) := by
    funext j
    rw [Fintype.sum_option]
    simp [hcoef, hpick]
  have hexp : f (fun j => w (σ₀ j) + ∑ k, ε j k • w k)
      = ∑ r : Fin i → Option κ, (∏ j, coef j (r j)) • f (fun j => w (pick j (r j))) := by

    rw [hcol, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact f.map_smul_univ (fun j => coef j (r j)) (fun j => w (pick j (r j)))
  set r0 : Fin i → Option κ := fun _ => none with hr0
  have hterm0 : (∏ j, coef j (r0 j)) • f (fun j => w (pick j (r0 j))) = f (fun j => w (σ₀ j)) := by
    simp [hr0, hcoef, hpick]
  rw [hD, hD, hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hterm0, add_sub_cancel_left]
  have hbound : ∀ r : Fin i → Option κ, ‖(∏ j, coef j (r j)) • f (fun j => w (pick j (r j)))‖
      ≤ (∏ j, ‖coef j (r j)‖) * Δmax := by
    intro r
    rw [norm_smul, norm_prod]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hD]
    exact hΔ (fun j => pick j (r j))
  have hsum : ∑ r : Fin i → Option κ, ∏ j, ‖coef j (r j)‖ = ∏ j, (1 + ∑ k, ‖ε j k‖) := by
    have hps : ∏ j, ∑ o, ‖coef j o‖ = ∑ r : Fin i → Option κ, ∏ j, ‖coef j (r j)‖ := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [← hps]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.sum_option]
    simp [hcoef]
  have hone : ∏ j, ‖coef j (r0 j)‖ = 1 := by simp [hr0, hcoef]
  calc ‖∑ r ∈ Finset.univ.erase r0, (∏ j, coef j (r j)) • f (fun j => w (pick j (r j)))‖
      ≤ ∑ r ∈ Finset.univ.erase r0, (∏ j, ‖coef j (r j)‖) * Δmax :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => hbound r)
    _ = (∏ j, (1 + ∑ k, ‖ε j k‖) - 1) * Δmax := by
        rw [← Finset.sum_mul, ← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hone]
        ring

private theorem ext_detPerturbNumeric : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbNumeric := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbNumeric
  intro ρ hρ
  have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hle : (ρ : ℝ) ^ (-3 / 2 : ℝ) ≤ (ρ : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hρ1 (by norm_num)
  have hmul : (ρ : ℝ) * ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10) ≤ 1 / 10 := by
    rw [Real.rpow_neg_one] at hle
    have : (ρ : ℝ) * (ρ : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    nlinarith
  have h1 : (1 + (ρ : ℝ) ^ (-3 / 2 : ℝ) / 10) ^ ρ
      ≤ Real.exp ((ρ : ℝ) * ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      (by linarith [Real.add_one_le_exp ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10)]) ρ
  have h2 : Real.exp ((ρ : ℝ) * ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10)) ≤ Real.exp (1 / 10) :=
    Real.exp_le_exp.2 hmul
  have h3 : Real.exp (1 / 10) ≤ 3 / 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := 1 / 10) (by norm_num [abs_of_pos])
    rw [abs_le] at this
    nlinarith [this.2]
  linarith

private theorem two_pow_add_pow_sub_two_pow_mul_le (c : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∀ i : ℕ, ((2 : ℝ) ^ c + ε) ^ i - 2 ^ (c * i) ≤ i * ε * (2 ^ c + 1) ^ i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hb : (0 : ℝ) ≤ 2 ^ c := by positivity
    have hB1 : (1 : ℝ) ≤ 2 ^ c + 1 := by linarith
    have hbB : (2 : ℝ) ^ (c * i) ≤ (2 ^ c + 1) ^ (i + 1) := by
      rw [pow_mul]
      have hbase : ((2 : ℝ) ^ c) ^ i ≤ (2 ^ c + 1) ^ i :=
        pow_le_pow_left₀ hb (by linarith) i
      exact hbase.trans (pow_le_pow_right₀ hB1 (Nat.le_succ i))
    have ha : 0 ≤ (2 : ℝ) ^ c + ε := by linarith
    have hpos : 0 ≤ (i : ℝ) * ε * (2 ^ c + 1) ^ i := by positivity
    have e : ((2 : ℝ) ^ c + ε) ^ (i + 1) - 2 ^ (c * (i + 1))
        = (2 ^ c + ε) * ((2 ^ c + ε) ^ i - 2 ^ (c * i)) + ε * 2 ^ (c * i) := by
      rw [mul_add_one, pow_add (2 : ℝ) (c * i) c, pow_succ ((2 : ℝ) ^ c + ε) i]
      ring
    rw [e]
    have k1 := mul_le_mul_of_nonneg_left ih ha
    have k2 := mul_le_mul_of_nonneg_right (show (2 : ℝ) ^ c + ε ≤ 2 ^ c + 1 by linarith) hpos
    have k3 := mul_le_mul_of_nonneg_left hbB h0
    have k4 : ((i + 1 : ℕ) : ℝ) * ε * (2 ^ c + 1) ^ (i + 1)
        = (2 ^ c + 1) * (i * ε * (2 ^ c + 1) ^ i) + ε * (2 ^ c + 1) ^ (i + 1) := by
      rw [Nat.cast_succ, pow_succ ((2 : ℝ) ^ c + 1) i]
      ring
    rw [k4]
    exact add_le_add (k1.trans k2) k3

private theorem ext_detProductRest : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetProductRest := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetProductRest
  intro i c ε h0 h1
  exact two_pow_add_pow_sub_two_pow_mul_le c ε h0 h1 i

theorem _root_.GlobalTheory.ext_all_inputs : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.All := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.All
  exact ⟨_root_.GlobalTheory.packingCount, _root_.GlobalTheory.gaussTail_of_card_le, ext_ballVolume, ext_gHadamard,
    _root_.GlobalTheory.nearestPlane_rounding, ext_cauchyBinetMax', ext_detPerturbation,
    ext_detPerturbNumeric, ext_detProductRest⟩

end GlobalTheory
end

section

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw

noncomputable section

namespace GlobalTheory.ThetaExist

theorem coeff_eq_zero_of_orthonormal {C H κ : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : C →L[ℂ] H) (e : κ → C)
    (h : Orthonormal ℂ fun i => T (e i)) {c : κ → ℂ} (hs : HasSum (fun i => c i • e i) 0)
    (k : κ) : c k = 0 := by
  classical
  have h1 := ((innerSL ℂ (T (e k))).comp T).hasSum hs
  simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, map_zero,
    orthonormal_iff_ite.1 h, smul_eq_mul, mul_ite, mul_one, mul_zero] at h1
  have h2 : HasSum (fun i => if k = i then c i else 0) (c k) := by
    convert hasSum_ite_eq k (c k) using 2 with i
    by_cases hi : k = i
    · simp [hi]
    · simp [hi, Ne.symm hi]
  exact h2.unique h1

theorem coeff_eq_zero_of_fourier {d : Type*} [Fintype d] {c : (d → ℤ) → ℂ}
    (hc : Summable fun n => ‖c n‖)
    (h0 : ∀ t : d → ℝ, ∑' n, c n * cexp (2 * Real.pi * I * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) = 0)
    (k : d → ℤ) : c k = 0 := by
  refine coeff_eq_zero_of_orthonormal _ UnitAddTorus.mFourier
    (UnitAddTorus.orthonormal_mFourier (d := d)) ?_ k
  have hs : Summable fun n => c n • UnitAddTorus.mFourier n :=
    .of_norm (by simpa [norm_smul, UnitAddTorus.mFourier_norm] using hc)
  suffices h : (0 : C(UnitAddTorus d, ℂ)) = ∑' n, c n • UnitAddTorus.mFourier n from
    h ▸ hs.hasSum
  ext x
  have hx : ∃ t : d → ℝ, x = fun j => (t j : UnitAddCircle) := by
    choose t ht using fun j => QuotientAddGroup.mk_surjective (x j)
    exact ⟨t, funext fun j => (ht j).symm⟩
  obtain ⟨t, rfl⟩ := hx
  rw [← ContinuousMap.tsum_apply hs, ContinuousMap.zero_apply, ← h0 t]
  refine tsum_congr fun n => ?_
  simp only [ContinuousMap.smul_apply, smul_eq_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {ι : Type} [Fintype ι]

def expH (w : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι → ℂ := fun v => cexp (Real.pi * Hf v w)

theorem differentiable_Hf (a : EuclideanSpace ℂ ι) :
    Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v a := by
  simp_rw [FPw.Hf_eq_inner]
  exact (innerSL ℂ a).differentiable

theorem re_Hf_le (v a : EuclideanSpace ℂ ι) : (Hf v a).re ≤ ‖v‖ * ‖a‖ := by
  rw [FPw.Hf_eq_inner, mul_comm]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

theorem norm_term_le (Y : GT ι) (w : EuclideanSpace ℂ ι) {R : ℝ} (hw : ‖w‖ ≤ R) (γ : lat Y.b)
    {v : EuclideanSpace ℂ ι} (hv : ‖v‖ ≤ R) :
    ‖Y.ka γ * paU 1 γ (expH w) v‖ ≤ Real.exp (5 * Real.pi * R ^ 2) *
      Real.exp (-(Real.pi / 4) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) := by
  set g : EuclideanSpace ℂ ι := γ.1
  unfold paU expH
  rw [norm_mul, Y.ka_abs g γ.2, one_mul, ← Complex.exp_add, Complex.norm_exp, ← Real.exp_add,
    Real.exp_le_exp, Hf_self, sub_eq_add_neg v, Hf_add_left]
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  have h1 : (Hf v g).re ≤ R * ‖g‖ := (re_Hf_le v g).trans (by gcongr)
  have h2 : (Hf v w).re ≤ R * R := (re_Hf_le v w).trans (by gcongr)
  have h3 : (Hf (-g) w).re ≤ ‖g‖ * R := (re_Hf_le (-g) w).trans (by rw [norm_neg]; gcongr)
  have e : (((1 : ℕ) : ℂ) * Real.pi * Hf v g - ((1 : ℕ) : ℂ) * Real.pi * ((‖g‖ : ℝ) : ℂ) ^ 2 / 2 +
      Real.pi * (Hf v w + Hf (-g) w)).re =
      Real.pi * ((Hf v g).re - ‖g‖ ^ 2 / 2 + (Hf v w).re + (Hf (-g) w).re) := by
    simp only [← Complex.ofReal_pow]
    simp only [Nat.cast_one, one_mul, add_re, sub_re, re_ofReal_mul, div_ofNat_re, ofReal_re]
    ring
  rw [e]
  have : (Hf v g).re - ‖g‖ ^ 2 / 2 + (Hf v w).re + (Hf (-g) w).re ≤ 5 * R ^ 2 - ‖g‖ ^ 2 / 4 := by
    nlinarith [sq_nonneg (‖g‖ / 2 - 2 * R)]
  nlinarith [mul_le_mul_of_nonneg_left this Real.pi_pos.le]

theorem summable_gauss (Y : GT ι) {a : ℝ} (ha : 0 < a) :
    Summable fun γ : lat Y.b => Real.exp (-a * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) :=
  summable_lattice_exp_neg_mul_norm_sq (lat Y.b) ha

theorem differentiable_paTh (Y : GT ι) (w : EuclideanSpace ℂ ι) :
    Differentiable ℂ (paTh Y 1 (expH w)) := by
  rw [← differentiableOn_univ]
  refine SCV.differentiableOn_tsum_of_locally_normal
    (F := fun (γ : lat Y.b) v => Y.ka γ * paU 1 γ (expH w) v) isOpen_univ (fun γ => ?_)
    (fun x _ => ?_)
  · have h1 := differentiable_Hf (γ : EuclideanSpace ℂ ι)
    have h2 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf (v - γ.1) w :=
      (differentiable_Hf w).comp (differentiable_id.sub_const _)
    unfold paU expH
    refine Differentiable.differentiableOn ?_
    fun_prop
  · refine ⟨Metric.ball 0 (max (‖x‖ + 1) ‖w‖), Metric.isOpen_ball.mem_nhds ?_, _,
      (summable_gauss Y (a := Real.pi / 4) (by positivity)).mul_left _,
      fun γ z hz => norm_term_le Y w (le_max_right _ _) γ (mem_ball_zero_iff.1 hz).le⟩
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)

theorem paTh_centre (Y : GT ι) (v : EuclideanSpace ℂ ι) :
    paTh Y 1 (expH v) v = cexp (Real.pi * Hf v v) *
      ∑' γ : lat Y.b, (Y.ka γ * (Real.exp (-(Real.pi / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) : ℝ)) *
        cexp (2 * Real.pi * I * ((Hf v γ).im : ℂ)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  set g : EuclideanSpace ℂ ι := γ.1
  unfold paU expH
  rw [Hf_self g, sub_eq_add_neg v, Hf_add_left, Hf_neg_left, ← Hf_conj v g, conj_eq_sub (Hf v g),
    ← Complex.exp_add, Complex.ofReal_exp, mul_assoc (Y.ka g), ← Complex.exp_add,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem exists_sec_ne_zero (Y : GT ι) (hC : Coc Y 1) : ∃ s ∈ Y.Sec 1, s ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hz : ∀ w, paTh Y 1 (expH w) = 0 := fun w =>
    hcon _ ⟨differentiable_paTh Y w, fun γ hγ v => paTh_add hC _ hγ v⟩
  set B := Y.b.restrictScalars ℤ with hB
  set c : lat Y.b → ℂ := fun γ =>
    Y.ka γ * (Real.exp (-(Real.pi / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) : ℝ) with hc
  have hcs : Summable fun γ => ‖c γ‖ := by
    refine (summable_gauss Y (a := Real.pi / 2) (by positivity)).congr fun γ => ?_
    rw [hc]
    simp only [norm_mul, Y.ka_abs γ γ.2, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  choose x _ hx using fun j => Y.perfect (B.coord j).toAddMonoidHom
  have key := coeff_eq_zero_of_fourier (c := fun n => c (B.equivFun.symm n))
    ((B.equivFun.symm.toEquiv.summable_iff (f := fun γ => ‖c γ‖)).2 hcs) (fun t => ?_) 0
  · simp [hc, ka_zero hC] at key
  · set v : EuclideanSpace ℂ ι := ∑ j, (t j : ℂ) • x j with hv
    have h1 := paTh_centre Y v
    rw [hz v, Pi.zero_apply, eq_comm, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)] at h1
    rw [← h1, ← B.equivFun.symm.toEquiv.tsum_eq]
    refine tsum_congr fun n => ?_
    have h2 : ∀ j, (Hf (x j) (B.equivFun.symm n : lat Y.b)).im = n j := fun j => by
      rw [← hx j]
      simp [Finsupp.single_apply]
    suffices h3 : ∑ j, (n j : ℝ) * t j = (Hf v (B.equivFun.symm n : lat Y.b)).im by
      rw [h3]; rfl
    simp only [FPw.Hf_eq_inner] at h2 ⊢
    rw [hv, inner_sum, Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, Complex.im_ofReal_mul, h2, mul_comm]

theorem exists_theta_ne_zero (E : Type) [Field E] [NumberField E] (X : PT E) :
    ∃ s ∈ X.Sec 1 1, s ≠ 0 := by
  let Y : GT (Idx X.dim) :=
    { b := X.b
      integral := X.integral
      perfect := X.perfect
      ka := fun γ => (X.eps γ : ℂ)
      ka_abs := fun x hx => by rcases X.eps_pm x hx with h | h <;> simp [h] }
  have hC : Coc Y 1 := by
    intro γ hγ δ hδ
    obtain ⟨k, hk⟩ := X.integral γ δ hγ hδ
    have h := congrArg (fun r : ℝ => (r : ℂ)) (X.eps_add γ hγ δ hδ)
    change ((X.eps (γ + δ) : ℤ) : ℂ) = (X.eps γ : ℂ) * (X.eps δ : ℂ) * _
    rw [hk] at h ⊢
    have hs : Complex.sin (-(Real.pi * (1 : ℕ) * ((k : ℝ) : ℂ))) = 0 := by
      rw [Complex.sin_neg]
      simpa [mul_comm] using Complex.sin_int_mul_pi k
    rw [Complex.exp_mul_I, hs, Complex.cos_neg]
    simpa using h
  obtain ⟨s, ⟨hd, hs⟩, hne⟩ := exists_sec_ne_zero Y hC
  refine ⟨fun v => s (v 0), ⟨hd.comp (differentiable_apply 0), fun γ hγ v => ?_⟩, fun h => hne ?_⟩
  · have := hs (γ 0) (hγ 0) (v 0)
    simpa [HC, Y] using this
  · funext z
    exact congrFun h fun _ => z

end GlobalTheory.ThetaExist
end
end
