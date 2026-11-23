module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DifferentiableZeroModeLiftOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ThetaSectionPointwiseNormSqEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofTorMkCIsQuotientMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaNA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.MemSpanBn
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col ZM

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem zeroMode_pointwise_bound [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (w : Vsp X.dim) (T M : ℝ)
    (hT : ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) ≤ T)
    (hM : ∀ t, (Col.YB hI hP 1).ptN2 1 (ZM.zmB hI s) t ≤ M) :
    Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.sqrt M * T := by
  classical
  choose γ hγL hγ using fun m : Fin (Module.finrank ℝ (IR I)) → ℤ => dual_lift hI m
  obtain ⟨E0, hE0def⟩ : ∃ e : ℝ,
      Real.exp (-Real.pi * ‖uc (IR I) w‖ ^ 2 - Real.pi / 2 * ‖p2 (IR I) w‖ ^ 2) = e := ⟨_, rfl⟩
  have hE0 : 0 < E0 := hE0def ▸ Real.exp_pos _

  have hmode : ∀ m, ‖zmC hI s m w‖ * E0 ≤
      Real.sqrt M * Real.exp (-Real.pi * ‖uMap I w - uMap I (-γ m)‖ ^ 2) := by
    intro m
    rw [← hE0def, mode_norm hI hP hs (hγL m) m (hγ m) w]
    have h1 : uMap I w - uMap I (-γ m) = uc (IR I) w + uc (IR I) (γ m) := by
      rw [map_neg, sub_neg_eq_add, uMap_eq_uc, uMap_eq_uc]
    rw [h1]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hM _)) (Real.exp_pos _).le

  have hinj : Function.Injective (fun m => uMap I (-γ m)) := by
    intro m m' h
    have h' : uc (IR I) (γ m) = uc (IR I) (γ m') := by
      simp only [map_neg, uMap_eq_uc, neg_inj] at h
      exact h
    funext i
    have e1 := hγ m i
    have e2 := hγ m' i
    rw [← Col.inner_uc (K := IR I) (γ m) _ (Ib hI i).2, h',
      Col.inner_uc (K := IR I) (γ m') _ (Ib hI i).2, e2] at e1
    exact_mod_cast e1.symm
  have hfin : ∀ F : Finset (Fin (Module.finrank ℝ (IR I)) → ℤ),
      ∑ m ∈ F, ‖zmC hI s m w‖ * E0 ≤ Real.sqrt M * T := by
    intro F
    calc ∑ m ∈ F, ‖zmC hI s m w‖ * E0
        ≤ ∑ m ∈ F, Real.sqrt M * Real.exp (-Real.pi * ‖uMap I w - uMap I (-γ m)‖ ^ 2) :=
          Finset.sum_le_sum fun m _ => hmode m
      _ = Real.sqrt M * ∑ y ∈ F.image (fun m => uMap I (-γ m)),
            Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.sum_image (fun a _ b _ h => hinj h)]
      _ ≤ Real.sqrt M * T := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          apply hT
          intro y hy
          obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hy
          exact ⟨-γ m, X.L.neg_mem (hγL m), rfl⟩
  have hsumN : Summable fun m : Fin (Module.finrank ℝ (IR I)) → ℤ => ‖zmC hI s m w‖ := by
    apply summable_of_sum_le (c := Real.sqrt M * T / E0) (fun m => norm_nonneg _)
    intro F
    rw [le_div_iff₀ hE0, Finset.sum_mul]
    exact hfin F

  have hF := tof_torus_inversion (fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => zmG I s (w + tb hI t))
    (fib_continuous hI hs w) (fun x n => fib_periodic hI hs w x n) hsumN.of_norm
  have hF' : HasSum (fun m => zmC hI s m w) (zmG I s w) := by
    have h0 : zmG I s w = zmG I s (w + tb hI 0) := by simp [tb]
    rw [h0]
    exact hF
  have hsq : Real.sqrt (X.ptN2 1 s fun _ => w) = ‖zmG I s w‖ * E0 := by
    rw [thetaSectionPointwiseNormSq_eq hI s w]
    have hexp : Real.exp (-(2 * Real.pi) * ‖uc (IR I) w‖ ^ 2 - Real.pi * ‖p2 (IR I) w‖ ^ 2) =
        E0 ^ 2 := by
      rw [← hE0def, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp, ← mul_pow, Real.sqrt_sq (mul_nonneg (norm_nonneg _) hE0.le)]
  calc Real.sqrt (X.ptN2 1 s fun _ => w) = ‖zmG I s w‖ * E0 := hsq
    _ ≤ (∑' m, ‖zmC hI s m w‖) * E0 := by
        gcongr
        rw [← hF'.tsum_eq]
        exact norm_tsum_le_tsum_norm hsumN
    _ = ∑' m, ‖zmC hI s m w‖ * E0 := tsum_mul_right.symm
    _ ≤ Real.sqrt M * T := (hsumN.mul_right _).tsum_le_of_sum_le hfin

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex MeasureTheory

noncomputable section

theorem ct_expo_vec {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (w ua y : V)
    {q M1 r : ℝ} (hq : 0 < q) (hw : ‖w‖ ≤ r)
    (hc6 : |2 * inner ℝ (q • ua) y| ≤ M1 * ‖y‖ ^ 2) :
    Real.pi * q * ‖ua‖ ^ 2 - Real.pi * q * ‖w - (ua + y)‖ ^ 2 ≤
      2 * Real.pi * r * (q * ‖ua‖ + q * ‖y‖) - Real.pi * (q - M1) * ‖y‖ ^ 2 := by
  have e1 : ‖w - (ua + y)‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w ua - 2 * inner ℝ w y + ‖ua‖ ^ 2 +
      2 * inner ℝ ua y + ‖y‖ ^ 2 := by
    rw [@norm_sub_sq_real, @norm_add_sq_real, inner_add_right]
    ring
  have hua := norm_nonneg ua
  have hy := norm_nonneg y
  have hpq : 0 ≤ Real.pi * q := by positivity
  have t1 : Real.pi * q * inner ℝ w ua ≤ Real.pi * q * (r * ‖ua‖) :=
    mul_le_mul_of_nonneg_left ((real_inner_le_norm w ua).trans (mul_le_mul_of_nonneg_right hw hua)) hpq
  have t2 : Real.pi * q * inner ℝ w y ≤ Real.pi * q * (r * ‖y‖) :=
    mul_le_mul_of_nonneg_left ((real_inner_le_norm w y).trans (mul_le_mul_of_nonneg_right hw hy)) hpq
  have h3 : -(2 * inner ℝ (q • ua) y) ≤ M1 * ‖y‖ ^ 2 := (neg_le_abs _).trans hc6
  rw [real_inner_smul_left] at h3
  have t3 : Real.pi * (-(2 * (q * inner ℝ ua y))) ≤ Real.pi * (M1 * ‖y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
  have t4 : 0 ≤ Real.pi * q * ‖w‖ ^ 2 := by positivity
  rw [e1]
  nlinarith [t1, t2, t3, t4]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
  {I : Submodule ℤ (Vsp X.dim)}

theorem ct_cabPoly_zero {ι : Type} [Fintype ι] : cabPoly (0 : EuclideanSpace ℂ ι) 0 = 1 := by
  simp [cabPoly]

theorem ct_beta (hA : PropAStatement) (hS : GSupStatement) (hI : IsSplit P I) (hP : Ext.PackingCount)
    (w : EuclideanSpace ℂ (Fin (Col.gB (IR I)))) (c : ℕ) (hc : c ≤ DF) :
    ∃ βt ∈ (ctY (Col.YB hI hP P.q) w).Sec P.q,
      βt 0 = 1 ∧ (∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j βt 0 = 0) ∧
      (ctY (Col.YB hI hP P.q) w).l2 P.q βt ≤ 6 ∧
      ∀ t, (ctY (Col.YB hI hP P.q) w).ptN2 P.q βt t ≤ 12 * (5.12 : ℝ) ^ Col.gB (IR I) := by
  classical
  have hq2 : (2 : ℝ) ≤ P.q := cab_q_ge P
  have hq2n : 2 ≤ P.q := by exact_mod_cast hq2
  have hR0sq := P.hR0
  have hR0ne : P.R0 ≠ 0 := by intro h; rw [h] at hR0sq; norm_num at hR0sq
  have hR0pos : 0 < |P.R0| := abs_pos.mpr hR0ne
  have hlat : ∀ γ ∈ lat (ctY (Col.YB hI hP P.q) w).b, γ ≠ 0 →
      |P.R0| ≤ Real.sqrt (P.q * Real.pi) * ‖γ‖ := cab_YB_abs hI hP P.q
  have hGle : Col.gB (IR I) ≤ X.gA := cab_gB_le (IR I)
  have hGle' : (Col.gB (IR I) : ℝ) ≤ X.gA := by exact_mod_cast hGle
  have hcD : (c : ℝ) ≤ DF := by exact_mod_cast hc
  have h90 : 90 * ((Fintype.card (Fin (Col.gB (IR I))) : ℝ) + c) ≤ |P.R0| ^ 2 := by
    rw [sq_abs, Fintype.card_fin]; nlinarith [hR0sq.2]
  obtain ⟨β, hβ, hjet, hl2⟩ := hA (Fin (Col.gB (IR I))) (ctY (Col.YB hI hP P.q) w) P.q c |P.R0| P.hq
    (ctY_coc _ _ _ (Col.YB_coc hI hP P.q)) hR0pos hlat
    (by rw [sq_abs]; exact hR0sq.1) h90 (cabPoly 0 0) (by rw [ct_cabPoly_zero]; simp)
  rw [ct_cabPoly_zero] at hjet hl2
  have hJ := cab_J_le (0 : EuclideanSpace ℂ (Fin (Col.gB (IR I)))) (by simp) 0 P.q P.hq
  rw [ct_cabPoly_zero, Fintype.card_fin] at hJ
  have hl2' : (ctY (Col.YB hI hP P.q) w).l2 P.q β ≤
      6 * ((Nat.factorial 0 : ℕ) * (2 / (P.q * Real.pi)) ^ 0 * (2 / P.q) ^ Fintype.card (Fin (Col.gB (IR I)))) := by
    rw [Fintype.card_fin]; simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul] at hJ ⊢
    linarith
  have h90' : 90 * (Fintype.card (Fin (Col.gB (IR I))) : ℝ) ≤ |P.R0| ^ 2 := by
    have : (0 : ℝ) ≤ 90 * c := by positivity
    linarith
  have hβc : ContDiff ℂ (⊤ : ℕ∞) β := (cab_contDiff_top hβ.1).of_le (by exact_mod_cast le_top)
  obtain ⟨hb0, hbj⟩ := ct_jet_one_iter β hβc c hjet
  refine ⟨β, hβ, hb0, hbj, ?_, fun t => ?_⟩
  · refine hl2'.trans ?_
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, Fintype.card_fin]
    have : (2 / (P.q : ℝ)) ^ Col.gB (IR I) ≤ 1 :=
      pow_le_one₀ (by positivity) ((div_le_one (by linarith)).2 hq2)
    linarith
  · have := cab_sup hS (ctY (Col.YB hI hP P.q) w) P.q 0 hq2n |P.R0| hR0pos hlat h90' β hβ hl2' t
    simpa [Fintype.card_fin] using this

def ctA {dim : (E →+* ℂ) → ℕ} (x0 : Vsp dim) (q : ℕ) : Vsp dim := (1 / (q : ℂ)) • x0

def ctC {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (q : ℕ) (a : Vsp dim) : ℂ :=
  cexp ((q * Real.pi / 2 : ℂ) * Col.S (IR I) a - q * Real.pi * Hf a a / 2 +
    q * Real.pi * Hf (Col.wmap (IR I) a) (Col.wmap (IR I) a) / 2)

def ctS (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ)
    (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (a : Vsp X.dim) : (Fin 1 → Vsp X.dim) → ℂ :=
  (ctC I q a)⁻¹ • X.U q (fun _ => a) (Col.colS X I q β)

theorem ct_uc_A (x0 : Vsp X.dim) (q : ℕ) :
    Col.uc (IR I) (ctA x0 q) = (1 / (q : ℝ)) • Col.uc (IR I) x0 := by
  unfold Col.uc Col.z ctA
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Col.Hf_smul_l, smul_smul]
  congr 1
  rw [show (1 / (q : ℂ)) = ((1 / (q : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]

theorem ct_norm_C (hI : IsSplit P I) (q : ℕ) (a : Vsp X.dim) :
    ‖ctC I q a‖ = Real.exp (-(q * Real.pi * ‖Col.uc (IR I) a‖ ^ 2)) := by
  have hK := Col.hK_of hI
  unfold ctC
  rw [Complex.norm_exp]
  congr 1
  have h1 := Col.norm_sq_decomp hK a
  have h2 := Col.norm_wmap hK a
  have h3 := Col.norm_uc_sq (IR I) a
  rw [Col.Hf_self a, Col.Hf_self (Col.wmap (IR I) a), h2, h3]
  have hS : (Col.S (IR I) a).re = ∑ k, ((Col.z (IR I) k a).re ^ 2 - (Col.z (IR I) k a).im ^ 2) := by
    unfold Col.S; rw [Complex.re_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [sq, Complex.mul_re]; ring
  have hn : ∀ k, ‖Col.z (IR I) k a‖ ^ 2 = (Col.z (IR I) k a).re ^ 2 + (Col.z (IR I) k a).im ^ 2 := by
    intro k; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im]
  rw [hS, h1]
  simp only [hn, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  norm_num
  ring

theorem l2_U_eq_l2 {q : ℕ} {F : (Fin 1 → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q 1) (a : Fin 1 → Vsp X.dim) :
    X.l2 q (X.U q a F) = X.l2 q F := by
  unfold PT.l2
  simp_rw [pointwiseNormSq_translate X]
  have hc : Continuous (fun v => X.ptN2 q F v) := by
    have := hF.1.continuous
    unfold PT.ptN2 HC Hf
    fun_prop
  exact TiledBoundaries.stepT E X 1 ℝ (fun v => X.ptN2 q F v) hc (fun γ hγ v => pointwiseNormSq_add_period X hF hγ v) a

theorem ct_fun (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (a : Vsp X.dim) :
    ctS X I q β a = fun w => (ctC I q a)⁻¹ *
      (cexp (q * Real.pi * Hf (w 0) a - q * Real.pi * Hf a a / 2) * Col.sP X I q β (w 0 - a)) := by
  funext w
  simp [ctS, PT.U, HC, Col.colS]

theorem ct_main (hI : IsSplit P I) (σ : E →+* ℂ) (q c : ℕ)
    (βt : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (hβt : Differentiable ℂ βt) (hb0 : βt 0 = 1)
    (hbj : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j βt 0 = 0) (ua : Vsp X.dim)
    (xs : Fin c → Vsp X.dim) (hxs : ∀ k, InPart σ (xs k)) :
    iteratedFDeriv ℂ c (fun v => cexp (-(2 * Real.pi * q : ℂ) * Complex.I * Hf v ua) * Col.F0 I q βt v) 0 xs =
      ∏ k, (-(2 * Real.pi * q : ℂ) * Complex.I * Hf (xs k) ua) := by
  set c0 : ℂ := -(2 * Real.pi * q : ℂ) * Complex.I with hc0
  set ℓL : Vsp X.dim →L[ℂ] ℂ := c0 • innerSL ℂ ua with hℓ
  have hℓv : ∀ v, ℓL v = c0 * Hf v ua := by
    intro v; rw [hℓ, ContinuousLinearMap.smul_apply, innerSL_apply_apply, Col.Hf_eq_inner, smul_eq_mul]
  have hf1 : (fun v => cexp (c0 * Hf v ua) * Col.F0 I q βt v) =
      fun v => cexp (ℓL v) * Col.F0 I q βt v := by funext v; rw [hℓv]
  rw [hf1]
  set W := Col.wmap (IR I) with hW
  have hexpc : ContDiff ℂ (⊤ : ℕ∞) (fun v => cexp (ℓL v)) := ℓL.contDiff.cexp
  have hgc : ContDiff ℂ (⊤ : ℕ∞) (fun v => βt (W v)) :=
    (cab_contDiff_top (hβt.comp W.differentiable)).of_le (by exact_mod_cast le_top)
  have hF0c : ContDiff ℂ (⊤ : ℕ∞) (Col.F0 I q βt) :=
    (cab_contDiff_top (differentiable_zeroModeLift I q βt hβt)).of_le (by exact_mod_cast le_top)
  have hle : ((c : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hr := cab_restrict (cabVP σ) (c := c) (f := fun v => cexp (ℓL v) * Col.F0 I q βt v)
    (g := fun v => cexp (ℓL v) * βt (W v)) ((hexpc.mul hF0c).of_le hle) ((hexpc.mul hgc).of_le hle)
    (fun v hv => by simp only [zeroModeLift_on_part hI q βt σ v hv, hW]) xs hxs
  rw [hr]
  have hj : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j (fun v => βt (W v)) 0 = 0 := by
    intro j hj1 hjc
    have hβj : ContDiff ℂ j βt := contDiff_of_differentiable_fd hβt j
    have := W.iteratedFDeriv_comp_right hβj (0 : Vsp X.dim) le_rfl
    show iteratedFDeriv ℂ j (βt ∘ W) 0 = 0
    rw [this, map_zero, hbj j hj1 hjc]
    ext x; simp
  have hm := ct_iter_mul_jet_one (fun v => cexp (ℓL v)) (fun v => βt (W v)) hexpc hgc c
    (by simp [hb0]) hj
  rw [hm, ct_iter_cexp_apply]
  have h0 : Hf (0 : Vsp X.dim) ua = 0 := by simp [Hf]
  simp [hℓv, h0]

end

end ReciprocityTheory.ChartRestriction.G.I2
end
