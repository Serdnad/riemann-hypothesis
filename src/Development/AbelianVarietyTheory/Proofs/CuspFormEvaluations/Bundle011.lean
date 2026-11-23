module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.TorsionCoset

variable {E : Type} [Field E] [NumberField E]

theorem eps_zero (X : PT E) : X.eps 0 = 1 := by
  have h := X.eps_add 0 (zero_mem _) 0 (zero_mem _)
  simp only [add_zero] at h
  rcases X.eps_pm 0 (zero_mem _) with h1 | h1
  · exact h1
  · rw [h1] at h
    norm_num [Hf] at h

theorem natCast_smul_mem (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (k : ℕ) :
    (k : ℂ) • x ∈ X.L := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx k

theorem eps_natCast_smul (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (k : ℕ) :
    (X.eps ((k : ℂ) • x) : ℝ) = (X.eps x : ℝ) ^ k := by
  induction k with
  | zero => simp [eps_zero]
  | succ k ih =>
    have h := X.eps_add _ (natCast_smul_mem X hx k) x hx
    have him : (Hf ((k : ℂ) • x) x).im = 0 := by
      unfold Hf
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [PiLp.smul_apply, mul_assoc, Complex.mul_conj]
    rw [show ((k + 1 : ℕ) : ℂ) • x = (k : ℂ) • x + x by push_cast; rw [add_smul, one_smul],
      h, ih, him]
    simp [pow_succ]

theorem isPi_natCast (X : PT E) (n : ℕ) : IsPi X (n ^ 2) ((n : ℂ) • LinearMap.id) := by
  refine ⟨fun α v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    simp [act]
    ring
  · exact natCast_smul_mem X hx n
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    unfold Hf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
    ring
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    have h := eps_natCast_smul X hx n
    have h2 : (X.eps x : ℝ) ^ n = (X.eps x : ℝ) ^ (n ^ 2) := by
      rcases X.eps_pm x hx with h1 | h1
      · simp [h1]
      · rw [h1]
        push_cast
        rw [sq, pow_mul]
        rcases neg_one_pow_eq_or ℝ n with h3 | h3 <;> simp [h3]
    exact_mod_cast h.trans h2

theorem exists_isReps (X : PT E) (n : ℕ) (hn : n ≠ 0) :
    ∃ K, IsReps X (n ^ 2) 1 ((n : ℂ) • LinearMap.id) K := by
  classical
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsq : ∀ x : Vsp X.dim, ((n ^ 2 : ℕ) : ℂ) • x = (n : ℂ) • (n : ℂ) • x := fun x => by
    rw [smul_smul]; push_cast; rw [sq]
  let S : Set (Fin 1 → Vsp X.dim) :=
    {b | (n : ℂ) • (n : ℂ) • b 0 ∈ X.L ∧ (n : ℂ) • b 0 ∈ ZSpan.fundamentalDomain X.b}
  have hS : S.Finite := by
    have hb := ZSpan.setFinite_inter X.b
      ((ZSpan.fundamentalDomain_isBounded X.b).smul₀ (n : ℂ))
    refine Set.Finite.of_injOn (f := fun b => (n : ℂ) • (n : ℂ) • b 0) ?_ ?_ hb
    · intro b hb
      exact ⟨Set.smul_mem_smul_set hb.2, hb.1⟩
    · intro b _ c _ h
      funext k
      rw [Subsingleton.elim k 0]
      exact smul_right_injective _ hn' (smul_right_injective _ hn' h)
  refine ⟨hS.toFinset, fun b hb k => ?_, fun b hb => ?_⟩
  · rw [Subsingleton.elim k 0, hsq]
    exact (hS.mem_toFinset.1 hb).1
  · have hb0 := hb 0
    rw [hsq] at hb0
    have hfl : (n : ℂ) • b 0 - ZSpan.fract X.b ((n : ℂ) • b 0) ∈ X.L := by
      rw [ZSpan.fract_apply, sub_sub_cancel]
      exact (ZSpan.floor X.b _).2
    refine ⟨fun _ => (n : ℂ)⁻¹ • ZSpan.fract X.b ((n : ℂ) • b 0), ⟨hS.mem_toFinset.2 ⟨?_, ?_⟩,
      fun k => ?_⟩, ?_⟩
    · simp only [smul_inv_smul₀ hn']
      have := sub_mem hb0 (natCast_smul_mem X hfl n)
      rwa [smul_sub, sub_sub_cancel] at this
    · simp only [smul_inv_smul₀ hn']
      exact ZSpan.fract_mem_fundamentalDomain X.b _
    · rw [Subsingleton.elim k 0]
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_sub, smul_inv_smul₀ hn'] using hfl
    · rintro c ⟨hc, hc'⟩
      have h1 := (hS.mem_toFinset.1 hc).2
      have h2 := hc' 0
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_sub] at h2
      funext k
      rw [Subsingleton.elim k 0, eq_inv_smul_iff₀ hn', ← (ZSpan.fract_eq_self.2 h1),
        ZSpan.fract_eq_fract, neg_add_eq_sub]
      exact h2

theorem exists_ne_zero_on_coset (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E)
    (s : (Fin 1 → Vsp X.dim) → ℂ) (hs : s ∈ X.Sec 1 1) (h0 : s ≠ 0) (n : ℕ) (hn : 2 ≤ n)
    (a : Vsp X.dim) : ∃ y ∈ X.L, s (fun _ => a + ((n : ℂ)⁻¹) • y) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hn0 : n ≠ 0 := by omega
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hq : 2 ≤ n ^ 2 := by nlinarith
  obtain ⟨K, hK⟩ := exists_isReps X n hn0
  obtain ⟨-, -, -, hspan⟩ :=
    thetaBasis_holds E X (n ^ 2) 1 _ (by omega) (isPi_natCast X n) s hs h0 K hK
  obtain ⟨F, hF, hFv⟩ := GlobalTheory.BasePointFree.exists_sec_ne_zero E X s hs h0 (n ^ 2) hq
    (fun _ => (n : ℂ)⁻¹ • a)
  apply hFv
  have hle : Submodule.span ℂ ((fun b => X.U (n ^ 2) b (s0 X ((n : ℂ) • LinearMap.id) s)) ''
      (K : Set _)) ≤ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ => ℂ)
        (fun _ : Fin 1 => (n : ℂ)⁻¹ • a)) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have h := hcon _ (neg_mem (hK.1 b hb 0))
    have e : a + (n : ℂ)⁻¹ • -(((n ^ 2 : ℕ) : ℂ) • b 0) = (n : ℂ) • ((n : ℂ)⁻¹ • a - b 0) := by
      rw [smul_sub, smul_inv_smul₀ hn', smul_neg, smul_smul, sub_eq_add_neg]
      congr 3
      push_cast
      field_simp
    rw [e] at h
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, PT.U, s0,
      Fin.prod_univ_one, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, h, mul_zero]
  exact hle (hspan hF)

end GlobalTheory.TorsionCoset
end

section

open Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

namespace ThetaBound

section General

variable {ι : Type} [Fintype ι]

theorem l2NormSq_nonneg_gaussianTorus (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : 0 ≤ Y.l2 q F := by
  unfold GT.l2
  rw [MeasureTheory.average_eq]
  refine MeasureTheory.integral_nonneg_of_ae ?_ |> smul_nonneg (by positivity)
  refine Filter.Eventually.of_forall fun v => ?_
  unfold GT.ptN2
  positivity

theorem le_firstMinimum_of_period_lower_bound (Y : GT ι) (hι : Fintype.card ι ≠ 0) {lam : ℝ}
    (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖) : lam ≤ Y.la1 := by
  refine le_csInf ⟨‖Y.b ⟨0, by omega⟩‖, Y.b ⟨0, by omega⟩,
    Submodule.subset_span ⟨_, rfl⟩, Y.b.ne_zero _, rfl⟩ ?_
  rintro t ⟨x, hx, hx0, rfl⟩
  exact hmin x hx hx0

theorem pointwiseNormSq_le_l2_of_firstMinimum (hsup : GSupStatement) (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    (v : EuclideanSpace ℂ ι) :
    Y.ptN2 1 F v ≤ (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
      (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) ^ 2 * Y.l2 1 F := by
  refine (hsup ι Y 1 le_rfl F hF v).trans (mul_le_mul_of_nonneg_right ?_ (l2NormSq_nonneg_gaussianTorus Y 1 F))
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← pow_mul, mul_comm (Fintype.card ι) 2]
  simp only [Nat.cast_one, one_pow, mul_one, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  by_cases hι : Fintype.card ι = 0
  · simp [hι]
  have h1 := le_firstMinimum_of_period_lower_bound Y hι hmin
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : 0 < Y.la1 := hlam.trans_le h1
  gcongr


end General

section Columns

open TensorLat

variable {E : Type} [Field E] [NumberField E]

theorem col_mem_Sec (X : PT E) {q : ℕ} {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1) :
    (fun z => s fun _ => z) ∈ (gtOf X q).Sec q := by
  refine ⟨hs.1.comp (differentiable_pi.2 fun _ => differentiable_id), fun γ hγ v => ?_⟩
  have e : (fun _ : Fin 1 => v + γ) = (fun _ => v) + (fun _ => γ) := by funext j; simp
  simp only [e]
  rw [hs.2 (fun _ => γ) (fun _ => hγ) (fun _ => v)]
  simp [HC, gtOf]

theorem oneColumn_pointwiseNorm_eq_torus (X : PT E) (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) (x : Vsp X.dim) :
    (gtOf X q).ptN2 q (fun z => s fun _ => z) x = X.ptN2 q s fun _ => x := by
  simp [GT.ptN2, PT.ptN2, HC, jof_Hf_self_re]

theorem oneColumn_l2Norm_eq_torus (X : PT E) (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    (gtOf X q).l2 q (fun z => s fun _ => z) = X.l2 q s := by
  rw [l2_norm_fundamental_domain, GT.l2]
  simp only [oneColumn_pointwiseNorm_eq_torus]
  rfl

theorem l2_pos_of_mem_sec_of_ne_zero (X : PT E) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1)
    (hne : s ≠ 0) : 0 < X.l2 q s := by
  refine lt_of_le_of_ne ?_ fun h => hne (eq_zero_of_l2_eq_zero X packingCount hq hs h.symm)
  rw [← oneColumn_l2Norm_eq_torus]
  exact l2NormSq_nonneg_gaussianTorus _ _ _

end Columns

end ThetaBound


open scoped Classical in
open Classical in
theorem theta_value_bound (hsup : GSupStatement) {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (Y : GT ι) (F : EuclideanSpace ℂ ι → ℂ) (hF : F ∈ Y.Sec 1) (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    {κ : Type} (s : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ s, ‖c j‖ ≤ 1) (y : κ → EuclideanSpace ℂ ι)
    (P : MvPolynomial ι ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    ‖∑ j ∈ s, c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
      s.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) / (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) * Real.sqrt (Y.l2 1 F) := by
  set C : ℝ := Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
    (Real.sqrt Real.pi * lam)) ^ Fintype.card ι with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ j ∈ s,
      ‖c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
        (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) * C *
          Real.sqrt (Y.l2 1 F) := by
    intro j hj
    have h := translate_jet_bound U hU 1 le_rfl F hF.1 (C ^ 2 * Y.l2 1 F)
      (ThetaBound.pointwiseNormSq_le_l2_of_firstMinimum hsup Y hF hlam hmin) P a hP (y j)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC0, Nat.cast_one, one_mul] at h
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hc j hj)).trans (h.trans_eq ?_)
    ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ key).trans_eq ?_)
  rw [nsmul_eq_mul]
  ring

end GlobalTheory
end
