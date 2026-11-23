module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle004
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem ratio_bound {m : ℕ} {f : Fin (m + 1) → ℝ} {c u : ℝ} (hf : ∀ i, 0 < f i) (hc : 0 ≤ c)
    (hu : ∀ i, f i ≤ u) (h1 : 1 ≤ c * ∏ i, f i) (i j : Fin (m + 1)) : f i / f j ≤ c * u ^ (m + 1) := by
  rw [Fin.prod_univ_succAbove _ j] at h1
  have h2 : ∏ k, f (j.succAbove k) ≤ u ^ m := by
    calc ∏ k, f (j.succAbove k) ≤ ∏ _k : Fin m, u := Finset.prod_le_prod₀ (fun k _ => (hf _).le) fun k _ => hu _
      _ = u ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hu0 : 0 < u := (hf i).trans_le (hu i)
  have h3 : 1 ≤ c * (f j * u ^ m) :=
    h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (hf j).le) hc)
  rw [div_le_iff₀ (hf j)]
  calc f i ≤ u * 1 := by rw [mul_one]; exact hu i
    _ ≤ u * (c * (f j * u ^ m)) := mul_le_mul_of_nonneg_left h3 hu0.le
    _ = c * u ^ (m + 1) * f j := by ring

private theorem chain_first {m : ℕ} {r : Fin (m + 1) → ℝ} {t s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hst : s ≤ t) (hr : ∀ i, 0 < r i) (h : ∀ i j : Fin (m + 1), (j : ℕ) = i + 1 → t * r j ≤ r i)
    (i : Fin (m + 1)) : s ^ m * r i ≤ r 0 := by
  have h1 := Reduction.pow_mul_le_of_chain (r := fun j => (r j.rev)⁻¹) hs0 hs1 hst (fun j => inv_pos.2 (hr _))
    (fun p q hpq => by
      have h2 := h q.rev p.rev (by have := q.2; simp only [Fin.val_rev]; omega)
      rw [← div_eq_mul_inv, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ (hr _)]
      exact h2) i.rev
  simp only [Fin.rev_last, Fin.rev_rev] at h1
  rw [← div_eq_mul_inv, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ (hr _)] at h1
  exact h1

private theorem le_of_pow_le {x c : ℝ} {d : ℕ} (hd : d ≠ 0) (hc : 1 ≤ c) (h : x ^ d ≤ c) : x ≤ c := by
  rcases le_or_gt x 1 with h1 | h1
  · exact h1.trans hc
  · exact (le_self_pow₀ h1.le hd).trans h

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem qht_le_height (g : KernelIndexFullLattice.G1 E a) (γ : GL (Fin a) E) :
    qht (E := E) (a := a) g.1 ≤ height (AdelicGLn.diagonal E a γ * g.1) := by
  have h1 := ciInf_le (f := fun γ : GL (Fin a) E =>
    height (K := E) (ratGL E a γ * (retractOne g.1 : KernelIndexFullLattice.G1 E a).1))
    ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩ γ
  rw [retractOne_coe] at h1
  unfold qht
  rw [retractOne_coe]
  exact h1

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem prod_bound {ω : Set (AdelicGLn.AdelicGL E a)} (hω : IsCompact ω) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL E a)),
      b * Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) * kk ∈ Reduction.normOneGL (K := E) (n := a) →
      ∏ i, ρ i ≤ c ∧ (∏ i, ρ i)⁻¹ ≤ c := by
  have hdc : Continuous fun g : AdelicGLn.AdelicGL E a => (Reduction.detModule E a g : ℝ) :=
    continuous_subtype_val.comp Reduction.continuous_detModule
  obtain ⟨M₁, hM₁⟩ := hω.bddAbove_image hdc.continuousOn
  obtain ⟨M₂, hM₂⟩ := hω.bddAbove_image (hdc.inv₀ fun g => (Reduction.detModule E a g).2.ne').continuousOn
  refine ⟨max 1 (max M₁ M₂), le_max_left _ _, fun b hb ρ hρ kk hkk hx => ?_⟩
  have hd : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  have h1 := Reduction.mem_normOneGL_iff_detModule.1 hx
  rw [map_mul, map_mul, Reduction.mem_normOneGL_iff_detModule.1 (Reduction.maxCompact_le_normOneGL hkk),
    mul_one] at h1
  have h2 := congrArg Subtype.val h1
  rw [Positive.val_mul, detModule_diagUnits_posIdele, Positive.val_one] at h2
  have h3 := eq_inv_of_mul_eq_one_right h2
  constructor
  · refine le_of_pow_le hd (le_max_left _ _) ?_
    rw [h3]
    exact (hM₂ ⟨b, hb, rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))
  · refine le_of_pow_le hd (le_max_left _ _) ?_
    rw [inv_pow, h3, inv_inv]
    exact (hM₁ ⟨b, hb, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))

end

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.height_bound_of_quasiHeight_le :
    SiegelHt := by
  intro E _ _ _ a
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) a
  rcases a with _ | m
  · refine ⟨ω, 0, 0, hω, hωB, fun g => ?_⟩
    obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
    exact ⟨γ, b, kk, ρ, hρ, hb, hkk, hxe, fun i => i.elim0⟩
  obtain ⟨Ch, hCh0, hCh⟩ := exists_height_le_normOne (K := E) (n := m + 1) hω
  obtain ⟨c, hc, hcb⟩ := prod_bound hω
  have hc0 : 0 < c := one_pos.trans_le hc
  have hs0 : 0 < min t 1 := lt_min ht one_pos
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = (min t 1) ^ m := ⟨_, rfl⟩
  have hσ0 : 0 < σ := hσ ▸ pow_pos hs0 m
  obtain ⟨e, he⟩ : ∃ e, e = Fintype.card (InfinitePlace E) := ⟨_, rfl⟩
  rw [← he] at hCh
  refine ⟨ω, Ch * c ^ (2 * e) * σ⁻¹ ^ (2 * ((m + 1) * e)), (m + 1) * e, hω, hωB, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγx : AdelicGLn.diagonal E (m + 1) γ * g.1 ∈ Reduction.normOneGL (K := E) (n := (m + 1)) :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) g.2
  obtain ⟨hP1, hP2⟩ := hcb b hb ρ hρ kk hkk (hxe ▸ hγx)
  have hP : 0 < ∏ i, ρ i := Finset.prod_pos fun i _ => hρ i
  have key : ∀ v : ℝ, (∀ i j, ρ i / ρ j ≤ c * (σ⁻¹ * v) ^ (m + 1)) →
      qht (E := E) (a := m + 1) g.1 ≤ Ch * c ^ (2 * e) * σ⁻¹ ^ (2 * ((m + 1) * e)) * v ^ (2 * ((m + 1) * e)) := by
    intro v hv
    have h1 : 1 ≤ c * (σ⁻¹ * v) ^ (m + 1) := by
      have := hv 0 0
      rwa [div_self (hρ 0).ne'] at this
    refine (qht_le_height g γ).trans ((hCh b hb ρ hρ kk hkk _ hγx hxe _ h1 hv).trans_eq ?_)
    simp only [mul_pow, ← pow_mul]
    rw [show (m + 1) * (2 * e) = 2 * ((m + 1) * e) by ring]
    ring
  refine ⟨γ, b, kk, ρ, hρ, hb, hkk, hxe, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl : i = Fin.last m := Fin.ext (by simpa using hi)
    have h := key (ρ (Fin.last m))⁻¹ fun p q => by
      have h1 := ratio_bound (f := fun j => (ρ j)⁻¹) (u := σ⁻¹ * (ρ (Fin.last m))⁻¹) (fun j => inv_pos.2 (hρ j)) hc0.le
        (fun j => by
          rw [← mul_inv]
          refine inv_anti₀ (mul_pos hσ0 (hρ _)) ?_
          rw [hσ]
          exact Reduction.pow_mul_le_of_chain hs0.le (min_le_right _ _) (min_le_left _ _) hρ hs j)
        (by rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, one_le_div hP]; exact hP1) q p
      rwa [inv_div_inv] at h1
    rwa [inv_pow (ρ _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos (hρ _) _)] at h
  · obtain rfl : i = 0 := Fin.ext hi
    refine key (ρ 0) fun p q => ratio_bound hρ hc0.le (fun j => ?_) ?_ p q
    · rw [le_inv_mul_iff₀ hσ0, hσ]
      exact chain_first hs0.le (min_le_right _ _) (min_le_left _ _) hρ hs j
    · rwa [inv_le_iff_one_le_mul₀ hP] at hP2
end

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped ContDiff

private theorem der_det {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun r : ℂ => (1 + r • M).det) M.trace 0 := by
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ r : ℂ, (1 + r • M).det = 1 + M.trace * r + p.eval r * r ^ 2 :=
    ⟨_, fun r => Matrix.det_one_add_smul r M⟩
  have h1 := (((hasDerivAt_id (0 : ℂ)).const_mul M.trace).const_add 1).add
    ((p.hasDerivAt 0).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
  rw [funext hp]
  exact HasDerivAt.congr_deriv h1 (by simp)

private theorem der_log {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => Real.log ‖(1 + (t : ℂ) • M).det‖) M.trace.re 0 := by
  have h1 := (der_det M).clog (by simp)
  have h2 : HasDerivAt (fun r : ℂ => Complex.log (1 + r • M).det) M.trace ((0 : ℝ) : ℂ) := by
    simpa using h1
  have h3 := h2.real_of_complex
  simpa only [Complex.log_re] using h3

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem det_ne {y : Matrix (Fin a) (Fin a) (Cinf E)} (hy : IsUnit y) (w : InfinitePlace E) : y.det w ≠ 0 :=
  (((Matrix.isUnit_iff_isUnit_det y).1 hy).map (Pi.evalMonoidHom (fun _ : InfinitePlace E => ℂ) w)).ne_zero

private theorem sm_at {y : Lie E a} (hy : IsUnit (Matrix.of y)) :
    ContDiffAt ℝ ∞ (fun y : Lie E a => sc (Matrix.of y)) y := by
  unfold sc
  refine ((ContDiffAt.sum fun w _ => ?_).div_const _).neg.exp
  have h : ContDiff ℝ ∞ fun x : Lie E a => (Matrix.of x).det w :=
    (contDiff_apply ℝ (fun _ => ℂ) w).comp GlobalTheory.CuspRep.contDiff_det
  exact (h.contDiffAt.norm ℝ (det_ne hy w)).log (norm_ne_zero_iff.2 (det_ne hy w))

private theorem det_line (X : Lie E a) (t : ℝ) (w : InfinitePlace E) :
    (Matrix.of (oneL E a + t • X)).det w = (1 + (t : ℂ) • Matrix.of fun i j => X i j w).det := by
  have h := (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).map_det (Matrix.of (oneL E a + t • X))
  refine h.trans (congrArg _ ?_)
  ext i j
  by_cases hij : i = j <;> simp [oneL, toL, Matrix.one_apply, hij]

private theorem der_sc (X : Lie E a) :
    HasDerivAt (fun t : ℝ => sc (Matrix.of (oneL E a + t • X))) (-ell E a X) 0 := by
  unfold sc
  simp only [det_line]
  have h := ((HasDerivAt.fun_sum (u := Finset.univ) fun (w : InfinitePlace E) _ =>
    der_log (Matrix.of fun i j => X i j w)).div_const ((a : ℝ) * Fintype.card (InfinitePlace E))).neg.exp
  exact HasDerivAt.congr_deriv h (by simp [ell, Matrix.trace])

private theorem sc_mul_star {y : Matrix (Fin a) (Fin a) (Cinf E)} : sc (y * star y) = sc y ^ 2 := by
  unfold sc
  rw [← Real.exp_nat_mul]
  congr 1
  have h : ∀ w, Real.log ‖(y * star y).det w‖ = 2 * Real.log ‖y.det w‖ := fun w => by
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Pi.mul_apply, Pi.star_apply,
      norm_mul, norm_star, ← sq, Real.log_pow]
    norm_num
  simp only [h, ← Finset.mul_sum]
  push_cast
  ring

private theorem sc_one : sc (1 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 := by
  simp [sc]

theorem UpperTheory.deriv_similitudeChar_at_one_eq_trace :
    ScSm := by
  intro E _ _ a
  refine ⟨fun y hy => (sm_at hy).contDiffWithinAt, sc_one, fun X => ?_, fun h => sc_mul_star, fun k => ?_⟩
  · have h1 : IsUnit (Matrix.of (oneL E a)) := isUnit_one
    have hd := ((sm_at h1).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a)
    have h2 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd hl (by simp)
    exact h2.unique (der_sc X)
  · have h : sc k.1 ^ 2 = 1 := by
      rw [← sc_mul_star, Matrix.mem_unitaryGroup_iff.1 k.2, sc_one]
    have hp : 0 < sc k.1 := Real.exp_pos _
    exact (pow_eq_one_iff_of_nonneg hp.le two_ne_zero).1 h
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem quad_eq (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Fin a → Cinf E) :
    quad p x = ∑ w : InfinitePlace E, ∑ j, ∑ i, (x i w * p i j w * star (x j w)).re := by
  simp only [quad, dotProduct, vecMul, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, Complex.re_sum, Finset.sum_mul]

private theorem qf_eq (x : Fin a → Cinf E) :
    qf x = ∑ w : InfinitePlace E, ((x ⬝ᵥ star x) w).re := by
  rw [qf, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dotProduct, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem UpperTheory.geometric_side_quadraticForm_identity :
    QfFacts := by
  intro E _ _ a
  refine ⟨fun x => ?_, fun p p' c x => ⟨?_, ?_⟩, fun h x => ?_, fun c x => ?_, fun p x => ?_, fun x => ⟨?_, ?_⟩⟩
  · rw [qf_eq, quad, vecMul_one]
  · simp only [quad_eq, Matrix.add_apply, Pi.add_apply, mul_add, add_mul, Complex.add_re, Finset.sum_add_distrib]
  · simp only [quad_eq, Matrix.smul_apply, Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, Complex.smul_re, smul_eq_mul]
  · rw [qf_eq, quad, star_vecMul, dotProduct_mulVec, vecMul_vecMul]
    rfl
  · simp only [qf, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  · have hp : ∀ i j w, ‖p i j w‖ ≤ ‖toL p‖ := fun i j w =>
      ((norm_le_pi_norm (toL p i j) w).trans (norm_le_pi_norm (toL p i) j)).trans (norm_le_pi_norm (toL p) i)
    have key : ∀ w j i, |(x i w * p i j w * star (x j w)).re| ≤ ‖toL p‖ / 2 * (‖x i w‖ ^ 2 + ‖x j w‖ ^ 2) := by
      intro w j i
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, norm_star]
      have h1 := hp i j w
      have h2 := norm_nonneg (p i j w)
      have h3 := mul_nonneg (norm_nonneg (x i w)) (norm_nonneg (x j w))
      have h4 := mul_le_mul_of_nonneg_left h1 h3
      have h5 := mul_nonneg (h2.trans h1) (sq_nonneg (‖x i w‖ - ‖x j w‖))
      nlinarith
    rw [quad_eq, qf, Finset.sum_comm (f := fun i w => ‖x i w‖ ^ 2), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    calc _ ≤ ∑ j, ∑ i, ‖toL p‖ / 2 * (‖x i w‖ ^ 2 + ‖x j w‖ ^ 2) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => key w j i))
      _ = _ := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  · have h0 := qf_nonneg x
    have h : ‖x‖ ≤ √(qf x) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => Real.le_sqrt_of_sq_le ?_
      calc ‖x i w‖ ^ 2 ≤ ∑ w, ‖x i w‖ ^ 2 :=
            Finset.single_le_sum (f := fun w => ‖x i w‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w)
        _ ≤ qf x := Finset.single_le_sum (f := fun i => ∑ w, ‖x i w‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖x‖ ^ 2 ≤ √(qf x) ^ 2 := by gcongr
      _ = qf x := Real.sq_sqrt h0
  · calc qf x ≤ ∑ _i : Fin a, ∑ _w : InfinitePlace E, ‖x‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun w _ => ?_
          have := (norm_le_pi_norm (x i) w).trans (norm_le_pi_norm x i)
          gcongr
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
end

section

open UpperTheory.V.Lit.Geo

theorem UpperTheory.geometric_side_lower_bound :
    ThetaLow := by
  classical
  intro A V _ _ _ φ hs v hv
  have ht : 0 < ‖φ v‖ := norm_pos_iff.mpr hv
  set t := ‖φ v‖ with htdef
  have hn : ∀ k : ℕ, ‖φ (k • v)‖ = k * t := by
    intro k
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
  have hinj : Function.Injective (fun k : ℕ => k • v) := by
    intro k l h
    have h1 : (k : ℝ) * t = l * t := by
      rw [← hn k, ← hn l]
      exact congrArg (fun x => ‖φ x‖) h
    exact_mod_cast mul_right_cancel₀ ht.ne' h1
  set n := ⌊1 / t⌋₊ with hndef
  have h1 : 1 / t < n + 1 := Nat.lt_floor_add_one _
  have h2 : (n : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
  have h3 : ∑ x ∈ (Finset.range (n + 1)).image (fun k : ℕ => k • v), Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
      ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
    hs.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun a _ b _ h => hinj h)] at h3
  have h4 : ∑ _k ∈ Finset.range (n + 1), Real.exp (-Real.pi) ≤
      ∑ k ∈ Finset.range (n + 1), Real.exp (-Real.pi * ‖φ (k • v)‖ ^ 2) := by
    refine Finset.sum_le_sum fun k hk => Real.exp_le_exp.mpr ?_
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h5 : (k : ℝ) * t ≤ 1 := by
      have := hk'.trans h2
      rwa [le_div_iff₀ ht] at this
    have h6 : 0 ≤ (k : ℝ) * t := by positivity
    have h7 : ((k : ℝ) * t) ^ 2 ≤ 1 := by nlinarith
    rw [hn]
    nlinarith [Real.pi_pos]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
  push_cast at h4
  have h8 : 1 ≤ t * (n + 1) := by
    rw [div_lt_iff₀ ht] at h1
    linarith
  have h9 := mul_le_mul_of_nonneg_left (h4.trans h3) ht.le
  have h10 := mul_le_mul_of_nonneg_right h8 (Real.exp_pos (-Real.pi)).le
  calc Real.exp (-Real.pi) = 1 * Real.exp (-Real.pi) := (one_mul _).symm
    _ ≤ t * (n + 1) * Real.exp (-Real.pi) := h10
    _ = t * ((n + 1) * Real.exp (-Real.pi)) := by ring
    _ ≤ _ := h9
end

section

open UpperTheory.V.Lit.Geo NumberField Matrix GlobalTheory.CuspRep Topology Filter

theorem UpperTheory.unitaryGroup_lieAlgebra_eq_skewHermitian :
    LatEx := by
  intro E _ _ a U hU
  let O : Set (Af E) := GroundTheory.Global.integralFiniteAdeles (𝓞 E) E
  have hOo : IsOpen O := GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 E) (K := E)
  have hOc : IsCompact O := GroundTheory.Global.isCompact_integralFiniteAdeles E
  let B : Set (Fin a → Af E) := Set.univ.pi fun _ => O
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => hOo
  have hBc : IsCompact B := isCompact_univ_pi fun _ => hOc
  have hB0 : (0 : Fin a → Af E) ∈ B := fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).zero_mem
  let L : AddSubgroup (Fin a → Af E) :=
    { carrier := {x | ∀ u ∈ U, x ᵥ* u.val ∈ B}
      zero_mem' := fun u _ => by rw [Matrix.zero_vecMul]; exact hB0
      add_mem' := fun {x y} hx hy u hu => by
        rw [Matrix.add_vecMul]
        exact fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).add_mem (hx u hu i hi) (hy u hu i hi)
      neg_mem' := fun {x} hx u hu => by
        rw [Matrix.neg_vecMul]
        exact fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).neg_mem (hx u hu i hi) }
  have hc : Continuous fun p : (Fin a → Af E) × GL (Fin a) (Af E) => p.1 ᵥ* p.2.val :=
    continuous_fst.matrix_vecMul (Units.continuous_val.comp continuous_snd)
  have hn : (L : Set (Fin a → Af E)) ∈ 𝓝 0 := by
    refine hU.eventually_forall_of_forall_eventually (x₀ := (0 : Fin a → Af E))
      (P := fun x (u : GL (Fin a) (Af E)) => x ᵥ* u.val ∈ B) fun u _ => ?_
    refine hc.continuousAt.eventually_mem (hBo.mem_nhds ?_)
    simpa only [Matrix.zero_vecMul] using hB0
  have ho : IsOpen (L : Set (Fin a → Af E)) := L.isOpen_of_mem_nhds hn
  refine ⟨L, ⟨ho, hBc.of_isClosed_subset (L.isClosed_of_isOpen ho) fun x hx => ?_⟩, fun u hu x hx v hv => ?_⟩
  · simpa only [Units.val_one, Matrix.vecMul_one] using hx 1 U.one_mem
  · rw [Matrix.vecMul_vecMul]
    exact hx (u * v) (U.mul_mem hu hv)
end

section

open UpperTheory.V.Lit.Geo

theorem UpperTheory.geometric_side_upper_bound :
    ThetaUp := by
  classical
  intro N
  obtain ⟨⟨K, hK, hK1⟩⟩ : Nonempty {K : ℝ // K ^ N * Real.exp (-K) < 1 / (2 * Real.exp Real.pi) ∧ 1 ≤ K} := by
    obtain ⟨K, hK⟩ := (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * Real.exp Real.pi) by positivity))).and
      (Filter.eventually_ge_atTop (1 : ℝ))).exists
    exact ⟨⟨K, hK⟩⟩
  have hK0 : 0 ≤ K := by linarith
  have ha : Real.exp (-Real.pi * (K - 1)) * K ^ N ≤ 1 / 2 := by
    have e1 : Real.exp (-Real.pi * (K - 1)) = Real.exp Real.pi * Real.exp (-(Real.pi * K)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(Real.pi * K)) ≤ Real.exp (-K) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
    have hKN : 0 ≤ K ^ N := by positivity
    calc Real.exp (-Real.pi * (K - 1)) * K ^ N
        = Real.exp Real.pi * (K ^ N * Real.exp (-(Real.pi * K))) := by rw [e1]; ring
      _ ≤ Real.exp Real.pi * (K ^ N * Real.exp (-K)) := by gcongr
      _ ≤ Real.exp Real.pi * (1 / (2 * Real.exp Real.pi)) := by gcongr
      _ = 1 / 2 := by field_simp
  refine ⟨2 * K ^ N, by positivity, ?_⟩
  intro ι q i₀ μ hS hμ hμ1 hgap
  have hKμ : 1 / μ ≤ K / μ := by gcongr
  obtain ⟨hsY, hY⟩ := hS.2 (1 / μ) (K / μ) (by positivity) hKμ
  have hsX : Summable fun i => Real.exp (-Real.pi * (K / μ * q i)) :=
    (hS.2 (K / μ) (K / μ) (by positivity) le_rfl).1
  have hsI : Summable (fun i => if i = i₀ then (1 : ℝ) else 0) := (hasSum_ite_eq i₀ (1 : ℝ)).summable
  have hX2 : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤
      1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i)) := by
    calc ∑' i, Real.exp (-Real.pi * (K / μ * q i))
        ≤ ∑' i, ((if i = i₀ then (1 : ℝ) else 0) +
            Real.exp (-Real.pi * (K - 1)) * Real.exp (-Real.pi * (1 / μ * q i))) := by
          refine Summable.tsum_le_tsum (fun i => ?_) hsX (hsI.add (hsY.mul_left _))
          by_cases h : i = i₀
          · have hq := hS.1 i
            have h0 : -Real.pi * (K / μ * q i) ≤ 0 := by
              have : 0 ≤ K / μ * q i := by positivity
              nlinarith [Real.pi_pos]
            have h1 := Real.exp_le_one_iff.mpr h0
            have h2 : 0 ≤ Real.exp (-Real.pi * (K - 1)) * Real.exp (-Real.pi * (1 / μ * q i)) := by positivity
            rw [if_pos h]
            linarith
          · have hr : 1 ≤ q i / μ := by
              rw [le_div_iff₀ hμ]
              linarith [hgap i h]
            rw [if_neg h, zero_add, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have e3 : K / μ * q i = K * (q i / μ) := by ring
            have e4 : 1 / μ * q i = q i / μ := by ring
            rw [e3, e4]
            nlinarith [mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hr), Real.pi_pos]
      _ = 1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i)) := by
          rw [Summable.tsum_add hsI (hsY.mul_left _), tsum_mul_left]
          congr 1
          exact tsum_ite_eq i₀ (fun _ => (1 : ℝ))
  have eK : K / μ / (1 / μ) = K := by field_simp
  rw [eK] at hY
  have hX0 : 0 ≤ ∑' i, Real.exp (-Real.pi * (K / μ * q i)) := tsum_nonneg fun i => (Real.exp_pos _).le
  have hX : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤ 2 := by
    have ha0 : 0 ≤ Real.exp (-Real.pi * (K - 1)) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left hY ha0
    nlinarith
  have h1K : 1 ≤ K / μ := by
    rw [le_div_iff₀ hμ]
    linarith
  obtain ⟨-, hS1⟩ := hS.2 1 (K / μ) one_pos h1K
  simp only [one_mul, div_one] at hS1
  have hpow : 0 ≤ (K / μ) ^ N := by positivity
  calc ∑' i, Real.exp (-Real.pi * q i) ≤ (K / μ) ^ N * ∑' i, Real.exp (-Real.pi * (K / μ * q i)) := hS1
    _ ≤ (K / μ) ^ N * 2 := by gcongr
    _ = 2 * K ^ N / μ ^ N := by rw [div_pow]; ring
end
