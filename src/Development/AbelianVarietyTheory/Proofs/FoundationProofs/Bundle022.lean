module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Convex
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.Hk

theorem dia_diag_mul_of_dvd_lowerLeft : ∀ (N l q : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 1 0 → ∃ γ' ∈ GlobalTheory.Hk.lev N l, mat σ * dg q 1 * mat γ = mat γ' * (mat σ * dg q 1) := by
  intro N l q σ γ hq hnd hσ hγ hc
  obtain ⟨u, hu⟩ := hc
  have hcop : Nat.Coprime q (N * l) := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  have hcN : IsCoprime (N : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_right_right hcop).symm
  have hcl : IsCoprime (l : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_left_right hcop).symm
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨ha, hd, hcN'⟩ := (Gamma1_mem N γ).1 h1
  have hcl' := Gamma0_mem.1 h0
  have hu' : (γ 1 0 : ℤ) = q * u := hu
  have huN : (u : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcN' ⊢
    rw [hu'] at hcN'
    exact hcN.dvd_of_dvd_mul_left hcN'
  have hul : (u : ZMod l) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcl' ⊢
    rw [hu'] at hcl'
    exact hcl.dvd_of_dvd_mul_left hcl'
  have hs : ((N * l : ℕ) : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ.1
  have hsN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_right _ _) hs)
  have hsl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_left _ _) hs)
  have dσ : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.det_coe; rwa [Matrix.det_fin_two] at this
  have dγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have dσN : ((σ 0 0 : ℤ) : ZMod N) * ((σ 1 1 : ℤ) : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) dσ
    push_cast at this
    rw [hsN] at this
    simpa using this
  refine ⟨⟨!![(σ 0 0 * γ 0 0 + σ 0 1 * u) * σ 1 1 - (σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1) * σ 1 0,
      -(σ 0 0 * γ 0 0 + σ 0 1 * u) * σ 0 1 + (σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1) * σ 0 0;
      (σ 1 0 * γ 0 0 + σ 1 1 * u) * σ 1 1 - (σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1) * σ 1 0,
      -(σ 1 0 * γ 0 0 + σ 1 1 * u) * σ 0 1 + (σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1) * σ 0 0], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    rw [hu'] at dγ
    linear_combination (σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 + 1) * (γ 0 0 * γ 1 1 - γ 0 1 * (q * u)) * dσ + dγ
  · refine Subgroup.mem_inf.2 ⟨(Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩
    · simp [hsN, huN, ha, hd, dσN]
    · simp [hsN, huN, ha, hd, mul_comm, dσN]
    · simp [hsN, huN]
    · simp [hsl, hul]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, dg, Matrix.mul_apply, Fin.sum_univ_two, hu']
    · linear_combination (-(q : ℤ) * (σ 0 0 * γ 0 0 + σ 0 1 * u)) * dσ
    · linear_combination (-(σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1)) * dσ
    · linear_combination (-(q : ℤ) * (σ 1 0 * γ 0 0 + σ 1 1 * u)) * dσ
    · linear_combination (-(σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1)) * dσ

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.Hk

theorem tinv_fin_fin : ∀ (N l q j : ℕ) (γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → j < q → γ ∈ GlobalTheory.Hk.lev N l →
    ¬ (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l,
      !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  intro N l q j γ hq _ _ hγ hA
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0
  obtain ⟨ha1, hd1, hc0⟩ := h1
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  set a := γ 0 0 with ha
  set b := γ 0 1 with hb
  set c := γ 1 0 with hc
  set d := γ 1 1 with hd
  have hmat : mat γ = !![a, b; c, d] := by
    ext i k; fin_cases i <;> fin_cases k <;> rfl
  rw [hmat] at hA ⊢
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at hA
  set A : ℤ := a + j * c with hAdef
  set B : ℤ := b + j * d with hBdef
  have hAq : ((A : ℤ) : ZMod q) ≠ 0 := by
    intro h
    exact hA ((ZMod.intCast_zmod_eq_zero_iff_dvd A q).mp h)
  set j' : ℕ := ((B : ZMod q) * (A : ZMod q)⁻¹).val with hj'
  have hj'lt : j' < q := ZMod.val_lt _
  have hdiv : (q : ℤ) ∣ B - j' * A := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hj', ZMod.natCast_zmod_val]
    field_simp
    ring
  obtain ⟨e, he⟩ := hdiv
  have hdet' : !![A, e; (q : ℤ) * c, d - c * j'].det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + c * he
  let g : SL(2, ℤ) := ⟨!![A, e; (q : ℤ) * c, d - c * j'], hdet'⟩
  refine ⟨j', hj'lt, g, Subgroup.mem_inf.mpr ⟨(Gamma1_mem N g).mpr ⟨?_, ?_, ?_⟩, Gamma0_mem.mpr ?_⟩, ?_⟩
  · show ((a + j * c : ℤ) : ZMod N) = 1
    push_cast; rw [ha1, hc0]; ring
  · show ((d - c * j' : ℤ) : ZMod N) = 1
    push_cast; rw [hd1, hc0]; ring
  · show (((q : ℤ) * c : ℤ) : ZMod N) = 0
    push_cast; rw [hc0]; ring
  · show (((q : ℤ) * c : ℤ) : ZMod l) = 0
    push_cast; rw [h0]; ring
  · show _ = !![A, e; (q : ℤ) * c, d - c * j'] * _
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    have e00 : 1 * a + (j : ℤ) * c = A * 1 + e * 0 := by rw [hAdef]; ring
    have e01 : 1 * b + (j : ℤ) * d = A * j' + e * q := by linear_combination he - hBdef
    have e10 : 0 * a + (q : ℤ) * c = (q : ℤ) * c * 1 + (d - c * j') * 0 := by ring
    have e11 : 0 * b + (q : ℤ) * d = (q : ℤ) * c * j' + (d - c * j') * q := by ring
    rw [e00, e01, e10, e11]

end GlobalTheory.Hk
end

section

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold Real

namespace GlobalTheory.Hk

private theorem im_div_pos' {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) (b : ℕ) :
    0 < ((z + b) / (p : ℂ)).im := by
  have : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

private theorem sum_root' {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ∑ b ∈ Finset.range p, (Complex.exp (2 * π * Complex.I / p) ^ b) ^ m =
      if p ∣ m then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp.ne'
  set ζ := Complex.exp (2 * π * Complex.I / p)
  simp_rw [← pow_mul, fun b => mul_comm b m, pow_mul]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]; simp
  · have h1 : ζ ^ m ≠ 1 := fun e => h ((hζ.pow_eq_one_iff_dvd m).1 e)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one]; simp

theorem hasSum_uOp (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (hq0 : 0 < q)
    (hf : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun m => a (q * m) • Function.Periodic.qParam 1 τ ^ m) (uOp q f τ) := by
  have hp0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hinj : Function.Injective fun m : ℕ => q * m := mul_right_injective₀ hq0.ne'
  have hrange : ∀ n, n ∉ Set.range (fun m : ℕ => q * m) → ¬ q ∣ n :=
    fun n hn ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
  set Q := Function.Periodic.qParam 1 τ with hQ
  set x := Complex.exp (2 * π * Complex.I * τ / q) with hx
  have hxq : x ^ q = Q := by
    rw [hx, ← Complex.exp_nat_mul, hQ, Function.Periodic.qParam]; congr 1; push_cast; field_simp
  have hB : ∀ b : ℕ, HasSum (fun m => a m * x ^ m * (Complex.exp (2 * π * Complex.I / q) ^ b) ^ m)
      (f (ofComplex (((τ : ℂ) + b) / q))) := fun b => by
    have h := hf (ofComplex (((τ : ℂ) + b) / q))
    rw [ofComplex_apply_of_im_pos (im_div_pos' hq0 τ.2 b)] at h ⊢
    convert h using 2 with m
    have e : Function.Periodic.qParam 1 (((τ : ℂ) + b) / q) =
        x * Complex.exp (2 * π * Complex.I / q) ^ b := by
      rw [hx, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    simp [e, mul_pow, mul_assoc]
  have hC := hasSum_sum (s := Finset.range q) fun b _ => hB b
  simp_rw [← Finset.mul_sum, sum_root' hq0] at hC
  rw [← hinj.hasSum_iff fun n hn => by simp [hrange n hn]] at hC
  have hD := hC.mul_left (q : ℂ)⁻¹
  refine cast (congrArg (HasSum · (uOp q f τ)) (funext fun n => ?_)) hD
  simp only [Function.comp, dvd_mul_right, if_true, pow_mul, hxq, smul_eq_mul]
  field_simp

end GlobalTheory.Hk
end
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem vOp_hasSum (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (hq : 0 < q)
    (hf : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun m => (if q ∣ m then a (m / q) else 0) • Function.Periodic.qParam 1 τ ^ m)
      (GlobalTheory.Hk.vOp q f τ) := by
  have him : 0 < ((q : ℂ) * (τ : ℂ)).im := by
    have : ((q : ℂ) * (τ : ℂ)).im = (q : ℝ) * τ.im := by simp
    rw [this]; exact mul_pos (by exact_mod_cast hq) τ.im_pos
  set τ' : ℍ := ofComplex ((q : ℂ) * τ) with hτ'
  have hc : (τ' : ℂ) = (q : ℂ) * τ := by
    rw [hτ', ofComplex_apply_of_im_pos him]
  have hqp : Function.Periodic.qParam 1 (τ' : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ q := by
    simp only [Function.Periodic.qParam, hc, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have h1 := hf τ'
  unfold vOp
  rw [← hτ']
  refine (Function.Injective.hasSum_iff (g := fun m : ℕ => q * m)
    (fun x y h => Nat.eq_of_mul_eq_mul_left hq h) ?_).mp ?_
  · intro x hx
    have : ¬ q ∣ x := by
      rintro ⟨c, rfl⟩; exact hx ⟨c, rfl⟩
    simp [this]
  · convert h1 using 1
    funext m
    simp only [Function.comp, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hq, hqp, ← pow_mul]

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory Filter Topology
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem hasSum_cuspFunction_of_hasSum {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hs : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ))
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    HasSum (fun m => a m • q ^ m) (cuspFunction 1 f q) := by
  have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq1 hq0
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q, h1⟩
  have h2 := Function.Periodic.cuspFunction_eq_of_nonzero 1 (f ∘ ofComplex) hq0
  have h3 : cuspFunction 1 f q = f τ := by
    simpa [cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  have h4 : Function.Periodic.qParam 1 (τ : ℂ) = q :=
    Function.Periodic.qParam_right_inv one_ne_zero hq0
  rw [h3, ← h4]
  exact hs τ

theorem analyticAt_cuspFunction_of_hasSum {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hs : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) :
    AnalyticAt ℂ (cuspFunction 1 f) 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hrad : 1 ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    have hq0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0
    have hq1 : ‖((r : ℝ) : ℂ)‖ < 1 := by
      have : (r : ℝ) < 1 := by exact_mod_cast hr
      simpa using this
    have ht := (hasSum_cuspFunction_of_hasSum hs hq0 hq1).summable.tendsto_atTop_zero.norm
    refine p.le_radius_of_tendsto (l := 0) ?_
    have ht' : Tendsto (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n) atTop (𝓝 0) := by simpa using ht
    convert ht' using 2 with n
    simp [hp, FormalMultilinearSeries.ofScalars_norm]
  have hpos : 0 < p.radius := lt_of_lt_of_le zero_lt_one hrad
  have hP := p.hasFPowerSeriesOnBall hpos
  have hAn : AnalyticAt ℂ p.sum 0 := hP.analyticAt
  have hne : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → cuspFunction 1 f q = p.sum q := by
    intro q hq0 hq1
    rw [hp, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq a q,
      (hasSum_cuspFunction_of_hasSum hs hq0 hq1).tsum_eq]
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
  have hev : ∀ᶠ q in 𝓝[≠] (0 : ℂ), cuspFunction 1 f q = p.sum q := by
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with q hq hq0
    exact hne q hq0 (by simpa using hq)
  have h0 : cuspFunction 1 f 0 = p.sum 0 := by
    have ht : Tendsto (cuspFunction 1 f) (𝓝[≠] 0) (𝓝 (p.sum 0)) :=
      (hAn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun q hq => hq.symm)
    simp only [cuspFunction, Function.Periodic.cuspFunction, Function.update_self]
    refine Tendsto.limUnder_eq ?_
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq0
    simp [cuspFunction, Function.Periodic.cuspFunction, Function.update_of_ne hq0]
  refine hAn.congr ?_
  filter_upwards [hball] with q hq
  rcases eq_or_ne q 0 with rfl | hq0
  · exact h0.symm
  · exact (hne q hq0 (by simpa using hq)).symm

theorem coef_of_hasSum : ∀ (f : ℍ → ℂ) (a : ℕ → ℂ),
    (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) →
      ∀ n, GlobalTheory.Hk.coef f n = a n := by
  intro f a hs n
  have han := analyticAt_cuspFunction_of_hasSum hs
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos han hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction 1 f)
      (FormalMultilinearSeries.ofScalars ℂ fun m => coef f m) 0 := by
    simpa [coef, qExpansion_coeff, div_eq_mul_inv, mul_comm] using han.hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · n) (h2.eq_formalMultilinearSeries h1)

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem one_mem_strictPeriods_lev (N l : ℕ) :
    (1 : ℝ) ∈ ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem]
  · exact AddSubgroup.mem_zmultiples 1
  · refine ⟨?_, ?_⟩
    · show ModularGroup.T ∈ Gamma1 N
      rw [CongruenceSubgroup.Gamma1_mem]
      simp [ModularGroup.T]
    · show ModularGroup.T ∈ Gamma0 l
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [ModularGroup.T]

theorem lev_hasSum_coef : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ (f : ModularForm (lev N l) k) (τ : ℍ),
    HasSum (fun m => coef ⇑f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  intro N l k _ f τ
  have h1 := one_mem_strictPeriods_lev N l
  haveI : Fact (IsCusp OnePoint.infty ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularForm.hasSum_qExpansion f one_pos h1 τ

end GlobalTheory.Hk
end

section

open Matrix GlobalTheory.KZ
open Filter Topology

namespace GlobalTheory.KZ

theorem hs_isOpen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem hs_isPreconnected : IsPreconnected Hs :=
  (convex_halfSpace_im_gt (r := 0)).isPreconnected

theorem mero_eq_zero_of_eventually {a : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a Hs) {τ : ℂ} (hτ : τ ∈ Hs)
    (h : a =ᶠ[𝓝 τ] 0) : (a : Mero) = 0 := by
  have hE := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs_isPreconnected hτ h
  exact Filter.Germ.coe_eq.2 (Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) fun z hz => hE hz)

theorem Tower.an_meromorphicAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K)
    (φ : ℂ → ℂ) (hφ : X.an x = (φ : Mero)) (τ : ℂ) (hτ : τ ∈ Hs) :
    MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := by
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero x
  have ha' : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd hs_isOpen
  have hb' : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd hs_isOpen

  rw [hφ] at hab
  have hrel : ∀ᶠ z in codiscreteWithin Hs, φ z * b z = a z := Filter.Germ.coe_eq.1 hab
  have hrel' : ∀ᶠ z in 𝓝[≠] τ, φ z * b z = a z := by
    have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hrel) τ hτ
    have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (hs_isOpen.mem_nhds hτ)
    filter_upwards [h1, h2] with z hz1 hz2
    rcases hz1 with hz1 | hz1
    · exact hz1
    · exact absurd hz2 hz1

  have hbne : ∀ᶠ z in 𝓝[≠] τ, b z ≠ 0 := by
    rcases (hb' τ hτ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (mero_eq_zero_of_eventually hb' hτ h) hb0
    · exact h
  have heq : (fun z => a z / b z) =ᶠ[𝓝[≠] τ] φ := by
    filter_upwards [hrel', hbne] with z h1 h2
    rw [← h1, mul_div_cancel_right₀ _ h2]
  have hmer : MeromorphicAt φ τ :=
    ((ha' τ hτ).meromorphicAt.div (hb' τ hτ).meromorphicAt).congr heq
  refine ⟨hmer, fun hx htop => ?_⟩
  have hφ0 : ∀ᶠ z in 𝓝[≠] τ, φ z = 0 := meromorphicOrderAt_eq_top_iff.1 htop
  have ha0 : ∀ᶠ z in 𝓝[≠] τ, a z = 0 := by
    filter_upwards [hrel', hφ0] with z h1 h2
    rw [← h1, h2, zero_mul]
  have ha00 : a =ᶠ[𝓝 τ] 0 := by
    rcases (ha' τ hτ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact h
    · exact absurd ((ha0.and h).exists) (by rintro ⟨z, h1, h2⟩; exact h2 h1)
  have hA : (a : Mero) = 0 := mero_eq_zero_of_eventually ha' hτ ha00
  rw [← hφ, hA] at hab
  apply hb0
  have hu : X.an x⁻¹ * X.an x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  calc (b : Mero) = X.an x⁻¹ * X.an x * (b : Mero) := by rw [hu, one_mul]
    _ = X.an x⁻¹ * (X.an x * (b : Mero)) := by rw [mul_assoc]
    _ = 0 := by rw [hab, mul_zero]

end GlobalTheory.KZ
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem Tower.gal_level {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ)
    (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) (hM : 0 < M) (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic M Ω) (Polynomial.degree_cyclotomic_pos M Ω hM).ne'
  rw [Polynomial.isRoot_cyclotomic_iff] at hζ
  have hsζ : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hsζ.pow_eq_one
  intro γ hγ
  have hγ' := hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ'
  obtain ⟨-, h01, h10, -⟩ := hγ'
  have key := X.recip M f hM hf ζ hζ s (i : ℤ) (by rw [zpow_natCast, hi]) γ γ
    ⟨rfl, by simp [en, h01], by simp [en, h10], rfl⟩
  rw [hf γ hγ] at key
  exact key.symm

end GlobalTheory
end
