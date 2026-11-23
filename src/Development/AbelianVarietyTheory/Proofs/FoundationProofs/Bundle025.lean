module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.NumberTheory.ModularForms.Basic
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section
namespace GlobalTheory.SlashUpperTriangularMatrices

theorem toGL_val (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) :
    ((toGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix g := by
  unfold toGL; rw [dite_eq_right h]; rfl

theorem slash_upper (k : ℤ) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toGL !![a, b; 0, d]) τ =
      f (ofComplex (((a : ℂ) * τ + b) / d)) * ((a : ℂ) * d) ^ (k - 1) * (d : ℂ) ^ (-k) := by
  have hdet : (!![a, b; 0, d]).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [ha.ne', hd.ne']
  have hv := toGL_val _ hdet
  set G := toGL !![a, b; 0, d]
  have e00 : G 0 0 = a := by simp [G, hv]
  have e01 : G 0 1 = b := by simp [G, hv]
  have e10 : G 1 0 = 0 := by simp [G, hv]
  have e11 : G 1 1 = d := by simp [G, hv]
  have hG : G.det.val = (a : ℝ) * d := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e00, e01, e10, e11]; ring
  have hpos : 0 < G.det.val := by rw [hG]; positivity
  have hsm : G • τ = ofComplex (((a : ℂ) * τ + b) / d) := by
    rw [← ofComplex_apply (G • τ), coe_smul_of_det_pos hpos]
    simp [num, denom, e00, e01, e10, e11]
  rw [ModularForm.slash_apply, hsm, σ, if_pos hpos, hG]
  have hden : denom G τ = d := by simp [denom, e10, e11]
  rw [hden, abs_of_pos (by positivity)]
  simp

theorem pow_pair (x : ℂ) (hx : x ≠ 0) (k : ℤ) : x ^ (k - 1) * x ^ (-k) = x⁻¹ := by
  rw [← zpow_add₀ hx]; ring_nf; simp

theorem toGL_SL (σ : SL(2, ℤ)) : toGL (mat σ) = (σ : GL (Fin 2) ℝ) := by
  have h : (mat σ).det ≠ 0 := by simp [mat]
  ext i j
  rw [toGL_val _ h]
  simp [mat]

theorem ul_eq (k : ℤ) (l : ℕ) (f : ℍ → ℂ) (hl : 0 < l) : UlF k l f = GlobalTheory.Hk.uOp l f := by
  funext τ
  simp only [UlF, hkF, Finset.sum_apply, ulFam]
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  simp only [fun j : Fin l => slash_upper k 1 (j : ℤ) l one_pos hl' f τ]
  rw [GlobalTheory.Hk.uOp, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => f (ofComplex (((((1 : ℤ)) : ℂ) * τ + ((j : ℤ) : ℂ)) / ((l : ℤ) : ℂ))) *
      (((1 : ℤ) : ℂ) * ((l : ℤ) : ℂ)) ^ (k - 1) * ((l : ℤ) : ℂ) ^ (-k)) l]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : ((l : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  rw [one_mul, one_mul, mul_assoc, pow_pair _ hx, mul_comm]

theorem dd_eq (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : DdF k σ f = GlobalTheory.Hk.dia k σ f := by
  simp [DdF, hkF, GlobalTheory.Hk.dia, toGL_SL, ModularForm.SL_slash]

theorem toGL_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    toGL (g * h) = toGL g * toGL h := by
  have hgh : (g * h).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hg hh
  ext i j
  rw [Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh, RingHom.map_mul]

theorem tq_eq (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) (hq : 0 < q) :
    TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f := by
  have hsplit : TqF k q σ f = UlF k q f + f ∣[k] toGL (mat σ * dg q 1) := by
    have e : ∀ i : Fin q, tqFam q σ i.castSucc = ulFam q i := fun i => by
      rw [tqFam, if_pos (by simp)]; rfl
    have e2 : tqFam q σ (Fin.last q) = mat σ * dg q 1 := by
      rw [tqFam, if_neg (by simp)]
    simp only [TqF, UlF, hkF]
    rw [Fin.sum_univ_castSucc, e2]
    simp only [e]
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hdg : (dg q 1).det ≠ 0 := by simp [dg, Matrix.det_fin_two_of, hq.ne']
  have hσ : (mat σ).det ≠ 0 := by simp [mat]
  rw [hsplit, ul_eq k q f hq, toGL_mul _ _ hσ hdg, SlashAction.slash_mul, toGL_SL, ← ModularForm.SL_slash,
    GlobalTheory.Hk.heckeT]
  funext τ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [dg, slash_upper k q 0 1 hq' one_pos, GlobalTheory.Hk.vOp]
  push_cast
  simp [mul_comm]

theorem dia_iff (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)) : IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ := by
  simp [IsDiam, GlobalTheory.Hk.IsDia, CongruenceSubgroup.Gamma0_mem, mat]

end GlobalTheory.SlashUpperTriangularMatrices

namespace GlobalTheory.SlashUpperTriangularMatrices

theorem bridge : (∀ (k : ℤ) (l : ℕ) (f : ℍ → ℂ), 0 < l → UlF k l f = GlobalTheory.Hk.uOp l f) ∧
  (∀ (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), DdF k σ f = GlobalTheory.Hk.dia k σ f) ∧
  (∀ (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f) ∧
  (∀ (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)), IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ) ∧
  ∀ N l : ℕ, Lev N l = GlobalTheory.Hk.lev N l :=
  ⟨fun k l f hl => ul_eq k l f hl, dd_eq, fun k q σ f hq => tq_eq k q σ f hq, dia_iff, fun _ _ => rfl⟩

end GlobalTheory.SlashUpperTriangularMatrices
end
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerChange

lemma exists_ball (z : ℂ) (hz : 0 < z.im) :
    ∃ (c : ℂ) (r : ℝ), Metric.ball c r ⊆ {u : ℂ | 0 < u.im} ∧ Complex.I ∈ Metric.ball c r ∧
      z ∈ Metric.ball c r := by
  have key : ∀ (u : ℂ) (R : ℝ), 0 < u.im → 0 < R → u.re ^ 2 + u.im ^ 2 < 2 * R * u.im →
      u ∈ Metric.ball ((R : ℂ) * Complex.I) R := by
    intro u R hu hR h
    rw [Metric.mem_ball, Complex.dist_eq, ← sq_lt_sq₀ (norm_nonneg _) hR.le, Complex.sq_norm,
      Complex.normSq_apply]
    simp
    nlinarith
  set a := (z.re ^ 2 + z.im ^ 2) / z.im with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a * z.im = z.re ^ 2 + z.im ^ 2 := by rw [ha]; field_simp
  refine ⟨((a + 1 : ℝ) : ℂ) * Complex.I, a + 1, ?_, key _ _ (by simp) (by linarith) ?_,
    key _ _ hz (by linarith) ?_⟩
  · intro u hu
    rw [Metric.mem_ball, Complex.dist_eq] at hu
    have := (Complex.abs_im_le_norm _).trans_lt hu
    simp at this
    have := (abs_lt.1 this).1
    show 0 < u.im
    linarith
  · simp; linarith
  · nlinarith [mul_nonneg ha0 hz.le]

lemma hasDerivAt_segInt (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (fun τ : ℂ => ∫ t in (0 : ℝ)..1,
      g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I)) (g z) z := by
  obtain ⟨c, r, hB, hI, hzB⟩ := exists_ball z hz
  obtain ⟨G, hG⟩ := (hg.mono hB).isExactOn_ball
  refine ((hG z hzB).sub_const (G Complex.I)).congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hzB] with τ hτ
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, Complex.I + t * (τ - Complex.I) ∈ Metric.ball c r := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    simpa using (convex_ball c r).add_smul_sub_mem hI hτ ht
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => G (Complex.I + s * (τ - Complex.I)))
        (g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℂ => Complex.I + u * (τ - Complex.I)) (τ - Complex.I) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (τ - Complex.I)).const_add Complex.I
    exact (HasDerivAt.comp (t : ℂ) (h₂ := G) (hG _ (hmem t ht)) h1).comp_ofReal
  have hc : ContinuousOn (fun t : ℝ => g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I))
      (Set.uIcc 0 1) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (hg.continuousOn.mono hB).comp (f := fun t : ℝ => Complex.I + t * (τ - Complex.I))
      (by fun_prop) hmem
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

def ecoef (w : ℕ) (h : ℍ → ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (h ∘ ofComplex) (Complex.I + t * (v - Complex.I)) *
    (-(Complex.I + t * (v - Complex.I))) ^ (w - n) * (v - Complex.I)

lemma coeff_eichler (w : ℕ) (h : ℍ → ℂ) (τ : ℍ) (n : ℕ) :
    (eichler w h τ).coeff n = (w.choose n : ℂ) * ecoef w h n τ := by
  unfold eichler ecoef
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using hn)]; simp

lemma hasDerivAt_ecoef (w : ℕ) (h : ℍ → ℂ) (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (n : ℕ) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (ecoef w h n) ((h ∘ ofComplex) z * (-z) ^ (w - n)) z :=
  hasDerivAt_segInt (fun u => (h ∘ ofComplex) u * (-u) ^ (w - n))
    ((UpperHalfPlane.mdifferentiable_iff.1 hh).mul (by fun_prop)) z hz

lemma polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  unfold slP
  rw [LinearMap.sum_apply]
  rfl

lemma polySlash_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (s z u : ℂ)
    (h1 : (g 0 0 : ℂ) - s * g 1 0 = u) (h2 : (g 0 1 : ℂ) - s * g 1 1 = -z * u) :
    slP w g ((X + C (-s)) ^ w) = C (u ^ w) * (X + C (-z)) ^ w := by
  have e : C u * (X + C (-z)) = (C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) +
      C (-s) * (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) := by
    have e1 := congrArg C h1
    have e2 := congrArg C h2
    simp only [map_sub, map_mul, map_neg] at e1 e2 ⊢
    linear_combination (-X) * e1 - e2
  rw [C_pow, ← mul_pow, e, polySlash_apply]
  conv_rhs => rw [add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_X_add_C_pow, smul_eq_C_mul, mul_pow, C_mul, C_pow, map_natCast]
  ring

lemma coe_smul_eq (σ : SL(2, ℤ)) (τ : ℍ) :
    ((σ • τ : ℍ) : ℂ) = ((mat σ 0 0 : ℂ) * τ + mat σ 0 1) / ((mat σ 1 0 : ℂ) * τ + mat σ 1 1) := by
  rw [coe_specialLinearGroup_apply]
  simp

theorem polySlash_eichler_smul (k : ℕ) (hk : 2 ≤ k) (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (σ : SL(2, ℤ)) : ∃ C : ℂ[X], ∀ τ : ℍ,
      slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C := by
  obtain ⟨w, rfl⟩ : ∃ w, k = w + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set h : ℍ → ℂ := f ∣[((w + 2 : ℕ) : ℤ)] σ with hdef
  have hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hdef, ModularForm.SL_slash]
    exact hf.slash _ _
  set a : ℂ := ((mat σ 0 0 : ℤ) : ℂ) with ha
  set b : ℂ := ((mat σ 0 1 : ℤ) : ℂ) with hb
  set c : ℂ := ((mat σ 1 0 : ℤ) : ℂ) with hc
  set d : ℂ := ((mat σ 1 1 : ℤ) : ℂ) with hd
  have hdet : a * d - b * c = 1 := by
    have := σ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc, hd]
    exact_mod_cast this
  refine ⟨slP w (mat σ) (eichler w f (σ • I)) - eichler w h I, fun τ => ?_⟩
  ext n
  set q : ℕ → ℂ := fun i => ((C a * X + C b) ^ i * (C c * X + C d) ^ (w - i)).coeff n with hq
  have hslP : ∀ p : ℂ[X], (slP w (mat σ) p).coeff n = ∑ i ∈ Finset.range (w + 1), p.coeff i * q i := by
    intro p
    rw [polySlash_apply, finsetSum_coeff]
    simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rfl
  set Φ : ℂ → ℂ := fun v => ∑ i ∈ Finset.range (w + 1),
      (w.choose i : ℂ) * ecoef w f i ((a * v + b) / (c * v + d)) * q i -
    (w.choose n : ℂ) * ecoef w h n v with hΦ
  have hΦ1 : ∀ τ : ℍ, Φ τ = (slP w (mat σ) (eichler w f (σ • τ))).coeff n - (eichler w h τ).coeff n := by
    intro τ
    simp only [hΦ, hslP, coeff_eichler, coe_smul_eq]
    rfl
  have hder : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt Φ 0 z := by
    intro z hz
    obtain ⟨τ, rfl⟩ : ∃ τ : ℍ, (τ : ℂ) = z := ⟨⟨z, hz⟩, rfl⟩
    have hj : c * τ + d ≠ 0 := by
      rw [hc, hd, ← ModularGroup.denom_apply]
      exact denom_ne_zero _ _
    have hs : ((σ • τ : ℍ) : ℂ) = (a * τ + b) / (c * τ + d) := coe_smul_eq σ τ
    have hm : HasDerivAt (fun v : ℂ => (a * v + b) / (c * v + d)) ((c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      have h1 : HasDerivAt (fun v : ℂ => a * v + b) a (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
      have h2 : HasDerivAt (fun v : ℂ => c * v + d) c (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
      refine (h1.fun_div h2 hj).congr_deriv ?_
      rw [inv_pow, div_eq_mul_inv]
      linear_combination ((c * τ + d) ^ 2)⁻¹ * hdet
    have hA : ∀ i, HasDerivAt (fun v : ℂ => ecoef w f i ((a * v + b) / (c * v + d)))
        (f (σ • τ) * (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      intro i
      have := hasDerivAt_ecoef w f hf i _ (σ • τ).im_pos
      simp only [Function.comp_apply, ofComplex_apply] at this
      exact HasDerivAt.comp (τ : ℂ) (h₂ := ecoef w f i) (by rw [← hs]; exact this) hm
    have hB := hasDerivAt_ecoef w h hh n _ τ.im_pos
    simp only [Function.comp_apply, ofComplex_apply] at hB
    have hP := congrArg (fun p : ℂ[X] => p.coeff n)
      (polySlash_pow w (mat σ) ((σ • τ : ℍ) : ℂ) τ (c * τ + d)⁻¹
        (by rw [hs, ← ha, ← hc]; rw [div_eq_mul_inv]
            linear_combination (-a) * mul_inv_cancel₀ hj + (c * τ + d)⁻¹ * hdet)
        (by rw [hs, ← hb, ← hd]; rw [div_eq_mul_inv]
            linear_combination (-b) * mul_inv_cancel₀ hj - (c * τ + d)⁻¹ * τ * hdet))
    simp only [hslP, coeff_C_mul, coeff_X_add_C_pow] at hP
    have hv : h τ = f (σ • τ) * (c * τ + d)⁻¹ ^ (w + 2) := by
      rw [hdef, ModularForm.SL_slash_apply, ModularGroup.denom_apply, zpow_neg, zpow_natCast, inv_pow]
    refine ((HasDerivAt.fun_sum (u := Finset.range (w + 1)) fun i _ =>
      ((hA i).const_mul (w.choose i : ℂ)).mul_const (q i)).fun_sub
        (hB.const_mul (w.choose n : ℂ))).congr_deriv ?_
    have : ∑ i ∈ Finset.range (w + 1), (w.choose i : ℂ) *
        (f (σ • τ) * (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (c * τ + d)⁻¹ ^ 2) * q i =
        f (σ • τ) * (c * τ + d)⁻¹ ^ 2 * ∑ i ∈ Finset.range (w + 1),
          (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (w.choose i : ℂ) * q i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hP, hv]
    ring
  have hconst : Φ τ = Φ (I : ℍ) :=
    isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hder z hz).deriv) τ.im_pos (I : ℍ).im_pos
  rw [hΦ1, hΦ1] at hconst
  rw [coeff_add, coeff_sub]
  linear_combination hconst

end GlobalTheory.EichlerChange
end
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerSum

theorem eichler_integrand_intervalIntegrable {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (τ : ℍ) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ k * ((τ : ℂ) - Complex.I)) MeasureTheory.volume 0 1 := by
  have hd := (UpperHalfPlane.mdifferentiable_iff.mp hf).continuousOn
  apply ContinuousOn.intervalIntegrable
  have hmap : Set.MapsTo (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1) {z : ℂ | 0 < z.im} := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨h0, h1⟩ := ht
    have hτ := τ.im_pos
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.I_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.sub_re, Complex.I_re, zero_mul, add_zero]
    rw [UpperHalfPlane.coe_im]
    rcases eq_or_lt_of_le h1 with h | h
    · subst h; nlinarith
    · nlinarith [mul_nonneg h0 hτ.le]
  have hc : ContinuousOn (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1) := by fun_prop
  refine ContinuousOn.mul (ContinuousOn.mul (hd.comp hc hmap) ?_) continuousOn_const
  fun_prop

theorem eichler_finset_sum (w : ℕ) {ι : Type} [Fintype ι] (g : ι → ℍ → ℂ)
    (hg : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) (τ : ℍ) :
    eichler w (∑ i, g i) τ = ∑ i, eichler w (g i) τ := by
  unfold eichler
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [← Finset.sum_mul, ← map_sum, ← Finset.mul_sum,
  ← intervalIntegral.integral_finsetSum fun i _ => eichler_integrand_intervalIntegrable (hg i) τ (w - j)]
  congr 4
  funext t
  simp only [Function.comp_apply, Finset.sum_apply, Finset.sum_mul]

end GlobalTheory.EichlerSum
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]

theorem not_moves_top_iff (v : Valuation L ℝ≥0) (σ : G) :
    ¬ Moves v ⊤ σ ↔ ∃ r : ℝ≥0, r < 1 ∧ ∀ x : L, v x ≤ 1 → v (σ • x - x) ≤ r := by
  unfold Moves
  push_neg
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun x hx => h x (Subfield.mem_top x) hx⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun x _ hx => h x hx⟩

def smallSubgroup (v : Valuation L ℝ≥0) (hv : ∀ (g : G) (x : L), v (g • x) = v x) : Subgroup G where
  carrier := {σ | ¬ Moves v ⊤ σ}
  one_mem' := by
    show ¬ Moves v ⊤ (1 : G)
    rw [not_moves_top_iff]
    exact ⟨0, zero_lt_one, fun x _ => by simp⟩
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_setOf_eq, not_moves_top_iff] at hσ hτ ⊢
    obtain ⟨r, hr, h1⟩ := hσ
    obtain ⟨s, hs, h2⟩ := hτ
    refine ⟨max r s, max_lt hr hs, fun x hx => ?_⟩
    have hτx : v (τ • x) ≤ 1 := by rw [hv]; exact hx
    have e : (σ * τ) • x - x = (σ • (τ • x) - τ • x) + (τ • x - x) := by
      rw [mul_smul]; ring
    rw [e]
    exact (v.map_add _ _).trans (max_le_max (h1 _ hτx) (h2 _ hx))
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_setOf_eq, not_moves_top_iff] at hσ ⊢
    obtain ⟨r, hr, h1⟩ := hσ
    refine ⟨r, hr, fun x hx => ?_⟩
    have hy : v (σ⁻¹ • x) ≤ 1 := by rw [hv]; exact hx
    have e : σ⁻¹ • x - x = -(σ • (σ⁻¹ • x) - σ⁻¹ • x) := by
      rw [smul_inv_smul]; ring
    rw [e, Valuation.map_neg]
    exact h1 _ hy

theorem smallSubgroup_normal (v : Valuation L ℝ≥0) (hv : ∀ (g : G) (x : L), v (g • x) = v x) :
    (smallSubgroup v hv).Normal := by
  constructor
  intro σ hσ g
  change ¬ Moves v ⊤ σ at hσ
  change ¬ Moves v ⊤ (g * σ * g⁻¹)
  rw [not_moves_top_iff] at hσ ⊢
  obtain ⟨r, hr, h1⟩ := hσ
  refine ⟨r, hr, fun x hx => ?_⟩
  have hy : v (g⁻¹ • x) ≤ 1 := by rw [hv]; exact hx
  have e : (g * σ * g⁻¹) • x - x = g • (σ • (g⁻¹ • x) - g⁻¹ • x) := by
    rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  rw [e, hv]
  exact h1 _ hy

theorem exists_normal_not_moves_uniform :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L]
      [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) →
      ∃ N : Subgroup G, N.Normal ∧ (∀ σ : G, σ ∈ N ↔ ¬ Moves v ⊤ σ) ∧
        ∃ i : ℝ≥0, i < 1 ∧ ∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i := by
  intro L _ v G _ _ _ hv
  refine ⟨smallSubgroup v hv, smallSubgroup_normal v hv, fun σ => Iff.rfl, ?_⟩
  have hc : ∀ τ : G, ∃ r : ℝ≥0, r < 1 ∧
      (¬ Moves v ⊤ τ → ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ r) := by
    intro τ
    by_cases h : Moves v ⊤ τ
    · exact ⟨0, zero_lt_one, fun h' => absurd h h'⟩
    · obtain ⟨r, hr, h1⟩ := (not_moves_top_iff v τ).1 h
      exact ⟨r, hr, fun _ => h1⟩
  choose f hf1 hf2 using hc
  letI := Fintype.ofFinite G
  refine ⟨Finset.univ.sup f, ?_, ?_⟩
  · rw [Finset.sup_lt_iff zero_lt_one]
    exact fun τ _ => hf1 τ
  · intro τ hτ x hx
    exact (hf2 τ hτ x hx).trans (Finset.le_sup (f := f) (Finset.mem_univ τ))

end GlobalTheory.AlmostEt
end
