module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace UnipotentCoefficientShift

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_zero_of_conj_lt_one {a : E} (ha : IsIntegral ℤ a) (h : ∀ σ : E →+* ℂ, ‖σ a‖ < 1) :
    a = 0 := by
  classical
  by_contra ha0
  have hint : IsIntegral ℤ (Algebra.norm ℚ a) := Algebra.isIntegral_norm ℚ ha
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hN : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha0
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hN
    rw [← hn, map_zero]
  have hne : (Finset.univ : Finset (E →ₐ[ℚ] ℂ)).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, AlgHom.card]
    exact Module.finrank_pos
  have hlt : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ < ∏ _σ : E →ₐ[ℚ] ℂ, (1 : ℝ) :=
    Finset.prod_lt_prod_of_nonempty₀
      (fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr ha0))
      (fun σ _ => h (σ : E →+* ℂ)) hne
  rw [Finset.prod_const_one, ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ a, ← hn] at hlt
  have h1 : ‖((n : ℚ) : ℂ)‖ < 1 := by simpa using hlt
  have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn0
  have h3 : ‖((n : ℚ) : ℂ)‖ = |(n : ℝ)| := by
    rw [Rat.cast_intCast, Complex.norm_intCast]
  linarith

variable {r : ℕ} {X : Data E r}

theorem Hf_add_left (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ (u + v) w = X.Hf z τ u w + X.Hf z τ v w := by
  simp only [Data.Hf, Data.ppos_add, smul_add, hermC_sub_left, hermC_add_left, hermC_smul_left]
  ring

theorem Hf_sub_left (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ (u - v) w = X.Hf z τ u w - X.Hf z τ v w := by
  simp only [Data.Hf, Data.ppos_sub, smul_sub, hermC_sub_left, hermC_smul_left]
  ring

private lemma ppos_smul' (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u : Fin r → ℂ) :
    X.ppos z τ (k • u) = k • X.ppos z τ u := by
  simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]

theorem Hf_smul_left (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf z τ (k • u) w = k * X.Hf z τ u w := by
  simp only [Data.Hf, ppos_smul', smul_comm (2 : ℂ) k, hermC_sub_left, hermC_smul_left]
  ring

theorem Hf_add_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ u (v + w) = X.Hf z τ u v + X.Hf z τ u w := by
  simp only [Data.Hf, hermC_add_right]

theorem Hf_smul_right (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf z τ u (k • w) = conj k * X.Hf z τ u w := by
  simp only [Data.Hf, hermC_smul_right]

theorem Hf_conj {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf z τ u w) = X.Hf z τ w u := by
  have key : hermC τ.1 X.Gm w (X.ppos z τ u) = hermC τ.1 X.Gm (X.ppos z τ w) u := by
    rw [← hermC_conj τ.1 X.Gm_herm (X.ppos z τ u) w, X.hermC_ppos_left hz τ u w,
      hermC_conj τ.1 X.Gm_herm, X.hermC_ppos_left hz τ w u]
  simp only [Data.Hf]
  rw [hermC_conj τ.1 X.Gm_herm, hermC_sub_right, hermC_smul_right, hermC_sub_left, hermC_smul_left,
    key, map_ofNat]

private lemma maj_nonneg_of_mem_dom {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj z τ v := by
  rcases eq_or_ne v 0 with h | h
  · subst h
    simp [Data.maj, Data.posPart, hermC]
  · exact (X.maj_pos hz τ h).le

theorem norm_hermC_le_maj {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v v‖ ≤ X.maj z τ v := by
  have hv : v = X.ppos z τ v + (v - X.ppos z τ v) := by abel
  have hPq : X.ppos z τ (v - X.ppos z τ v) = 0 := by
    rw [Data.ppos_sub, X.ppos_ppos hz, sub_self]
  have hpq : hermC τ.1 X.Gm (X.ppos z τ v) (v - X.ppos z τ v) = 0 := by
    rw [hermC_sub_right, X.hermC_ppos_left hz τ v v, sub_self]
  have hqp : hermC τ.1 X.Gm (v - X.ppos z τ v) (X.ppos z τ v) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm (X.ppos z τ v) (v - X.ppos z τ v), hpq, map_zero]
  have hA : X.Hf z τ (X.ppos z τ v) (X.ppos z τ v) = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) := by
    rw [Data.Hf, X.ppos_ppos hz, two_smul, add_sub_cancel_right]
  have hB : X.Hf z τ (v - X.ppos z τ v) (v - X.ppos z τ v) =
      -hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    rw [Data.Hf, hPq, smul_zero, hermC_sub_left, hermC_zero_left, zero_sub]
  have hV : X.Hf z τ v v = 2 * hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) - hermC τ.1 X.Gm v v := by
    rw [Data.Hf, hermC_sub_left, hermC_smul_left, X.hermC_ppos_left hz τ v v]
  have hvv : hermC τ.1 X.Gm v v = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) +
      hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    conv_lhs => rw [hv]
    rw [hermC_add_left, hermC_add_right, hermC_add_right, hpq, hqp]
    ring
  have eA : hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) = (X.maj z τ (X.ppos z τ v) : ℂ) := by
    rw [← hA]; exact X.Hf_self hz τ _
  have eB : hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) = -(X.maj z τ (v - X.ppos z τ v) : ℂ) := by
    rw [← X.Hf_self hz τ, hB, neg_neg]
  have eC : ((X.maj z τ v : ℝ) : ℂ) = ((X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [← X.Hf_self hz τ, hV, hvv, eA, eB]
    push_cast
    ring
  have eC' : X.maj z τ v = X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) := by
    exact_mod_cast eC
  have ha := maj_nonneg_of_mem_dom hz τ (X.ppos z τ v)
  have hb := maj_nonneg_of_mem_dom hz τ (v - X.ppos z τ v)
  have e : hermC τ.1 X.Gm v v = ((X.maj z τ (X.ppos z τ v) - X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [hvv, eA, eB]
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, eC']
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem maj_smul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj z τ ((k : ℂ) • v) = k ^ 2 * X.maj z τ v := by
  have hS : (∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le b)))) =
      ((k ^ 2 : ℝ) : ℂ) * ∑ a : Fin X.p0, ∑ b : Fin X.p0,
        hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
          conj (hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b))) := by
    simp only [hermC_smul_left, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have hh : hermC τ.1 X.Gm ((k : ℂ) • v) ((k : ℂ) • v) = ((k ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_left, hermC_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  simp only [Data.maj, Data.posPart]
  rw [hS, hh, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem coef_shift (z : Frame X.Ψ r) (τ : X.Ψ) (u e : Fin r → ℂ) (c : ℂ) (he : X.Hf z τ e e ≠ 0) :
    X.Hf z τ (u + c • e) e / X.Hf z τ e e = X.Hf z τ u e / X.Hf z τ e e + c := by
  rw [Hf_add_left, Hf_smul_left, add_div, mul_div_assoc, div_self he, mul_one]

theorem ucomp_shift (z : Frame X.Ψ r) (τ : X.Ψ) (u e : Fin r → ℂ) (c : ℂ) (he : X.Hf z τ e e ≠ 0) :
    (u + c • e) - (X.Hf z τ (u + c • e) e / X.Hf z τ e e) • e =
      u - (X.Hf z τ u e / X.Hf z τ e e) • e := by
  rw [coef_shift z τ u e c he, add_smul]
  abel

theorem maj_decomp {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v e : Fin r → ℂ)
    (he : X.Hf z τ e e ≠ 0) :
    X.maj z τ v = X.maj z τ (v - (X.Hf z τ v e / X.Hf z τ e e) • e) +
      ‖X.Hf z τ v e / X.Hf z τ e e‖ ^ 2 * X.maj z τ e := by
  set K := X.Hf z τ v e / X.Hf z τ e e with hKdef
  have hK : K * X.Hf z τ e e = X.Hf z τ v e := div_mul_cancel₀ _ he
  have h1 : X.Hf z τ (v - K • e) e = 0 := by
    rw [Hf_sub_left, Hf_smul_left, hK, sub_self]
  have h2 : X.Hf z τ e (v - K • e) = 0 := by
    rw [← Hf_conj hz τ (v - K • e) e, h1, map_zero]
  have hv : v = (v - K • e) + K • e := (sub_add_cancel v (K • e)).symm
  have hexp : X.Hf z τ v v = X.Hf z τ (v - K • e) (v - K • e) + K * conj K * X.Hf z τ e e := by
    conv_lhs => rw [hv]
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_smul_left, Hf_smul_left, Hf_smul_right,
      Hf_smul_right, h1, h2]
    ring
  rw [X.Hf_self hz, X.Hf_self hz, X.Hf_self hz, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hexp
  exact_mod_cast hexp

end UnipotentCoefficientShift

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

lemma ppos_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.ppos x τ (c • v) = c • X.ppos x τ v := by
  simp only [ppos, hC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma ppos_zero (x : Frame X.Ψ r) (τ : X.Ψ) : X.ppos x τ 0 = 0 := by
  have := ppos_smul X x τ 0 0
  simpa using this

lemma ppos_selfadj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hA := gramPos_det_ne X hx τ
  have hsymm : ∀ v v', hermC τ.1 X.Gm v v' = conj (hermC τ.1 X.Gm v' v) := fun v v' =>
    hC_symm τ.1 X.Gm X.Gm_herm v' v

  have hspan : ∀ (y v : Fin r → ℂ), (∀ b : Fin X.p0, hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) →
      hermC τ.1 X.Gm (X.ppos x τ v) y = 0 := by
    intro y v hy
    unfold ppos
    rw [hC_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hC_smul_left, hsymm, hy a, map_zero, mul_zero]
  have h1 : hermC τ.1 X.Gm (X.ppos x τ u) (w - X.ppos x τ w) = 0 :=
    hspan (w - X.ppos x τ w) u (ppos_orth X x τ hA w)
  have h2 : hermC τ.1 X.Gm (u - X.ppos x τ u) (X.ppos x τ w) = 0 :=
    hspan (u - X.ppos x τ u) w (ppos_orth X x τ hA u) |> fun h => by rw [hsymm, h, map_zero]
  have e1 : hermC τ.1 X.Gm (X.ppos x τ u) w =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : w = X.ppos x τ w + (w - X.ppos x τ w) := by abel
    conv_lhs => rw [this]
    rw [hC_add_right, h1, add_zero]
  have e2 : hermC τ.1 X.Gm u (X.ppos x τ w) =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : u = X.ppos x τ u + (u - X.ppos x τ u) := by abel
    conv_lhs => rw [this]
    rw [hC_add_left, h2, add_zero]
  rw [e1, e2]

lemma Hf_eq (x : Frame X.Ψ r) (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ u w = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
  have hneg : hermC τ.1 X.Gm u (-w) = - hermC τ.1 X.Gm u w := by
    have := hC_smul_right τ.1 X.Gm (-1) u w
    simpa using this
  calc X.Hf x τ u w = 2 * hermC τ.1 X.Gm u (X.ppos x τ w) - hermC τ.1 X.Gm u w := by
        simp only [Hf]; rw [hC_sub_left, hC_smul_left, ppos_selfadj X hx]
    _ = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
        rw [sub_eq_add_neg ((2 : ℂ) • X.ppos x τ w) w, hC_add_right, hC_smul_right, hneg, map_ofNat]
        ring

section unitary

variable (x : Frame X.Ψ r) (τ : X.Ψ) (g : Matrix (Fin r) (Fin r) ℂ)
  (hg : ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g w) = hermC τ.1 X.Gm u w)

include hg

lemma gram_unitary : gram τ.1 X.Gm (g * mat x τ) = gram τ.1 X.Gm (mat x τ) := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]

lemma ppos_unitary (hx : x ∈ X.dom) (v : Fin r → ℂ) :
    X.ppos (X.lmulC (fun _ => g) x) τ (Matrix.mulVec g v) = Matrix.mulVec g (X.ppos x τ v) := by
  have hcol : ∀ a, col (mat (X.lmulC (fun _ => g) x) τ) a = Matrix.mulVec g (col (mat x τ) a) := by
    intro a; exact col_mul g (mat x τ) a
  have hgram : X.gramPos (X.lmulC (fun _ => g) x) τ = X.gramPos x τ := by
    simp only [gramPos]
    rw [show mat (X.lmulC (fun _ => g) x) τ = g * mat x τ from rfl, gram_unitary X x τ g hg]
  set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a
  have hpx : X.ppos x τ v = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a) := rfl
  have hsum : Matrix.mulVec g (X.ppos x τ v) =
      ∑ a, α a • col (mat (X.lmulC (fun _ => g) x) τ) (Fin.castLE X.p0_le a) := by
    rw [hpx, mulVec_lin]; simp only [hcol]
  rw [hsum]
  apply ppos_eq_of X _ τ (by rw [hgram]; exact gramPos_det_ne X hx τ)
  intro b
  rw [← hsum, hcol, ← Matrix.mulVec_sub, hg]
  exact ppos_orth X x τ (gramPos_det_ne X hx τ) v b

end unitary

theorem unitaryComplementMove_of_isotropic : UnitaryComplementMove (E := E) := by
  intro r X ξ hξ x hx h1 hu hfix _hU
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0 := fun τ => by
    rw [← emb_herm, hξ.2.1, map_zero]
  set x' := X.lmulC h1 x with hx'
  have hloc : ∀ τ : X.Ψ, X.lmulC h1 x = X.lmulC (fun _ => h1 τ) x ∨ True := fun _ => Or.inr trivial

  have hmat : ∀ τ, mat x' τ = h1 τ * mat x τ := fun τ => rfl
  have hgramτ : ∀ τ, gram τ.1 X.Gm (mat x' τ) = gram τ.1 X.Gm (mat x τ) := fun τ => by
    rw [hmat]; exact gram_unitary X x τ (h1 τ) (hu τ)

  have hfe : ∀ τ, Matrix.mulVec (h1 τ) (emb τ.1 ξ) = emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 1) (fun _ => 0)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, one_smul, zero_smul, ppos_zero, smul_zero,
      sub_zero, add_zero] at h
    exact h
  have hfJ : ∀ τ, Matrix.mulVec (h1 τ) ((2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ) =
      (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 0) (fun _ => -I)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, zero_smul, zero_add, ppos_smul, smul_smul] at h
    have e1 : I • (((2 : ℂ) * -I) • X.ppos x τ (emb τ.1 ξ) - -I • emb τ.1 ξ) =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      rw [smul_sub, smul_smul, smul_smul, show I * (2 * -I) = (2 : ℂ) by
        linear_combination (-2 : ℂ) * Complex.I_mul_I, show I * -I = (1 : ℂ) by
        linear_combination (-1 : ℂ) * Complex.I_mul_I, one_smul]
    rw [e1] at h
    exact h

  have hdom : x' ∈ X.dom := by
    intro τ
    refine ⟨?_, fun i => ?_⟩
    · rw [hmat, Matrix.det_mul]
      refine mul_ne_zero ?_ (hx τ).1
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0

      have hrad : ∀ w, hermC τ.1 X.Gm v w = 0 := fun w => by rw [← hu τ v w, hv]; simp [hermC]
      have hG : (Matrix.map X.Gm τ.1).det ≠ 0 := by
        have h := RingHom.map_det τ.1 X.Gm
        rw [show τ.1.mapMatrix X.Gm = X.Gm.map τ.1 from rfl] at h
        rw [← h]; exact (map_ne_zero _).mpr X.Gm_det
      by_contra hne
      apply hG
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨v, hne, ?_⟩
      funext b
      have := hrad (Pi.single b 1)
      simpa [hermC, Matrix.vecMul, dotProduct, Pi.single_apply, Matrix.map_apply] using this
    · have : dmin X.Gm x' τ i = dmin X.Gm x τ i := by
        simp only [dmin]; rw [hgramτ]
      rw [this]; exact (hx τ).2 i
  refine ⟨hdom, ?_, ?_, ?_⟩
  ·
    intro u _
    funext τ
    have hJe : (2 : ℂ) • X.ppos x' τ (emb τ.1 ξ) - emb τ.1 ξ =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (emb τ.1 ξ)
      rw [hfe τ] at hp
      rw [show X.ppos x' τ (emb τ.1 ξ) = X.ppos (X.lmulC (fun _ => h1 τ) x) τ (emb τ.1 ξ) from rfl, hp]
      rw [← Matrix.mulVec_smul, ← hfe τ, ← Matrix.mulVec_sub, hfe τ, hfJ τ]
    simp only [aproj, lineV]
    rw [Hf_eq X x' hdom, Hf_eq X x' hdom, Hf_eq X x hx, Hf_eq X x hx, hJe]
  · intro τ

    have hpp : X.posPart x' τ (emb τ.1 ξ) = X.posPart x τ (emb τ.1 ξ) := by
      have hgp : X.gramPos x' τ = X.gramPos x τ := by simp only [gramPos]; rw [hgramτ]
      simp only [posPart]
      rw [hgp]
      have hc : ∀ a : Fin X.p0, hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x' τ) (Fin.castLE X.p0_le a)) =
          hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x τ) (Fin.castLE X.p0_le a)) := by
        intro a
        rw [hmat, col_mul]
        conv_lhs => rw [← hfe τ]
        rw [hu τ]
      simp only [hc]
    simp only [maj, hpp]
  · intro u _
    funext τ
    simp only [Jz, applyV]
    have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (u τ)
    rw [show X.ppos x' τ (Matrix.mulVec (h1 τ) (u τ)) =
      X.ppos (X.lmulC (fun _ => h1 τ) x) τ (Matrix.mulVec (h1 τ) (u τ)) from rfl, hp]
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul]

end Data

theorem unitaryComplementMove : UnitaryComplementMove (E := E) := Data.unitaryComplementMove_of_isotropic

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma span_le_of_upper (p : ℕ) (hp : p ≤ r) (M N : Matrix (Fin r) (Fin r) ℂ) (hN : N.BlockTriangular id) :
    Submodule.span ℂ (Set.range fun a : Fin p => col (M * N) (Fin.castLE hp a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a)) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hcol : col (M * N) (Fin.castLE hp a) = ∑ j : Fin r, N j (Fin.castLE hp a) • col M j := by
    funext i
    simp only [col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  show col (M * N) (Fin.castLE hp a) ∈ Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a))
  rw [hcol]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : (j : ℕ) < p
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, congrArg (col M) (Fin.ext rfl)⟩)
  · have hlt : Fin.castLE hp a < j := Fin.lt_iff_val_lt_val.mpr (by show (a : ℕ) < j; omega)
    have h0 : N j (Fin.castLE hp a) = 0 := hN hlt
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

variable (X : Data E r)

lemma sameFlag_rmul (z : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : X.SameFlag z (rmul z b) := by
  unfold Data.SameFlag
  unfold Bor at hb
  rw [Set.mem_setOf_eq] at hb
  intro τ
  obtain ⟨hdet, htri⟩ := hb τ
  have hmul : mat (rmul z b) τ = mat z τ * mat b τ := by
    first
    | rfl
    | (unfold rmul mat; rfl)
    | (ext i j; simp [rmul, mat, Matrix.mul_apply])
  have hT : (mat b τ).BlockTriangular id := fun a c h => by
    first
    | exact htri a c h
    | (simp only [mat]; exact htri a c h)
  haveI : Invertible (mat b τ).det := invertibleOfNonzero hdet
  haveI : Invertible (mat b τ) := Matrix.invertibleOfDetInvertible _
  apply le_antisymm
  · have hinv : mat z τ = mat (rmul z b) τ * (mat b τ)⁻¹ := by
      rw [hmul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]
    rw [hinv]
    exact span_le_of_upper _ _ _ _ (Matrix.blockTriangular_inv_of_blockTriangular hT)
  · rw [hmul]
    exact span_le_of_upper _ _ _ _ hT

lemma maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · subst hv
    simp [Data.maj, Data.posPart, hermC]
  · exact (X.maj_pos hx τ hv).le

end

end ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

end ReciprocityTheory.ChartRestriction.G.FD
end
