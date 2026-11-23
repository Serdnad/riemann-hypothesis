module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramDeterminantReal
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Herm

variable {n : ℕ} (G : Matrix (Fin r) (Fin r) E)

def hermLin (y : Fin r → E) : (Fin r → E) →ₗ[E] E where
  toFun x := herm G x y
  map_add' x x' := by simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

lemma herm_sum_smul (c : Fin n → E) (β : Fin n → Fin r → E) (y : Fin r → E) :
    herm G (∑ k, c k • β k) y = ∑ k, c k * herm G (β k) y := by
  have h := map_sum (hermLin G y) (fun k => c k • β k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

lemma herm_add_smul (x ξ y : Fin r → E) (e : E) : herm G (x + e • ξ) y = herm G x y + e * herm G ξ y := by
  have h := map_add (hermLin G y) x (e • ξ)
  rw [map_smul, smul_eq_mul] at h
  exact h

variable {G} (hG : ∀ a b, cc (G a b) = G b a) {ξ : Fin r → E} {β : Fin n → Fin r → E}
  (hβ : ∀ k, herm G (β k) ξ = 0) (hξξ : herm G ξ ξ = 0)

include hβ in
lemma herm_B_ξ (c : Fin n → E) : herm G (∑ k, c k • β k) ξ = 0 := by
  rw [herm_sum_smul]
  simp [hβ]

include hβ hξξ in
lemma herm_lam_ξ (c : Fin n → E) (e : E) : herm G (∑ k, c k • β k + e • ξ) ξ = 0 := by
  rw [herm_add_smul, herm_B_ξ hβ, hξξ]
  ring

include hG hβ hξξ in
lemma herm_lam_lam (c c' : Fin n → E) (e e' : E) :
    herm G (∑ k, c k • β k + e • ξ) (∑ k, c' k • β k + e' • ξ) =
      herm G (∑ k, c k • β k) (∑ k, c' k • β k) := by
  have hadd : ∀ x y y' : Fin r → E, herm G x (y + y') = herm G x y + herm G x y' := by
    intro x y y'
    simp only [herm, Pi.add_apply, cc, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have hsm : ∀ (x y : Fin r → E) (a : E), herm G x (a • y) = cc a * herm G x y := by
    intro x y a
    simp only [herm, Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hswap : ∀ x y : Fin r → E, herm G y x = cc (herm G x y) := by
    intro x y
    have hmap : ∀ s : Finset (Fin r), ∀ f : Fin r → E, cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) :=
      fun s f => by simp only [cc, map_sum]
    have hmul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by simp only [cc, map_mul]
    simp only [herm, hmap, hmul, cc_cc, hG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hξβ : ∀ k, herm G ξ (β k) = 0 := fun k => by
    rw [hswap, hβ k]
    simp only [cc, map_zero]
  have hξB : herm G ξ (∑ k, c' k • β k) = 0 := by
    have hs : ∀ (s : Finset (Fin n)), herm G ξ (∑ k ∈ s, c' k • β k) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty, herm, Pi.zero_apply, cc, map_zero, mul_zero, Finset.sum_const_zero]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, hadd, hsm, hξβ, ih]
        ring
    exact hs _
  rw [herm_add_smul, hadd, hadd, hsm, hsm, herm_B_ξ hβ, hξξ, hξB]
  ring

lemma ne_smul_ξ (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    {c : Fin n → E} (hc : c ≠ 0) (e e' : E) : ∑ k, c k • β k + e • ξ ≠ e' • ξ := by
  intro h
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (Fin.cons (e - e') c) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, sub_smul]
    rw [← sub_eq_zero] at h
    rw [← h]
    abel)
  exact hc (funext fun k => by simpa using h0 k.succ)

lemma cons_li (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    {la : Fin n → Fin n → E} (hla : LinearIndependent E la) (e : Fin n → E) :
    LinearIndependent E (Fin.cons ξ (fun j => ∑ k, la j k • β k + e j • ξ) :
      Fin (n + 1) → Fin r → E) := by
  rw [Fintype.linearIndependent_iff] at hli hla ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have key := hli (Fin.cons (g 0 + ∑ j, g j.succ * e j) (fun k => ∑ j, g j.succ * la j k)) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hg]
    simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_smul,
      Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun x y => (g y.succ * la y x) • β x)]
    abel)
  have hs : ∀ j : Fin n, g j.succ = 0 := by
    refine hla (fun j => g j.succ) ?_
    funext k
    have := key k.succ
    simp only [Fin.cons_succ] at this
    simpa [Finset.sum_apply, smul_eq_mul] using this
  have h0 : g 0 = 0 := by
    have := key 0
    simpa [hs] using this
  intro i
  refine Fin.cases h0 (fun j => hs j) i

end Herm

lemma hC_comb2_ortho (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n p : ℕ} (f : Fin n → Fin r → ℂ)
    (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (b c : Fin n → ℂ) :
    hermC τ G (∑ k, b k • f k) (∑ l, c l • f l) = ReciprocityTheory.MultiplicativeHeights.jForm p c b := by
  have h1 : ∀ (w : Fin n → ℂ) (v : Fin r → ℂ),
      hermC τ G (∑ k, w k • f k) v = ∑ k, w k * hermC τ G (f k) v := by
    intro w v
    simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 : ∀ (w : Fin n → ℂ) (u : Fin r → ℂ),
      hermC τ G u (∑ l, w l • f l) = ∑ l, conj (w l) * hermC τ G u (f l) := by
    intro w u

    simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h1]
  simp_rw [h2, hf, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.sgn
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma comb_swap {m n : ℕ} (w : Fin n → ℂ) (y : Fin n → Fin m → ℂ) (f : Fin m → Fin r → ℂ) :
    ∑ j, w j • ∑ k, y j k • f k = ∑ k, (∑ j, w j * y j k) • f k := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

lemma qcomb {m n : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (w : Fin n → ℂ) (a : Fin n → Fin m → ℂ)
    (k : Fin m) : (Q *ᵥ ∑ j, w j • a j) k = ∑ j, w j * (Q *ᵥ a j) k := by
  have h := map_sum (Matrix.mulVecLin Q) (fun j => w j • a j) Finset.univ
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul] at h
  rw [h]
  simp [Finset.sum_apply]

lemma la_bound {T μ x : ℝ} (hT : 1 ≤ T) (hμ : 2 * μ ^ 2 ≤ T ^ 2) {p0 : ℕ} (hp0 : 1 ≤ p0)
    (hx : x ≤ T ^ 2 ∨ x ≤ T ^ (4 * (p0 - 1)) * (2 * μ ^ 2)) : x ≤ (T ^ (2 * p0 - 1)) ^ 2 := by
  have he : (T ^ (2 * p0 - 1)) ^ 2 = T ^ (4 * (p0 - 1)) * T ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he]
  have h1 : 1 ≤ T ^ (4 * (p0 - 1)) := one_le_pow₀ hT
  rcases hx with hx | hx
  · calc x ≤ T ^ 2 := hx
      _ = 1 * T ^ 2 := by ring
      _ ≤ T ^ (4 * (p0 - 1)) * T ^ 2 := by gcongr
  · calc x ≤ T ^ (4 * (p0 - 1)) * (2 * μ ^ 2) := hx
      _ ≤ T ^ (4 * (p0 - 1)) * T ^ 2 := by gcongr

end

end ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

def famN (x : Matrix (Fin r) (Fin r) ℂ) (i : ℕ) (hi : i ≤ r) : Fin i → Fin r → ℂ :=
  fun a => col x (Fin.castLE hi a)

def pN (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) (i : ℕ) : Fin r → ℂ :=
  if h : i ≤ r then pv τ G (famN x i h) e else 0

def mN (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) (i : ℕ) : ℝ :=
  (hermC τ G (pN τ G x e i) (pN τ G x e i)).re

theorem famN_succ (x : Matrix (Fin r) (Fin r) ℂ) (i : ℕ) (h : i + 1 ≤ r) :
    (fun a : Fin i => famN x (i + 1) h a.castSucc) = famN x i (Nat.le_of_succ_le h) := rfl

theorem mN_zero (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) : mN τ G x e 0 = 0 := by
  simp [mN, pN, pv, hermC]

section Frame
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (p0 : ℕ) (hp0 : p0 ≤ r)
  (x : Matrix (Fin r) (Fin r) ℂ) (hx : x.det ≠ 0)
  (hsg : ∀ i (h : i ≤ r), 0 < psgn p0 i * (gramF τ G (famN x i h)).det.re)
  (e : Fin r → ℂ) (he : hermC τ G e e = 0)
include hsg

theorem unit_of (i : ℕ) (h : i ≤ r) : IsUnit (gramF τ G (famN x i h)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 := hsg i h
  rw [h0] at h1
  simp at h1

include hG

theorem mN_succ (i : ℕ) (h : i + 1 ≤ r) : mN τ G x e (i + 1) = mN τ G x e i +
    (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re := by
  have hp := pv_pyth hG (famN x (i + 1) h) e (unit_of p0 x hsg (i + 1) h)
    (unit_of p0 x hsg i (Nat.le_of_succ_le h))
  rw [famN_succ] at hp
  simp only [mN, pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]
  rw [hp, Complex.add_re]

theorem mN_step (i : ℕ) (h : i + 1 ≤ r) : 0 ≤ sgn p0 i * (mN τ G x e (i + 1) - mN τ G x e i) := by
  have hA1 := unit_of p0 x hsg (i + 1) h
  have hA0 := unit_of p0 x hsg i (Nat.le_of_succ_le h)
  have hs := det_step hG (famN x (i + 1) h) e hA1 hA0
  rw [famN_succ] at hs
  rw [mN_succ hG p0 x hsg e i h, add_sub_cancel_left]
  set y := yv τ G (famN x (i + 1) h) e (Fin.last i)
  set hd := hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)
  have hre := congrArg Complex.re hs
  rw [Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero] at hre
  have hps : psgn p0 (i + 1) = psgn p0 i * sgn p0 i := Finset.prod_range_succ _ _
  have key : (psgn p0 i * (gramF τ G (famN x i (Nat.le_of_succ_le h))).det.re) * (sgn p0 i * hd.re) =
      Complex.normSq y * (psgn p0 (i + 1) * (gramF τ G (famN x (i + 1) h)).det.re) := by
    rw [hps]; linear_combination (psgn p0 i * sgn p0 i) * hre
  have h1 := hsg i (Nat.le_of_succ_le h)
  have h2 := hsg (i + 1) h
  refine le_of_mul_le_mul_left ?_ h1
  rw [mul_zero, key]
  exact mul_nonneg (Complex.normSq_nonneg _) h2.le

include hp0 in
theorem mN_up (j : ℕ) (hj : j ≤ p0) (i : ℕ) (hi : i ≤ j) : mN τ G x e i ≤ mN τ G x e j := by
  have step : ∀ k, k < p0 → mN τ G x e k ≤ mN τ G x e (k + 1) := by
    intro k hk
    have h1 := mN_step (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := k) (h := by omega)
    have hs : sgn p0 k = 1 := by simp [sgn, hk]
    rw [hs] at h1
    linarith
  revert hj
  induction j, hi using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hij ih => intro hj; exact (ih (by omega)).trans (step j (by omega))

theorem mN_down (i : ℕ) (hi : p0 ≤ i) (j : ℕ) (hij : i ≤ j) (hj : j ≤ r) :
    mN τ G x e j ≤ mN τ G x e i := by
  have step : ∀ k, p0 ≤ k → k + 1 ≤ r → mN τ G x e (k + 1) ≤ mN τ G x e k := by
    intro k hk hkr
    have h1 := mN_step (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := k) (h := hkr)
    have hs : sgn p0 k = -1 := by simp [sgn, not_lt.mpr hk]
    rw [hs] at h1
    linarith
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hij ih => intro hj; exact (step j (by omega) hj).trans (ih (by omega))

include hx in
theorem pN_top : pN τ G x e r = e := by
  have hA := unit_of p0 x hsg r le_rfl
  rw [pN, dif_pos le_rfl]
  have he' : e = ∑ d, (x⁻¹ *ᵥ e) d • famN x r le_rfl d := by
    have h1 : x *ᵥ (x⁻¹ *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx),
        Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, famN, col]
    exact Finset.sum_congr rfl fun d _ => by rw [mul_comm]; rfl
  have h2 : e - pv τ G (famN x r le_rfl) e = ∑ d, ((x⁻¹ *ᵥ e) d - yv τ G (famN x r le_rfl) e d) •
      famN x r le_rfl d := by
    conv_lhs => arg 1; rw [he']
    rw [pv, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => (sub_smul _ _ _).symm
  have h3 := comb_orth_zero τ G (famN x r le_rfl) hA _ fun d => by
    rw [← h2, hC_sub_left, pv_orth τ G _ e hA d]; exact sub_self _
  rw [← h2] at h3
  exact (sub_eq_zero.mp h3).symm

include hx he in
theorem mN_top : mN τ G x e r = 0 := by
  unfold mN
  rw [pN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e), he]
  simp

include hp0 hx he in
theorem mN_bounds (i : ℕ) (hi : i ≤ r) : 0 ≤ mN τ G x e i ∧ mN τ G x e i ≤ mN τ G x e p0 := by
  rcases le_total i p0 with hi0 | hi0
  · constructor
    · have h1 := mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e)
        (j := i) (hj := hi0) (i := 0) (hi := Nat.zero_le _)
      rw [mN_zero] at h1
      exact h1
    · exact mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e)
        (j := p0) (hj := le_rfl) (i := i) (hi := hi0)
  · constructor
    · have h1 := mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e)
        (i := i) (hi := hi0) (j := r) (hij := hi) (hj := le_rfl)
      rw [mN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e) (he := he)] at h1
      exact h1
    · exact mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e)
        (i := p0) (hi := le_rfl) (j := i) (hij := hi0) (hj := hi)

include hp0 hx he in
theorem mN_pos (hne : e ≠ 0) : 0 < mN τ G x e p0 := by
  by_contra hle
  rw [not_lt] at hle
  have hz : ∀ i, i ≤ r → mN τ G x e i = 0 := fun i hi => by
    have := mN_bounds hG p0 hp0 x hx hsg e he i hi; linarith
  have hstep : ∀ i (h : i + 1 ≤ r), pN τ G x e (i + 1) = pN τ G x e i := by
    intro i h
    have hA1 := unit_of p0 x hsg (i + 1) h
    have hA0 := unit_of p0 x hsg i (Nat.le_of_succ_le h)
    have hd0 : (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re = 0 := by
      have := mN_succ hG p0 x hsg e i h
      rw [hz i (by omega), hz (i + 1) h] at this; linarith
    have hs := det_step hG (famN x (i + 1) h) e hA1 hA0
    have hre := congrArg Complex.re hs
    rw [Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero, hd0,
      mul_zero] at hre
    have hd1 : (gramF τ G (famN x (i + 1) h)).det.re ≠ 0 := fun h0 => by
      have := hsg (i + 1) h; rw [h0, mul_zero] at this; exact lt_irrefl _ this
    have hy : yv τ G (famN x (i + 1) h) e (Fin.last i) = 0 :=
      Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hre.symm).resolve_right hd1)
    have hdv := dv_zero τ G (famN x (i + 1) h) e hA1 hA0 hy
    rw [dv, famN_succ, sub_eq_zero] at hdv
    simp only [pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]
    exact hdv
  have hall : ∀ i, i ≤ r → pN τ G x e i = 0 := by
    intro i hi
    induction i with
    | zero => rw [pN, dif_pos (Nat.zero_le r), pv]; exact Finset.sum_empty
    | succ i ih => rw [hstep i hi, ih (by omega)]
  exact hne ((pN_top hG p0 x hx hsg e).symm.trans (hall r le_rfl))

end Frame

end

end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
end
