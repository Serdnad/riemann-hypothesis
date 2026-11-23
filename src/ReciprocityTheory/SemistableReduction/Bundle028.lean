module

public import ReciprocityTheory.SemistableReduction.SemiDegM
public import ReciprocityTheory.SemistableReduction.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.SemistableReduction.SemiDegE
public import ReciprocityTheory.SemistableReduction.Bundle027
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def hypG {K : Type} [Field K] {r : ℕ} (j p : Fin r) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun a b => (if a = j ∧ b = p then 1 else 0) + (if a = p ∧ b = j then 1 else 0)

def hypForm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r) :
    HermForm K r where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hypG j p
  G_herm a b := by
    simp only [hypG, Matrix.of_apply, map_add (f := _), apply_ite S.c, map_one, map_zero]
    rw [add_comm]
    congr 1 <;> simp only [and_comm]

theorem hypForm_h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r)
    (x y : Fin r → K) : (hypForm S j p).h x y = S.c (x j) * y p + S.c (x p) * y j := by
  rw [HermForm.h]
  have e : ∀ a, ∑ b, (hypForm S j p).c (x a) * (hypForm S j p).G a b * y b =
      (if a = j then S.c (x a) * y p else 0) + (if a = p then S.c (x a) * y j else 0) := by
    intro a
    simp only [hypForm, hypG, Matrix.of_apply, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · by_cases ha : a = j <;> simp [ha]
    · by_cases ha : a = p <;> simp [ha]
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp [Finset.sum_add_distrib]

theorem abs_norm_neg {K : Type} [Field K] [NumberField K] (z : K) :
    |((Algebra.norm ℚ (-z) : ℚ) : ℝ)| = |((Algebra.norm ℚ z : ℚ) : ℝ)| := by
  rw [neg_eq_neg_one_mul, map_mul, Rat.cast_mul, abs_mul]
  have h1 : (-1 : K) = algebraMap ℚ K (-1) := by simp
  rw [h1, Algebra.norm_algebraMap]
  simp

theorem top_le_zero (hN : IntegralIndexStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (S : HermForm K r) (j p : Fin r) (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K))
    (hGj : Gj.FG) (hGp : Gp.FG) (hj : ∀ x ∈ Gj, IsAt j x) (hp : ∀ x ∈ Gp, IsAt p x)
    (hpair : ∀ x ∈ Gj, ∀ y ∈ Gp, IsIntegralElt (S.c (x j) * y p))
    (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hx0j : x0 j ≠ 0) (hy : y ∈ Gp) (hyp : y p ≠ 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (d : ℝ) (hd : 0 < d) (hδj : ∀ σ, δ σ j = d)
    (hδp : ∀ σ, δ σ p = d⁻¹) (h0 : latDeg (diagMet δ) Gj ![x0] = 0) :
    latDeg (diagMet δ) Gp ![y] ≤ 0 := by
  have hjp' : j ≠ p := fun h => by rw [h] at hjp; omega
  have hx0p : x0 p = 0 := hj x0 hx0 p (Ne.symm hjp')
  have hyj : y j = 0 := hp y hy j hjp'

  set n : ℝ := (Fintype.card (K →+* ℂ) : ℝ)
  have e0 := h0
  rw [latDeg_single δ Gj j x0 (hj x0 hx0)] at e0
  simp only [hδj] at e0
  rw [sum_log_single (x0 j) hx0j d hd] at e0
  rw [latDeg_single δ Gp p y (hp y hy)]
  simp only [hδp]
  rw [sum_log_single (y p) hyp d⁻¹ (inv_pos.2 hd), Real.log_inv]

  set A : ℝ := (spanIdx Gj ![x0] : ℝ)
  set B : ℝ := (spanIdx Gp ![y] : ℝ)
  set X : ℝ := |((Algebra.norm ℚ (x0 j) : ℚ) : ℝ)|
  set Y : ℝ := |((Algebra.norm ℚ (y p) : ℚ) : ℝ)|
  have hA : 1 ≤ A := by
    have := spanIdx_ne_zero Gj ![x0] hGj (kBasisIn_single j Gj hj x0 hx0 hx0j)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hB : 1 ≤ B := by
    have := spanIdx_ne_zero Gp ![y] hGp (kBasisIn_single p Gp hp y hy hyp)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hX : 0 < X := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hx0j
  have hY : 0 < Y := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hyp
  have key : A * B ≤ X * Y := by
    set T := Gj ⊔ Gp
    have hT : T.FG := hGj.sup hGp
    have hbT : IsKBasisIn T ![x0, y] := by
      refine ⟨fun i => ?_, ?_, ?_⟩
      · fin_cases i
        · exact Submodule.mem_sup_left hx0
        · exact Submodule.mem_sup_right hy
      · rw [LinearIndependent.pair_iff]
        intro s t hst
        have h1 := congr_fun hst j
        have h2 := congr_fun hst p
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hx0p, hyj,
          mul_zero, add_zero, zero_add] at h1 h2
        exact ⟨(mul_eq_zero.1 h1).resolve_right hx0j, (mul_eq_zero.1 h2).resolve_right hyp⟩
      · intro z hz
        obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
        rw [Matrix.range_cons_cons_empty]
        have e1 : z1 = (z1 j / x0 j) • x0 := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = j
          · subst ha; field_simp
          · rw [hj z1 hz1 a ha, hj x0 hx0 a ha, mul_zero]
        have e2 : z2 = (z2 p / y p) • y := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = p
          · subst ha; field_simp
          · rw [hp z2 hz2 a ha, hp y hy a ha, mul_zero]
        rw [e1, e2]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hint : IsIntegralOn (hypForm S j p) T := by
      intro z hz w hw
      obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨w1, hw1, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hw
      rw [hypForm_h]
      simp only [Pi.add_apply, hj z1 hz1 p (Ne.symm hjp'), hj w1 hw1 p (Ne.symm hjp'),
        hp z2 hz2 j hjp', hp w2 hw2 j hjp', add_zero, zero_add]
      refine isIntegralElt_add (hpair z1 hz1 w2 hw2) ?_
      have := isIntegralElt_c S (hpair w1 hw1 z2 hz2)
      rwa [map_mul, S.c_invol, mul_comm] at this
    have hgram : hGram (hypForm S j p) ![x0, y] =
        !![0, S.c (x0 j) * y p; S.c (y p) * x0 j, 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [hGram, hypForm_h, hx0p, hyj]
    have hdet : (hGram (hypForm S j p) ![x0, y]).det = -((S.c (x0 j) * y p) * (S.c (y p) * x0 j)) := by
      rw [hgram, Matrix.det_fin_two_of]
      ring
    have hcx : S.c (x0 j) ≠ 0 := fun h => hx0j (S.c.injective (by rw [h, map_zero]))
    have hcy : S.c (y p) ≠ 0 := fun h => hyp (S.c.injective (by rw [h, map_zero]))
    have hdet0 : (hGram (hypForm S j p) ![x0, y]).det ≠ 0 := by
      rw [hdet, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero hcx hyp) (mul_ne_zero hcy hx0j)
    have hb := hN K r 2 (hypForm S j p) T ![x0, y] hT hbT hint hdet0
    rw [hdet, abs_norm_neg, map_mul, map_mul, map_mul, norm_c, norm_c] at hb
    push_cast at hb
    rw [spanIdx_pair j p hjp Gj Gp hj hp x0 y hx0 hy] at hb
    push_cast at hb
    have hb' : (A * B) ^ 2 ≤ (X * Y) ^ 2 :=
      le_of_le_of_eq hb (by simp only [X, Y]; rw [abs_mul, abs_mul, abs_mul]; ring)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hb'
  have hlog : Real.log A + Real.log B ≤ Real.log X + Real.log Y := by
    rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul hX.ne' hY.ne']
    exact Real.log_le_log (by positivity) key
  linarith

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem gr_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (j : Fin r) : ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), IsAt j x := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if (j : ℕ) ≤ a then y a else 0) = 0
  split_ifs with h
  · exact hy a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
  · rfl

theorem exists_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp) (j : Fin r) :
    ∃ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), x j ≠ 0 := by
  obtain ⟨a, ha, hav⟩ := hsp (Pi.single j 1)
  have hcut : a • (Pi.single j 1 : Fin r → K) ∈ cutSub K r (j + 1) := by
    intro i hi
    have : i ≠ j := fun e => by rw [e] at hi; omega
    simp [this]
  refine ⟨projGe K r j (a • Pi.single j 1), ⟨_, ⟨hav, hcut⟩, rfl⟩, ?_⟩
  show (if (j : ℕ) ≤ j then (a • (Pi.single j 1 : Fin r → K)) j else 0) ≠ 0
  rw [if_pos le_rfl]
  simpa using ha

theorem pair_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (h2m : 2 * m ≤ r) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y))
    (j : Fin r) (hj : (j : ℕ) < m) :
    ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j),
      ∀ y ∈ (Lp ⊓ cutSub K r (Fin.rev j + 1)).map (projGe K r (Fin.rev j)),
        IsIntegralElt (S.c (x j) * y (Fin.rev j)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have hrev := Fin.val_rev j
  have hj' := j.isLt
  have e1 : projGe K r j x j = x j := by
    show (if (j : ℕ) ≤ j then x j else 0) = x j
    rw [if_pos le_rfl]
  have e2 : projGe K r (Fin.rev j) y (Fin.rev j) = y (Fin.rev j) := by
    show (if ((Fin.rev j : Fin r) : ℕ) ≤ (Fin.rev j : Fin r) then y (Fin.rev j) else 0) = _
    rw [if_pos le_rfl]
  rw [e1, e2]
  have h := hint x hxL y hyL
  rw [formM_witt, Finset.sum_eq_single j] at h
  · rwa [wVal_outer r m g j (Or.inl hj), wPart_outer r m j (Or.inl hj), one_mul] at h
  · intro a _ ha
    by_cases hlt : (a : ℕ) < j
    · have hao : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl (by omega)
      rw [wPart_outer r m a hao]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev, Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
      rw [this, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mid_supp {K : Type} [Field K] [NumberField K] {r : ℕ} (m : ℕ)
    (Lp : Submodule (𝓞 K) (Fin r → K)) :
    ∀ x ∈ (Lp ⊓ cutSub K r (r - m)).map (projGe K r m), ∀ a : Fin r,
      ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0 := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if m ≤ (a : ℕ) then y a else 0) = 0
  split_ifs with h
  · exact hy a (by omega)
  · rfl

theorem mid_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    IsIntegralOn (midForm S m g hfix) ((Lp ⊓ cutSub K r (r - m)).map (projGe K r m)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have h := hint x hxL y hyL
  convert h using 1
  rw [formM_witt]
  simp only [HermForm.h, midForm, midG, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.isLt
  show (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then
      S.c (if m ≤ (a : ℕ) then x a else 0) * g a * (if m ≤ (a : ℕ) then y a else 0)
      else 0) = _
  by_cases hmid : m ≤ (a : ℕ) ∧ (a : ℕ) + m < r
  · have ho : ¬ ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) := by omega
    simp only [if_pos hmid, if_pos hmid.1]
    rw [wVal_mid r m g a ho, wPart_mid r m a ho]
    ring
  · rw [if_neg hmid]
    by_cases hlt : (a : ℕ) < m
    · have ho : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl hlt
      rw [wPart_outer r m a ho]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by omega)
      rw [this, map_zero, zero_mul]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end
