module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open NumberField Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Finset

namespace GlobalTheory.HaarWeight

theorem filter_lt_succ {p n : ℕ} (h : n < p) :
    (univ.filter fun b : Fin p => b.1 < n + 1) = insert ⟨n, h⟩ (univ.filter fun b : Fin p => b.1 < n) := by
  ext b
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

theorem filter_le_eq {p : ℕ} (a : Fin p) :
    (univ.filter fun b : Fin p => b ≤ a) = univ.filter fun b : Fin p => b.1 < a.1 + 1 := by
  ext b
  simp only [mem_filter, mem_univ, true_and, Fin.le_def]
  omega

private theorem one_le_partial_lemma (T : ℕ → ℝ) (m : ℕ → ℕ) (M p : ℕ) (hT : ∀ a, 0 ≤ T a)
    (hN : ∀ a < p, 1 ≤ ∏ b ∈ range (a + 1), T b) (hm : ∀ a, m a ≤ M) :
    ∀ k ≤ p, ∀ j ≤ M, (∏ b ∈ range k, T b) ^ j ≤
      (∏ a ∈ range k, ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range k, T a ^ m a := by
  intro k
  induction k with
  | zero => intro _ j _; simp
  | succ k ih =>
    intro hk j hj
    have hP1 : 1 ≤ ∏ b ∈ range (k + 1), T b := hN k (by omega)
    have hQ := ih (by omega) (m k) (hm k)
    have hnn : 0 ≤ (∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k :=
      mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (hT k) _)
    calc (∏ b ∈ range (k + 1), T b) ^ j ≤ (∏ b ∈ range (k + 1), T b) ^ (m k + M) :=
          pow_le_pow_right₀ hP1 (by have := hm k; omega)
      _ = (∏ b ∈ range k, T b) ^ m k * ((∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k) := by
          rw [pow_add, Finset.prod_range_succ]; ring
      _ ≤ ((∏ a ∈ range k, ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range k, T a ^ m a) *
            ((∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k) := mul_le_mul_of_nonneg_right hQ hnn
      _ = (∏ a ∈ range (k + 1), ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range (k + 1), T a ^ m a := by
          rw [Finset.prod_range_succ (fun a => ∏ b ∈ range (a + 1), T b),
            Finset.prod_range_succ (fun a => T a ^ m a)]
          ring

theorem one_le_partial {p : ℕ} (T : Fin p → ℝ) (m : Fin p → ℕ) (M : ℕ)
    (hN : ∀ a : Fin p, 1 ≤ ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) (hT : ∀ a, 0 ≤ T a)
    (hm : ∀ a, m a ≤ M) :
    1 ≤ (∏ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) ^ M * ∏ a, T a ^ m a := by
  classical
  let T' : ℕ → ℝ := fun b => if h : b < p then T ⟨b, h⟩ else 1
  let m' : ℕ → ℕ := fun b => if h : b < p then m ⟨b, h⟩ else 0
  have hT' : ∀ b, 0 ≤ T' b := by
    intro b
    simp only [T']
    split_ifs
    · exact hT _
    · norm_num
  have hm' : ∀ b, m' b ≤ M := by
    intro b
    simp only [m']
    split_ifs
    · exact hm _
    · exact Nat.zero_le _
  have hTT : ∀ b : Fin p, T b = T' b := fun b => by simp [T', b.2]
  have hmm : ∀ b : Fin p, m b = m' b := fun b => by simp [m', b.2]
  have hpre : ∀ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b =
      ∏ b ∈ range (a.1 + 1), T' b := by
    intro a
    have ha := a.2
    rw [filter_le_eq, Finset.prod_filter]
    simp_rw [hTT]
    rw [Fin.prod_univ_eq_prod_range (fun i => if i < a.1 + 1 then T' i else 1) p, ← Finset.prod_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    omega
  have hN' : ∀ a < p, 1 ≤ ∏ b ∈ range (a + 1), T' b := fun a ha => (hpre ⟨a, ha⟩) ▸ hN ⟨a, ha⟩
  have key := one_le_partial_lemma T' m' M p hT' hN' hm' p le_rfl 0 (Nat.zero_le _)
  rw [pow_zero] at key
  have e1 : (∏ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) =
      ∏ a ∈ range p, ∏ b ∈ range (a + 1), T' b := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ b ∈ range (i + 1), T' b) p]
    exact Finset.prod_congr rfl fun a _ => hpre a
  have e2 : (∏ a : Fin p, T a ^ m a) = ∏ a ∈ range p, T' a ^ m' a := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => T' i ^ m' i) p]
    exact Finset.prod_congr rfl fun a _ => by rw [hTT, hmm]
  rw [e1, e2]
  exact key

theorem sum_exponent {r : ℕ} (c : Composition (r + 1)) : ∀ n, n ≤ c.length →
    ∑ b ∈ univ.filter (fun b : Fin c.length => b.1 < n),
      (2 * r + 1 + c.blocksFun b - 2 * c.sizeUpTo (b.1 + 1)) * c.blocksFun b =
      c.sizeUpTo n * (2 * r + 1 - c.sizeUpTo n) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n < c.length := by omega
    rw [filter_lt_succ hn', Finset.sum_insert (by simp), ih (by omega)]
    have hs := c.sizeUpTo_succ' ⟨n, hn'⟩
    have hle := c.sizeUpTo_le (n + 1)
    have hpos := c.one_le_blocksFun ⟨n, hn'⟩
    simp only at hs
    rw [hs] at hle ⊢
    generalize c.sizeUpTo n = x at hle ⊢
    generalize c.blocksFun ⟨n, hn'⟩ = y at hle hpos ⊢
    have h1 : x ≤ 2 * r + 1 := by omega
    have h2 : 2 * (x + y) ≤ 2 * r + 1 + y := by omega
    have h3 : x + y ≤ 2 * r + 1 := by omega
    zify [h1, h2, h3]
    ring

theorem endMin_sq {E : Type} [Field E] {r : ℕ} (rd : ℝ) (γ : PN.Pts E r) (a : Fin γ.1.length)
    (v : InfinitePlace E) :
    (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2 =
      ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
        ((rd ^ (2 * r + 1 + γ.1.blocksFun b - 2 * endIdx γ b))⁻¹ * v (γ.2 b)) ^ (2 * γ.1.blocksFun b) := by
  have ha := a.2
  have hsum := sum_exponent γ.1 (a.1 + 1) (by omega)
  rw [← filter_le_eq] at hsum
  unfold endIdx
  have hrd : ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
      ((rd ^ (2 * r + 1 + γ.1.blocksFun b - 2 * γ.1.sizeUpTo (b.1 + 1)))⁻¹) ^ (2 * γ.1.blocksFun b) =
      (rd ^ (2 * (γ.1.sizeUpTo (a.1 + 1) * (2 * r + 1 - γ.1.sizeUpTo (a.1 + 1)))))⁻¹ := by
    simp_rw [inv_pow, ← pow_mul]
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← hsum, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun b _ => by ring
  have hmin : v (endMin γ a) ^ 2 = ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
      v (γ.2 b) ^ (2 * γ.1.blocksFun b) := by
    unfold endMin Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry
    rw [map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [map_mul, map_pow]
    have hsg : v (((Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign (γ.1.blocksFun b) : ℤ) : E)) = 1 := by
      rw [Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign]
      push_cast
      rw [map_pow]
      have hm1 : v (-1) = 1 := by
        have h1 : v (-1) * v (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
        have h0 : 0 ≤ v (-1) := by
          first
            | exact v.1.nonneg (-1)
            | exact apply_nonneg v (-1)
            | positivity
        nlinarith
      rw [hm1, one_pow]
    rw [hsg, one_mul, ← pow_mul, mul_comm]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, hrd, hmin]

theorem gram_pow_le_haar : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (r k TT : ℕ) (rd H : ℝ) (γ : PN.Pts E r), 0 < rd → (∀ a, 1 ≤ ∏ v : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2) → NDPt rd γ ≤ H → NGPt rd TT γ ^ (k - 1) ≤ H ^ (6 * (2 * r + 2)) * nPt rd k TT γ := by
  intro E _ _ _ r k TT rd H γ hrd hN hD
  have hw0 : ∀ (w : InfinitePlace E) (x : E), 0 ≤ w x := fun w x => by
    first
      | exact w.1.nonneg x
      | exact apply_nonneg w x
      | positivity
  let Tw : Fin γ.1.length → InfinitePlace E → ℝ := fun a w =>
    (rd ^ (2 * r + 1 + γ.1.blocksFun a - 2 * endIdx γ a))⁻¹ * w (γ.2 a)
  let U : Fin γ.1.length → ℝ := fun a => ∏ w : InfinitePlace E, Tw a w ^ (2 * γ.1.blocksFun a)
  let mm : Fin γ.1.length → ℕ := fun a => 2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1
  have hTw : ∀ a w, 0 ≤ Tw a w := fun a w => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)
  have hU : ∀ a, 0 ≤ U a := fun a => Finset.prod_nonneg fun w _ => pow_nonneg (hTw a w) _
  have hNa : ∀ a, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b =
      ∏ w : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2 := by
    intro a
    simp only [U]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun w _ => (endMin_sq rd γ a w).symm
  have hmM : ∀ a, mm a ≤ 6 * (2 * r + 2) := by
    intro a
    simp only [mm]
    have h1 := γ.1.sizeUpTo_le (a.1 + 1)
    have h2 := γ.1.sizeUpTo_succ' a
    unfold endIdx
    omega
  have key := one_le_partial U mm (6 * (2 * r + 2)) (fun a => by rw [hNa]; exact hN a) hU hmM
  have hND : (∏ a : Fin γ.1.length, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b) =
      NDPt rd γ := by
    unfold NDPt
    exact Finset.prod_congr rfl fun a _ => hNa a
  rw [hND] at key
  have hNDnn : 0 ≤ NDPt rd γ := Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun w _ =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (pow_nonneg (hw0 _ _) _)
  have hY : ∏ a, U a ^ mm a = ∏ w : InfinitePlace E, ∏ a : Fin γ.1.length,
      Tw a w ^ (2 * γ.1.blocksFun a * (2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1)) := by
    simp only [U, mm]
    simp_rw [← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
  have hn : nPt rd k TT γ = NGPt rd TT γ ^ (k - 1) * ∏ a, U a ^ mm a := by
    rw [hY]
    unfold nPt NGPt
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
  have hG0 : 0 ≤ NGPt rd TT γ := Finset.prod_nonneg fun w _ =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)
  have hYnn : 0 ≤ ∏ a, U a ^ mm a := Finset.prod_nonneg fun a _ => pow_nonneg (hU a) _
  have h1 : 1 ≤ H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a :=
    calc 1 ≤ NDPt rd γ ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a := key
      _ ≤ H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hNDnn hD _) hYnn
  rw [hn]
  calc NGPt rd TT γ ^ (k - 1) = NGPt rd TT γ ^ (k - 1) * 1 := (mul_one _).symm
    _ ≤ NGPt rd TT γ ^ (k - 1) * (H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hG0 _)
    _ = H ^ (6 * (2 * r + 2)) * (NGPt rd TT γ ^ (k - 1) * ∏ a, U a ^ mm a) := by ring

end GlobalTheory.HaarWeight
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.MidLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hconj (x y : S.V) : star (S.hT x y) = S.hT y x := by
  have h := S.herm.eq x y
  simpa [starRingEnd_apply] using h

def prj (e f : Fin r → S.V) : S.V →ₗ[E] S.V :=
  LinearMap.id - ∑ a, (S.hT (f a)).smulRight (e a) - ∑ a, (S.hT (e a)).smulRight (f a)

theorem prj_apply (e f : Fin r → S.V) (y : S.V) :
    prj e f y = y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a := by
  simp [prj, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

variable {e f : Fin r → S.V} (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hef in
theorem hfe (a b : Fin r) : S.hT (f a) (e b) = if b = a then 1 else 0 := by
  rw [← hconj, hef]; split_ifs <;> simp

include hee hef in
theorem prj_e (b : Fin r) : prj e f (e b) = 0 := by
  rw [prj_apply]; simp [hfe hef, hee]

include hff hef in
theorem prj_f (b : Fin r) : prj e f (f b) = 0 := by
  rw [prj_apply]; simp [hff, hef]

theorem prj_perp {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) : prj e f y = y := by
  rw [prj_apply]; simp [(hy _).1, (hy _).2]

theorem pair_prj {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) (x : S.V) :
    S.hT (prj e f x) y = S.hT x y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [prj_apply]; simp [map_sub, map_sum, (hy _).1, (hy _).2]

include hee hef in
theorem prj_spanE {s : S.V} (hs : s ∈ Submodule.span E (Set.range e)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range e) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_e hee hef b)
  exact h hs

include hff hef in
theorem prj_spanF {s : S.V} (hs : s ∈ Submodule.span E (Set.range f)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range f) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_f hff hef b)
  exact h hs

theorem latSpanS_le_span (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    latSpanS aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.St.G.MidLat


open GlobalTheory.St.G.MidLat in
theorem GlobalTheory.St.G.midLat_selfDual_pairing : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧ ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb))) ∧ (∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = 1) ∧ ∀ y ∈ (VS D).L0, y - ∑ a, (VS D).hT (X.fY a) y • X.eX a - ∑ a, (VS D).hT (X.eX a) y • X.fY a ∈ X.Lb := by
  intro D X u
  have hprjL : ∀ y ∈ (VS D).L0, prj X.eX X.fY y ∈ X.Lb := by
    intro y hy
    rw [X.Lam_split] at hy
    obtain ⟨y1, hy1, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨s, hs, l, hl, rfl⟩ := Submodule.mem_sup.1 hy1
    have hs' := latSpanS_le_span _ _ hs
    have ht' := latSpanS_le_span _ _ ht
    rw [map_add (f := _), map_add (f := _), prj_spanE X.ee X.ef hs', prj_spanF X.ff X.ef ht', zero_add, add_zero,
      prj_perp (fun a => X.Lb_perp l hl a)]
    exact hl
  have hLbL : X.Lb ≤ (VS D).L0 := by
    rw [X.Lam_split]; exact le_sup_right.trans le_sup_left
  have h1 : ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
      ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧
        ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb)) := by
    intro y hy
    refine ⟨⟨fun h => ?_, fun h => hLbL h⟩, fun hint => ?_⟩
    · have := hprjL y h; rwa [prj_perp hy] at this
    · have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
      have hyL : y ∈ (VS D).L0 := by
        rw [← hU]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply, Submodule.mem_one]
        intro x hx
        obtain ⟨o, ho⟩ := hint _ (hprjL x hx)
        exact ⟨o, by rw [ho, pair_prj hy]⟩
      have := hprjL y hyL; rwa [prj_perp hy] at this
  refine ⟨h1, ?_, fun y hy => ?_⟩

  · let σ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (starRingEnd D.host.E)
    have hσ : ∀ o : 𝓞 D.host.E, ((σ o : 𝓞 D.host.E) : D.host.E) = star (o : D.host.E) := fun o => rfl
    let J : Ideal (𝓞 D.host.E) :=
      (LinearMap.range (((VS D).hT (X.zu u)).restrictScalars (𝓞 D.host.E) ∘ₗ X.Lb.subtype)).comap
        (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hJ : ∀ o, o ∈ J ↔ ∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = (o : D.host.E) := by
      intro o
      simp only [J, Submodule.mem_comap, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, LinearMap.restrictScalars_apply, Algebra.linearMap_apply, Subtype.exists,
        exists_prop]
    by_cases hJt : J = ⊤
    · obtain ⟨x, hx, hx1⟩ := (hJ 1).1 (hJt ▸ Submodule.mem_top)
      exact ⟨x, hx, by rw [hx1]; simp⟩
    exfalso
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJt
    have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)
    obtain ⟨c, hc, hc1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := D.host.E) hM0 hM.ne_top
    have hc' := (FractionalIdeal.mem_inv_iff (by rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero])).1 hc
    have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
    have hzL : X.zu u ∈ X.Lb := X.zu_Lb u
    have hwperp : ∀ a, (VS D).hT (X.eX a) (star c • X.zu u) = 0 ∧ (VS D).hT (X.fY a) (star c • X.zu u) = 0 := by
      intro a
      exact ⟨by rw [map_smul, smul_eq_mul, (X.zu_orth u a).1, mul_zero],
        by rw [map_smul, smul_eq_mul, (X.zu_orth u a).2, mul_zero]⟩
    have hwLb : star c • X.zu u ∈ X.Lb := by
      refine (h1 _ hwperp).2 ?_
      intro x hx
      have hxd : x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 := by rw [hU]; exact hLbL hx
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one] at hxd
      obtain ⟨o, ho⟩ := hxd (X.zu u) (hLbL hzL)
      have hoM : o ∈ M := hJM ((hJ o).2 ⟨x, hx, ho.symm⟩)
      obtain ⟨o', ho'⟩ := (FractionalIdeal.mem_one_iff _).1
        (hc' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨o, hoM, rfl⟩))
      refine ⟨σ o', ?_⟩
      change ((σ o' : 𝓞 D.host.E) : D.host.E) = _
      rw [hσ]
      change star (algebraMap (𝓞 D.host.E) D.host.E o') = _
      rw [ho', map_smul, smul_eq_mul, ← hconj (X.zu u) x, ← ho, star_mul, mul_comm]
    have hprim := (X.Fu_fixed u).2.2.2.2 (star c)
    dsimp only at hprim
    rw [X.flagZVector u] at hprim
    have horth : star c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (Formalism.MainNotions.S.Lat.hS D)
        (Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))) := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      have hX : Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
          = Submodule.span D.host.E (Set.range X.eX) := by
        show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
        rw [X.Fu_e u]
      rw [hX] at hx
      have hle : Submodule.span D.host.E (Set.range X.eX) ≤ LinearMap.ker ((VS D).hT (star c • X.zu u)) :=
        Submodule.span_le.2 (by
          rintro _ ⟨a, rfl⟩
          show (VS D).hT (star c • X.zu u) (X.eX a) = 0
          rw [← hconj, (hwperp a).1, star_zero])
      have := hle hx
      rw [LinearMap.mem_ker] at this
      rw [← hconj, this, star_zero]
    obtain ⟨o, ho⟩ := hprim ⟨Submodule.mem_sup_left ⟨hLbL hwLb, horth⟩, horth⟩
    apply hc1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨σ o, ?_⟩
    change ((σ o : 𝓞 D.host.E) : D.host.E) = c
    rw [hσ, ho, star_star]
  · have := hprjL y hy; rwa [prj_apply] at this
end
