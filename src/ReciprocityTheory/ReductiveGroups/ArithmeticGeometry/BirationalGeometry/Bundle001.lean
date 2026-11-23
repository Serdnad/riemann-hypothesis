module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

section Chart

variable (o : Type*) {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι : Type*}

def chartRing (x : ι → Ω) (i : ι) : Subalgebra o Ω :=
  Algebra.adjoin o (Set.range fun j => x j / x i)

structure ChartBundle (x : ι → Ω) (r : ℕ) (E : Type*) [AddCommGroup E] [Module Ω E] where

  lat : ι → AddSubgroup E

  stable : ∀ i, ∀ a ∈ chartRing o x i, ∀ e ∈ lat i, a • e ∈ lat i

  frame : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing o x i) ∧
    (∀ l, c l ∈ chartRing o x i) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ lat i) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing o x i) ∧ e = ∑ q, a q • b q

  overlap : ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ lat i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ lat j

variable {o}

theorem div_mem_chartRing (x : ι → Ω) (i j : ι) :
    x j / x i ∈ chartRing o x i :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem exists_pow_mul_mem_chartRing (x : ι → Ω) (i j : ι) (hi : x i ≠ 0)
    {a : Ω} (ha : a ∈ chartRing o x i) :
    ∃ m : ℕ, (x i / x j) ^ m * a ∈ chartRing o x j := by
  have hij : x i / x j ∈ chartRing o x j := div_mem_chartRing x j i
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have : x i / x j * (x k / x i) = x k / x j := by field_simp
    rw [pow_one, this]
    exact div_mem_chartRing x j k
  | algebraMap r =>
    exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y + z) =
        (x i / x j) ^ n * ((x i / x j) ^ m * y) + (x i / x j) ^ m * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hij _) hm) (mul_mem (pow_mem hij _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y * z) = ((x i / x j) ^ m * y) * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact mul_mem hm hn

variable (o)

def lineLat (x : ι → Ω) (d : ℕ) (i : ι) : AddSubgroup Ω :=
  ((Subalgebra.toSubmodule (chartRing o x i)).map (LinearMap.mulRight o (x i ^ d))).toAddSubgroup

variable {o}

theorem mem_lineLat (x : ι → Ω) (d : ℕ) (i : ι) (e : Ω) :
    e ∈ lineLat o x d i ↔ ∃ a ∈ chartRing o x i, a * x i ^ d = e := by
  simp [lineLat]

variable (o)

def lineBundle (x : ι → Ω) (d : ℕ) : ChartBundle o x 1 Ω where
  lat := lineLat o x d
  stable i a ha e he := by
    obtain ⟨c, hc, rfl⟩ := (mem_lineLat x d i e).1 he
    refine (mem_lineLat x d i _).2 ⟨a * c, mul_mem ha hc, ?_⟩
    rw [smul_eq_mul, mul_assoc]
  frame i hi := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    refine ⟨fun _ => x i ^ d, ?_, ?_, ?_⟩
    · rw [linearIndependent_unique_iff]
      exact pow_ne_zero _ hi
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 (pow_ne_zero _ hi))
    · intro e
      rw [mem_lineLat]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨fun _ => a, fun _ => ha, by simp⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a 0, ha 0, by simp⟩
  overlap i j hi hj e he := by
    obtain ⟨a, ha, rfl⟩ := (mem_lineLat x d i e).1 he
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_chartRing x i j hi ha
    refine ⟨m, (mem_lineLat x d j _).2 ⟨(x i / x j) ^ m * a * (x i / x j) ^ d,
      mul_mem hm (pow_mem (div_mem_chartRing x j i) _), ?_⟩⟩
    rw [smul_eq_mul, div_pow, div_pow]
    field_simp

end Chart

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

theorem fibSys_finite {W : Type*} [Fintype W] (r : W → ℕ) (H : W → MvPolynomial W ℂ)
    (hH : ∀ i, (H i).totalDegree < r i) :
    {w : W → ℂ | ∀ i, w i ^ r i = eval w (H i)}.Finite := by
  classical
  rcases isEmpty_or_nonempty W with hW | hW
  · exact Set.Subsingleton.finite fun x _ y _ => funext fun i => (IsEmpty.false i).elim
  obtain ⟨B, hB⟩ : ∃ B : Finset (W →₀ ℕ), ∀ u, u ∈ B ↔ ∀ i, u i < r i := by
    refine ⟨(Fintype.piFinset fun i => Finset.range (r i)).map
      Finsupp.equivFunOnFinite.symm.toEmbedding, fun u => ?_⟩
    rw [Finset.mem_map_equiv, Equiv.symm_symm, Fintype.mem_piFinset]
    simp [Finset.mem_range]
  obtain ⟨M, hMdef⟩ : ∃ M : Submodule ℂ (MvPolynomial W ℂ),
      M = Submodule.span ℂ ((fun b => monomial b (1 : ℂ)) '' (B : Set (W →₀ ℕ))) := ⟨_, rfl⟩
  have hmon : ∀ (n : ℕ) (u : W →₀ ℕ), u.degree ≤ n → ∀ a : ℂ, ∃ q ∈ M,
      ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) → eval w (monomial u a) = eval w q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro u hu a
    by_cases hall : ∀ i, u i < r i
    · refine ⟨monomial u a, ?_, fun _ _ => rfl⟩
      have e : monomial u a = a • monomial u (1 : ℂ) := by rw [smul_monomial, smul_eq_mul, mul_one]
      rw [e, hMdef]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨u, (hB u).mpr hall, rfl⟩)
    · push_neg at hall
      obtain ⟨i, hi⟩ := hall
      have hle : Finsupp.single i (r i) ≤ u := Finsupp.single_le_iff.mpr hi
      obtain ⟨u', hu'⟩ : ∃ u', u = u' + Finsupp.single i (r i) :=
        ⟨u - Finsupp.single i (r i), (tsub_add_cancel_of_le hle).symm⟩
      have hdeg : u'.degree + r i = u.degree := by
        rw [hu', map_add (f := _), Finsupp.degree_single]
      have hsplit : ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) →
          eval w (monomial u a) = eval w (monomial u' a * H i) := by
        intro w hw
        rw [hu', show monomial (u' + Finsupp.single i (r i)) a =
          monomial u' a * monomial (Finsupp.single i (r i)) 1 by rw [monomial_mul, mul_one],
          map_mul, map_mul, ← X_pow_eq_monomial, map_pow, eval_X, hw i]
      have hsum : monomial u' a * H i =
          ∑ v ∈ (H i).support, monomial (u' + v) (a * AddMonoidAlgebra.coeff (H i) v) := by
        conv_lhs => rw [(H i).as_sum]
        rw [Finset.mul_sum]
        simp only [monomial_mul]
      have hterm : ∀ v ∈ (H i).support, ∃ q ∈ M, ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) →
          eval w (monomial (u' + v) (a * AddMonoidAlgebra.coeff (H i) v)) = eval w q := by
        intro v hv
        have hv' : v.degree ≤ (H i).totalDegree := le_totalDegree hv
        have hlt : (u' + v).degree < n := by
          rw [map_add (f := _)]
          have := hH i
          omega
        exact ih _ hlt _ le_rfl _
      choose q hqM hq using hterm
      refine ⟨∑ v ∈ (H i).support.attach, q v.1 v.2, Submodule.sum_mem _ fun v _ => hqM v.1 v.2, ?_⟩
      intro w hw

      rw [hsplit w hw, hsum, map_sum, map_sum]
      exact (Finset.sum_attach _ _).symm.trans (Finset.sum_congr rfl fun v _ => hq v.1 v.2 w hw)
  have hA : ∀ p : MvPolynomial W ℂ, ∃ q ∈ M, ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) →
      eval w p = eval w q := by
    intro p
    refine MvPolynomial.induction_on' p (fun u a => hmon _ u le_rfl a) (fun p q hp hq => ?_)
    obtain ⟨p', hp'M, hp'⟩ := hp
    obtain ⟨q', hq'M, hq'⟩ := hq
    exact ⟨p' + q', M.add_mem hp'M hq'M, fun w hw => by rw [map_add (f := _), map_add (f := _), hp' w hw, hq' w hw]⟩
  have hex : ∀ x y : W → ℂ, ∃ i, x ≠ y → x i ≠ y i := fun x y => by
    by_cases h : x = y
    · exact ⟨Classical.arbitrary W, fun h' => (h' h).elim⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact ⟨i, fun _ => hi⟩
  choose idx hidx using hex
  by_contra hinf
  have hinf' : Set.Infinite {w : W → ℂ | ∀ i, w i ^ r i = eval w (H i)} := hinf
  obtain ⟨T, hTS, hTcard⟩ := hinf'.exists_subset_card_eq (B.card + 1)
  let Φ : (B → ℂ) →ₗ[ℂ] (T → ℂ) :=
    { toFun := fun c t => ∑ b : B, c b * eval (t : W → ℂ) (monomial (b : W →₀ ℕ) 1)
      map_add' := fun c c' => by
        funext t
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        funext t
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hΦ : ∀ c t, Φ c t = ∑ b : B, c b * eval (t : W → ℂ) (monomial (b : W →₀ ℕ) 1) :=
    fun _ _ => rfl
  have key : ∀ q ∈ M, ∃ c : B → ℂ, ∀ t : T, eval (t : W → ℂ) q = Φ c t := by
    intro q hq
    rw [hMdef] at hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      refine ⟨Pi.single ⟨b, hb⟩ 1, fun t => ?_⟩
      rw [hΦ, Finset.sum_eq_single ⟨b, hb⟩]
      · simp
      · intro b' _ hb'
        simp [Pi.single_apply, hb']
      · simp
    | zero => exact ⟨0, fun t => by simp [hΦ]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hy
      exact ⟨c + c', fun t => by rw [map_add (f := _), hc, hc', map_add (f := _)]; rfl⟩
    | smul a x _ hx =>
      obtain ⟨c, hc⟩ := hx
      exact ⟨a • c, fun t => by rw [MvPolynomial.smul_eval, hc, map_smul]; rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : (W → ℂ) → MvPolynomial W ℂ, ∀ x, L x = ∏ y ∈ T.erase x,
      (C ((x (idx x y) - y (idx x y))⁻¹) * (X (idx x y) - C (y (idx x y)))) := ⟨_, fun _ => rfl⟩
  have hLself : ∀ x, eval x (L x) = 1 := by
    intro x
    rw [hL, map_prod]
    refine Finset.prod_eq_one fun y hy => ?_
    have hne : x ≠ y := (Finset.ne_of_mem_erase hy).symm
    rw [map_mul, eval_C, map_sub, eval_X, eval_C, inv_mul_cancel₀ (sub_ne_zero.mpr (hidx x y hne))]
  have hLother : ∀ x, ∀ z ∈ T, z ≠ x → eval z (L x) = 0 := by
    intro x z hz hzx
    rw [hL, map_prod]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hzx, hz⟩) ?_
    rw [map_mul, map_sub, eval_X, eval_C, eval_C, sub_self, mul_zero]
  have hsurj : Function.Surjective Φ := by
    intro f
    obtain ⟨f', hf'⟩ : ∃ f' : (W → ℂ) → ℂ, ∀ t : T, f' t = f t :=
      ⟨fun x => if h : x ∈ T then f ⟨x, h⟩ else 0, fun t => by simp [t.2]⟩
    obtain ⟨q, hqM, hq⟩ := hA (∑ x ∈ T, C (f' x) * L x)
    obtain ⟨c, hc⟩ := key q hqM
    refine ⟨c, funext fun t => ?_⟩

    rw [← hc t, ← hq t (hTS t.2), map_sum, Finset.sum_eq_single (t : W → ℂ)]
    · rw [map_mul, eval_C, hLself, mul_one, hf']
    · intro x _ hxt
      rw [map_mul, hLother x t t.2 (Ne.symm hxt), mul_zero]
    · intro h
      exact absurd t.2 h
  have h1 := LinearMap.finrank_range_le Φ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at h1
  omega

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {σ : Type}

abbrev qmap : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)

def qIdeal (P : Ideal (MvPolynomial σ ℤ)) : Ideal (MvPolynomial σ ℚ) := P.map qmap

theorem qmap_injective : Function.Injective (qmap : MvPolynomial σ ℤ → MvPolynomial σ ℚ) := MvPolynomial.map_injective _ Int.cast_injective

theorem exists_int_mul_eq_qmap (q : MvPolynomial σ ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ q' : MvPolynomial σ ℤ, (D : MvPolynomial σ ℚ) * q = qmap q' := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨a.den, by exact_mod_cast a.den_nz, MvPolynomial.monomial u a.num, ?_⟩
    rw [show ((a.den : ℤ) : MvPolynomial σ ℚ) = C ((a.den : ℤ) : ℚ) from (map_intCast (C : ℚ →+* MvPolynomial σ ℚ) _).symm,
      C_mul_monomial, MvPolynomial.map_monomial]
    congr 1
    push_cast
    exact Rat.den_mul_eq_num a
  | add p q hp hq =>
    obtain ⟨D₁, hD₁, p', hp'⟩ := hp
    obtain ⟨D₂, hD₂, q', hq'⟩ := hq
    refine ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂, (D₂ : MvPolynomial σ ℤ) * p' + (D₁ : MvPolynomial σ ℤ) * q', ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_intCast, map_intCast, ← hp', ← hq']
    push_cast
    ring

theorem exists_int_mul_mem_of_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) {g : MvPolynomial σ ℚ}
    (hg : g ∈ qIdeal P) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ h ∈ P, (N : MvPolynomial σ ℚ) * g = qmap h := by
  have hg' : g ∈ Submodule.span (MvPolynomial σ ℚ) (qmap '' (P : Set (MvPolynomial σ ℤ))) := hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact ⟨1, one_ne_zero, h, hh, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, P.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, hN₁, h₁, hh₁, e₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂, hh₂, e₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, (N₂ : MvPolynomial σ ℤ) * h₁ + (N₁ : MvPolynomial σ ℤ) * h₂,
      P.add_mem (P.mul_mem_left _ hh₁) (P.mul_mem_left _ hh₂), ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_intCast, map_intCast, ← e₁, ← e₂]
    push_cast
    ring
  | smul a x _ hx =>
    obtain ⟨N, hN, h, hh, e⟩ := hx
    obtain ⟨D, hD, a', ha'⟩ := exists_int_mul_eq_qmap a
    refine ⟨D * N, mul_ne_zero hD hN, a' * h, P.mul_mem_left _ hh, ?_⟩
    rw [map_mul, ← ha', ← e, smul_eq_mul]
    push_cast
    ring

theorem mem_of_qmap_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {f : MvPolynomial σ ℤ}
    (hf : qmap f ∈ qIdeal P) : f ∈ P := by
  obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hf
  have hNf : (N : MvPolynomial σ ℤ) * f = h := by
    apply qmap_injective
    rw [map_mul, map_intCast, e]
  rw [← hNf, show (N : MvPolynomial σ ℤ) = C N from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) N).symm] at hh
  rcases hP.mem_or_mem hh with hC | hf'
  · have : N ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hC
    rw [hH] at this
    exact absurd ((Submodule.mem_bot ℤ).mp this) hN
  · exact hf'

def ratHom (P : Ideal (MvPolynomial σ ℤ)) :
    MvPolynomial σ ℤ ⧸ P →+* MvPolynomial σ ℚ ⧸ qIdeal P :=
  Ideal.quotientMap (qIdeal P) qmap Ideal.le_comap_map

theorem ratHom_mk (P : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ) :
    ratHom P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk (qIdeal P) (qmap f) := rfl

theorem ratHom_isLocalization (P : Ideal (MvPolynomial σ ℤ)) :
    (letI := (ratHom P).toAlgebra
     IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
       (MvPolynomial σ ℚ ⧸ qIdeal P)) := by
  let _ := (ratHom P).toAlgebra
  have hcast : ∀ n : ℤ, algebraMap (MvPolynomial σ ℤ ⧸ P) (MvPolynomial σ ℚ ⧸ qIdeal P)
      (algebraMap ℤ (MvPolynomial σ ℤ ⧸ P) n) = algebraMap ℚ (MvPolynomial σ ℚ ⧸ qIdeal P) n := by
    intro n
    rw [eq_intCast, map_intCast, map_intCast]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.mp hy
    rw [hcast]
    exact (IsUnit.mk0 (n : ℚ) (by exact_mod_cast nonZeroDivisors.ne_zero hn)).map _
  · intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨D, hD, q', hq'⟩ := exists_int_mul_eq_qmap q
    refine ⟨⟨Ideal.Quotient.mk P q', ⟨algebraMap ℤ _ D,
      Submonoid.mem_map.mpr ⟨D, mem_nonZeroDivisors_of_ne_zero hD, rfl⟩⟩⟩, ?_⟩
    change _ * algebraMap (MvPolynomial σ ℤ ⧸ P) _ (algebraMap ℤ _ D) = ratHom P (Ideal.Quotient.mk P q')
    rw [hcast, ratHom_mk, ← hq', mul_comm, map_mul]
    congr 1
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change ratHom P _ = ratHom P _ at hxy
    rw [ratHom_mk, ratHom_mk, Ideal.Quotient.eq, ← map_sub] at hxy
    obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hxy
    have hNab : (N : MvPolynomial σ ℤ) * (a - b) = h := by
      apply qmap_injective
      rw [map_mul, map_intCast, e]
    refine ⟨⟨algebraMap ℤ _ N, Submonoid.mem_map.mpr ⟨N, mem_nonZeroDivisors_of_ne_zero hN, rfl⟩⟩, ?_⟩
    change algebraMap ℤ _ N * Ideal.Quotient.mk P a = algebraMap ℤ _ N * Ideal.Quotient.mk P b
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, eq_intCast, ← map_intCast (Ideal.Quotient.mk P), ← map_mul,
      hNab, Ideal.Quotient.eq_zero_iff_mem]
    exact hh

theorem isDomain_qQuot (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) :
    IsDomain (MvPolynomial σ ℚ ⧸ qIdeal P) := by
  let _ := (ratHom P).toAlgebra
  have := ratHom_isLocalization P
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial σ ℤ ⧸ P)
    (M := Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
    (S := MvPolynomial σ ℚ ⧸ qIdeal P) ?_
  rintro _ ⟨n, hn, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  rw [eq_intCast, ← map_intCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
    show (n : MvPolynomial σ ℤ) = C n from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) n).symm] at h0
  have : n ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := h0
  rw [hH] at this
  exact nonZeroDivisors.ne_zero hn ((Submodule.mem_bot ℤ).mp this)

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter

section Vol

variable {o : Type*} [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}

def smallSectionCount (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (τ : ℕ) : ℝ :=
  Real.log (Nat.card {s : La τ // P τ (s : Ω)})

def arVolP (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) : ℝ :=
  limsup (fun k : ℕ => smallSectionCount P La (a * k) /
    (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop

end Vol

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
