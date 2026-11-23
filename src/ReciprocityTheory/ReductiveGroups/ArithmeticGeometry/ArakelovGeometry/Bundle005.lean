module

public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonoNormSq

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem bNormSq_nonneg' (μ : Measure (Ix κ → ℂ)) (m : ConeMetric (C := ℂ) (ι := Ix κ)) {r n : ℕ}
    (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) : 0 ≤ bNormSq μ s (wgt m n) c := by
  unfold bNormSq
  refine MeasureTheory.integral_nonneg fun z => mul_nonneg (sq_nonneg _) ?_
  unfold wgt
  refine inv_nonneg.mpr ?_
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem norm_le_of_sq_wgt_le {m : ConeMetric (C := ℂ) (ι := Ix κ)} {n : ℕ} {z : Ix κ → ℂ} (hz : z ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 * wgt m n z ≤ b) :
    a ≤ Real.sqrt b * m.ρ z ^ n := by
  have hρ : 0 < m.ρ z := m.pos z hz
  have hP : 0 < m.ρ z ^ n := pow_pos hρ n
  have hw : wgt m n z = ((m.ρ z ^ n) ^ 2)⁻¹ := by
    unfold wgt
    rw [← pow_mul, mul_comm n 2]
  rw [hw] at h
  have hP2 : 0 < (m.ρ z ^ n) ^ 2 := pow_pos hP 2
  have h2 : a ^ 2 ≤ b * (m.ρ z ^ n) ^ 2 := by
    rwa [← div_eq_mul_inv, div_le_iff₀ hP2] at h
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (b * (m.ρ z ^ n) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt b * m.ρ z ^ n := by rw [Real.sqrt_mul hb, Real.sqrt_sq hP.le]

theorem log_sqrt_bound (D : ℕ) {T : ℝ} (hT : 1 ≤ T) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ∧
      Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ≤
        (1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0' : 0 < T := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hpos : 0 < T * (n : ℝ) ^ D := mul_pos hT0' (pow_pos hnpos D)
  have hlog : Real.log (Real.sqrt (T * (n : ℝ) ^ D)) = (1 / 2) * (Real.log T + D * Real.log n) := by
    rw [Real.log_sqrt hpos.le, Real.log_mul hT0'.ne' (pow_pos hnpos D).ne', Real.log_pow]
    ring
  have hT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2n : Real.log 2 ≤ Real.log (n + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hln : Real.log n ≤ Real.log (n + 1) := Real.log_le_log hnpos (by linarith)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  refine ⟨?_, ?_⟩
  · rw [hlog]
    exact mul_nonneg (by norm_num) (add_nonneg hT0 (mul_nonneg hD0 hn0))
  · rw [hlog]
    have h1 : Real.log T ≤ Real.log T / Real.log 2 * Real.log (n + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hl2n hT0
    have h2 : (D : ℝ) * Real.log n ≤ D * Real.log (n + 1) := mul_le_mul_of_nonneg_left hln hD0
    have h3 : (1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1) =
        (1 / 2) * (Real.log T / Real.log 2 * Real.log (n + 1) + D * Real.log (n + 1)) := by ring
    rw [h3]
    linarith

theorem choose_bound (k D : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (((n + k + D).choose D : ℕ) : ℝ) ≤ ((1 + k + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
  have hN : n + k + D ≤ (1 + k + D) * n := by nlinarith
  have h1 : (n + k + D).choose D ≤ (n + k + D) ^ D := Nat.choose_le_pow _ _
  have h2 : (n + k + D) ^ D ≤ ((1 + k + D) * n) ^ D := Nat.pow_le_pow_left hN D
  have h3 : (n + k + D).choose D ≤ (1 + k + D) ^ D * n ^ D := by
    rw [← mul_pow]
    exact h1.trans h2
  exact_mod_cast h3

theorem le_of_injective_mulVec {R r : ℕ} (M : Matrix (Fin R) (Fin r) ℚ)
    (hM : Function.Injective M.mulVec) : r ≤ R := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := Matrix.mulVecLin M) hM
  simpa using h

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def deh {ι S : Type*} [Field S] (v : ι → S) (i₀ : ι) : MvPolynomial ι ℤ →+* S :=
  eval₂Hom (Int.castRingHom S) fun i => v i / v i₀

def homog {ι : Type*} [DecidableEq ι] (i₀ : ι) (N : ℕ) (G : MvPolynomial ι ℤ) :
    MvPolynomial ι ℤ :=
  ∑ m ∈ G.support, monomial (m + Finsupp.single i₀ (N - m.degree)) (G.coeff m)

theorem homog_isHomogeneous {ι : Type*} [DecidableEq ι] (i₀ : ι) {N : ℕ} (G : MvPolynomial ι ℤ)
    (hN : G.totalDegree ≤ N) : (homog i₀ N G).IsHomogeneous N := by
  apply IsHomogeneous.sum
  intro m hm
  apply isHomogeneous_monomial
  have : m.degree ≤ N := le_trans (le_totalDegree hm) hN
  have h := Finsupp.degree_single (R := ℕ) i₀ (N - m.degree)
  simp only [map_add (f := _), h]
  omega

theorem eval₂_homog {ι S : Type*} [Fintype ι] [DecidableEq ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {N : ℕ} (G : MvPolynomial ι ℤ) (hN : G.totalDegree ≤ N) :
    eval₂ (Int.castRingHom S) v (homog i₀ N G) = v i₀ ^ N * deh v i₀ G := by
  rw [homog, eval₂_sum, deh, coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m.degree ≤ N := le_trans (le_totalDegree hm) hN
  rw [eval₂_monomial, Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
    Finsupp.prod_single_index (by simp)]
  have h1 : (m.prod fun i k => v i ^ k) = ∏ i, v i ^ m i :=
    Finsupp.prod_fintype _ _ (by simp)
  have h2 : ∏ i, (v i / v i₀) ^ m i = (∏ i, v i ^ m i) / v i₀ ^ m.degree := by
    rw [Finset.prod_congr rfl fun i _ => div_pow (v i) (v i₀) (m i), Finset.prod_div_distrib,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
  rw [h1, h2]
  have h3 : v i₀ ^ N = v i₀ ^ (N - m.degree) * v i₀ ^ m.degree := by
    rw [← pow_add]; congr 1; omega
  rw [h3]
  field_simp

theorem aeval_smul_of_isHomogeneous {ι S : Type*} [Fintype ι] [CommRing S]
    {f : MvPolynomial ι ℤ} {d : ℕ} (hf : f.IsHomogeneous d) (c : S) (v : ι → S) :
    aeval (fun i => c * v i) f = c ^ d * aeval v f := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hf (mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem aeval_eq_pow_mul_deh {ι S : Type*} [Fintype ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {n : ℕ} {f : MvPolynomial ι ℤ} (hf : f.IsHomogeneous n) :
    aeval v f = v i₀ ^ n * deh v i₀ f := by
  have h : v = fun i => v i₀ * (v i / v i₀) := by
    funext i; rw [mul_div_cancel₀ _ hv]
  conv_lhs => rw [h]
  rw [aeval_smul_of_isHomogeneous hf]
  rfl

theorem deh_X {ι S : Type*} [Field S] (v : ι → S) (i₀ i : ι) : deh v i₀ (X i) = v i / v i₀ := by
  simp [deh]

theorem deh_eq_zero_of_deh_eq_zero {ι : Type*} [Fintype ι] {Ω : Type*} [Field Ω]
    (x : ι → Ω) (z : ι → ℂ) (i₀ : ι) (hx : x i₀ ≠ 0) (hz : z i₀ ≠ 0)
    (hP : ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0)
    {G : MvPolynomial ι ℤ} (hG : deh x i₀ G = 0) : deh z i₀ G = 0 := by
  classical
  have hH := homog_isHomogeneous i₀ G le_rfl
  have h1 : aeval x (homog i₀ G.totalDegree G) = 0 := by
    rw [aeval_def, algebraMap_int_eq, eval₂_homog x i₀ hx G le_rfl, hG, mul_zero]
  have h2 := hP _ (mem_coordIdeal_of_isHomogeneous ℤ x hH h1)
  rw [eval_map, eval₂_homog z i₀ hz G le_rfl] at h2
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hz)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem deh_apply {ι S : Type*} [Field S] (v : ι → S) (i₀ : ι) (F : MvPolynomial ι ℤ) :
    deh v i₀ F = eval₂ (Int.castRingHom S) (fun i => v i / v i₀) F := rfl

variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ}

structure Gen (x : ι → Ω) (e : Fin (D + 1) → ι) where
  Θ : MvPolynomial ι ℤ
  P : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  monic : P.Monic
  root : P.eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ) = 0
  min : ∀ H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ), H.natDegree < P.natDegree →
    H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ) = 0 → ∀ j, deh (x ∘ e) 0 (H.coeff j) = 0
  dd : MvPolynomial (Fin (D + 1)) ℤ
  dd_ne : deh (x ∘ e) 0 dd ≠ 0
  Q : ι → Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  hQ : ∀ i, deh (x ∘ e) 0 dd * deh x (e 0) (X i) = (Q i).eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ)
  cc : MvPolynomial (Fin (D + 1)) ℤ
  cc_ne : deh (x ∘ e) 0 cc ≠ 0
  U : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  V : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  hUV : (U * P + V * Polynomial.derivative P - Polynomial.C cc).map (deh (x ∘ e) 0) = 0

variable {x : ι → Ω} {e : Fin (D + 1) → ι}

def Gen.evQ (G : Gen x e) {S : Type*} [Field S] (ψ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S) :
    ι → S :=
  fun i => (G.Q i).eval₂ ψ t / ψ G.dd

def Gen.zOf (G : Gen x e) (w : Fin (D + 1) → ℂ) (ρ : ℂ) : ι → ℂ :=
  fun i => w 0 * G.evQ (deh w 0) ρ i

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem coneMap_eq_zero_of_mem_pts {J : Type} [Fintype J] {P : Ideal (MvPolynomial J ℤ)}
    (hP : IsHomogIdeal ℤ P) {z : J → ℂ} (hz : z ∈ pts P) {f : MvPolynomial J ℤ} (hf : f ∈ P) :
    coneMap ℤ z f = 0 := by
  ext d
  rw [coeff_coneMap, Polynomial.coeff_zero]
  have h := hz.2 _ (hP f hf d)
  rw [eval_map] at h
  rw [aeval_def, show algebraMap ℤ ℂ = Int.castRingHom ℂ from Subsingleton.elim _ _]
  exact h

theorem coneMap_rename {J J' : Type} {R : Type*} [CommRing R] [Algebra ℤ R] (x : J → R) (e : J' → J)
    (g : MvPolynomial J' ℤ) : coneMap ℤ x (rename e g) = coneMap ℤ (x ∘ e) g := by
  simp only [coneMap, aeval_rename]
  rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mHom (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℕ) : Submodule ℤ (MRing ι) :=
  Submodule.span ℤ {s | IsMultiHomog s a}

def mPiece (W : Ideal (MRing ι)) (a : K → ℕ) : Submodule ℤ (MRing ι ⧸ W) :=
  (mHom ι a).map (Ideal.Quotient.mkₐ ℤ W).toLinearMap

end

abbrev FinTwoTypeFamily (κ : Type) : Fin 2 → Type := fun _ => κ

variable {Ω : Type} [Field Ω] {κ : Type}

def pair (x x' : Ix κ → Ω) : (Σ k, FinTwoTypeFamily κ k) → Ω :=
  fun p => if p.1 = 0 then x ⟨(), p.2⟩ else x' ⟨(), p.2⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics

structure GDatum (D : ℕ) : Type 1 where

  Ω : Type
  [fieldΩ : Field Ω]
  [charΩ : CharZero Ω]

  κ : Type
  [fintypeκ : Fintype κ]

  x : Ix κ → Ω

  m : ConeMetric (C := ℂ) (ι := Ix κ)

  μ : Measure (Ix κ → ℂ)
  good : IsGood D x m μ

attribute [instance] GDatum.fieldΩ GDatum.charΩ GDatum.fintypeκ

def IsInvMat {J : Type} [Fintype J] (A : Matrix J J ℚ) : Prop :=
  ∃ B : Matrix J J ℚ, ∀ v : J → ℚ, A.mulVec (B.mulVec v) = v ∧ B.mulVec (A.mulVec v) = v

def IsPullFS {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ} (x : Ix κ → Ω)
    (e : Fin (D + 1) → Ix κ) (m : ConeMetric (C := ℂ) (ι := Ix κ)) : Prop :=
  ∀ z ∈ pts (coordIdeal ℤ x), m.ρ z = Real.sqrt (∑ k, ‖z (e k)‖ ^ 2)

def hhOf (I : AllFam) (D : ℕ) : ℝ :=
  I Unit (GlobalTheory (Fin (D + 1))) ⊥ (D + 1) fun _ =>
    HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))

abbrev pw (D : ℕ) : ℕ → ℝ := fun n => (n : ℝ) ^ (D + 1)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def NefOnGeneric (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ geomDeg W A 1

def HeightsNonneg (II : IntersectionSystem) (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ W : Ideal (MRing ι), IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A]

def MoriwakiBigStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤
      arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
