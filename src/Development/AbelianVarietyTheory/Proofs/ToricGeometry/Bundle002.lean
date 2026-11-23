module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

section

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.card_le_pow_of_linearIndependent_theta_principal :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ) (Q : (Fin g → ℂ) → ℂ) (b : Fin g → ℂ), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ (∀ j, b j ≠ 0) ∧ (∀ (i : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (Pi.single i 1) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = cexp (Q (z + Pi.single i 1) - Q z)) ∧ (∀ (j : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (τ.mulVec (Pi.single j 1)) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = b j * cexp (-(2 * Real.pi * I) * z j) * cexp (Q (z + τ.mulVec (Pi.single j 1)) - Q z))) → (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, Differentiable ℂ (f k) ∧ ∀ (l : Λ) z, f k (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f k z) → LinearIndependent ℂ f → N ≤ n ^ g) := by
  intro H1 H2 g Λ hdisc hspan Hm χ Ef hH hpos hχ hEf hbij n hn N f hf hind
  obtain ⟨φ, τ, Q, b, -, -, hΛ, hQd, -, hb, hQ1, hQ2⟩ :=
    H1 g Λ hdisc hspan Hm χ Ef hH hpos hχ hEf hbij
  let T : ((Fin g → ℂ) → ℂ) →ₗ[ℂ] ((Fin g → ℂ) → ℂ) :=
    { toFun := fun h z => h (φ z) * cexp (-((n : ℂ) * Q z))
      map_add' := fun h h' => by funext z; simp [add_mul]
      map_smul' := fun c h => by funext z; simp [mul_assoc] }
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro h hh
    funext w
    have hw := congr_fun hh (φ.symm w)
    change h (φ (φ.symm w)) * cexp (-((n : ℂ) * Q (φ.symm w))) = 0 at hw
    rw [φ.apply_symm_apply] at hw
    exact (mul_eq_zero.mp hw).resolve_right (Complex.exp_ne_zero _)
  refine H2 g n τ b hn hb N (T ∘ f) (fun k => ⟨?_, fun i z => ?_, fun j z => ?_⟩) (hind.map' T hT)
  · change Differentiable ℂ (fun z => f k (φ z) * cexp (-((n : ℂ) * Q z)))
    have hφd : Differentiable ℂ (LinearMap.toContinuousLinearMap φ.toLinearMap) :=
      (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable
    exact ((hf k).1.comp hφd).mul ((hQd.const_mul _).neg.cexp)
  · change f k (φ (z + Pi.single i 1)) * cexp (-((n : ℂ) * Q (z + Pi.single i 1))) =
      f k (φ z) * cexp (-((n : ℂ) * Q z))
    have hs : (fun j => (((Pi.single i 1 : Fin g → ℤ) j : ℤ) : ℂ)) = Pi.single i 1 := by
      ext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj]
    have hmem : φ (Pi.single i 1) ∈ Λ := (hΛ _).mpr ⟨Pi.single i 1, 0, by
      rw [hs]; ext j; simp [Matrix.mulVec, dotProduct]⟩
    obtain ⟨l, hl⟩ : ∃ l : Λ, (l : Fin g → ℂ) = φ (Pi.single i 1) := ⟨⟨_, hmem⟩, rfl⟩
    rw [map_add (f := _), ← hl, (hf k).2 l, hQ1 i l z hl, ← Complex.exp_nat_mul]
    have key : cexp (↑n * (Q (z + Pi.single i 1) - Q z)) * cexp (-(↑n * Q (z + Pi.single i 1))) =
        cexp (-(↑n * Q z)) := by
      rw [← Complex.exp_add]; congr 1; ring
    linear_combination f k (φ z) * key
  · change f k (φ (z + τ *ᵥ Pi.single j 1)) * cexp (-((n : ℂ) * Q (z + τ *ᵥ Pi.single j 1))) =
      b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k (φ z) * cexp (-((n : ℂ) * Q z)))
    have hs : (fun i => (((Pi.single j 1 : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j 1 := by
      ext i; by_cases hi : i = j <;> simp [Pi.single_apply, hi]
    have hmem : φ (τ *ᵥ Pi.single j 1) ∈ Λ := (hΛ _).mpr ⟨0, Pi.single j 1, by
      rw [hs]; ext i; simp⟩
    obtain ⟨l, hl⟩ : ∃ l : Λ, (l : Fin g → ℂ) = φ (τ *ᵥ Pi.single j 1) := ⟨⟨_, hmem⟩, rfl⟩
    rw [map_add (f := _), ← hl, (hf k).2 l, hQ2 j l z hl, mul_pow, mul_pow, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul]
    have key : cexp (↑n * (-(2 * ↑Real.pi * I) * z j)) *
        cexp (↑n * (Q (z + τ *ᵥ Pi.single j 1) - Q z)) *
        cexp (-(↑n * Q (z + τ *ᵥ Pi.single j 1))) =
        cexp (-(2 * ↑Real.pi * I) * ↑n * z j) * cexp (-(↑n * Q z)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    linear_combination (b j ^ n * f k (φ z)) * key

end GlobalTheory
end

section

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ClassicalTheta

theorem forall_of_box_of_translate {g n : ℕ} (hn : 1 ≤ n) (P : (Fin g → ℤ) → Prop)
    (hP : ∀ m j, P (m + Pi.single j (n : ℤ)) ↔ P m)
    (hbox : ∀ r : Fin g → Fin n, P (fun i => ((r i : ℕ) : ℤ))) (m : Fin g → ℤ) : P m := by
  have h1 : ∀ (j : Fin g) (k : ℤ) (m : Fin g → ℤ), P (m + Pi.single j (k * n)) ↔ P m := by
    intro j k
    induction k using Int.induction_on with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      have : m + Pi.single j (((k : ℤ) + 1) * n) =
          (m + Pi.single j ((k : ℤ) * n)) + Pi.single j (n : ℤ) := by
        rw [add_assoc, ← Pi.single_add]; congr 2; ring
      rw [this, hP, ih]
    | pred k ih =>
      intro m
      have : m + Pi.single j ((-(k : ℤ)) * n) =
          (m + Pi.single j ((-(k : ℤ) - 1) * n)) + Pi.single j (n : ℤ) := by
        rw [add_assoc, ← Pi.single_add]; congr 2; ring
      rw [← ih m, this, hP]
  have h2 : ∀ (k : Fin g → ℤ) (s : Finset (Fin g)) (m : Fin g → ℤ),
      P (m + ∑ j ∈ s, Pi.single j (k j * n)) ↔ P m := by
    intro k s
    induction s using Finset.induction_on with
    | empty => intro m; simp
    | insert a s ha ih =>
      intro m
      rw [Finset.sum_insert ha, add_comm (Pi.single a _), ← add_assoc, h1, ih]
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  let r : Fin g → Fin n := fun i => ⟨(m i % n).toNat, by
    have h0 := Int.emod_nonneg (m i) hn'.ne'
    have h1 := Int.emod_lt_of_pos (m i) hn'
    omega⟩
  have hm : m = (fun i => ((r i : ℕ) : ℤ)) + ∑ j, Pi.single j (m j / n * n) := by
    rw [Finset.univ_sum_single (fun j => m j / n * n)]
    funext i
    have h0 := Int.emod_nonneg (m i) hn'.ne'
    simp only [r, Pi.add_apply, Int.toNat_of_nonneg h0]
    have := Int.emod_add_mul_ediv (m i) n
    linarith
  rw [hm, h2]
  exact hbox r

theorem card_le_pow_of_linearIndependent :
    (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → ∀ (m : Fin g → ℤ) (w : Fin g → ℂ), (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) * (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ)))) → (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) → f = 0) → (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) := by
  intro hshift huniq g n τ b hn hb N f hf hli
  let c : ((Fin g → ℂ) → ℂ) → (Fin g → ℤ) → ℂ := fun F m =>
    ∫ x in Set.Icc (0 : Fin g → ℝ) 1, F (fun i => (x i : ℂ)) *
      cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))
  have key : ∀ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F →
      (∀ (i : Fin g) z, F (z + Pi.single i 1) = F z) →
      (∀ (j : Fin g) z, F (z + τ.mulVec (Pi.single j 1)) =
        b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * F z) →
      (∀ r : Fin g → Fin n, c F (fun i => ((r i : ℕ) : ℤ)) = 0) → F = 0 := by
    intro F hd hp hl hbox
    refine huniq g F hd hp (forall_of_box_of_translate hn (fun m => c F m = 0) ?_ hbox)
    intro m j
    have h := hshift g F hd hp m (τ.mulVec (Pi.single j 1))
    have h' : (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
        F ((fun i => (x i : ℂ)) + τ.mulVec (Pi.single j 1)) *
          cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) =
        b j ^ n * c F (m + Pi.single j (n : ℤ)) := by
      simp only [c]
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext x
      have hs : ∑ i, (((m + Pi.single j (n : ℤ) : Fin g → ℤ) i : ℤ) : ℂ) * (x i : ℂ) =
          n * (x j : ℂ) + ∑ i, (m i : ℂ) * (x i : ℂ) := by
        simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · simp
      rw [hl, hs, mul_add, Complex.exp_add, mul_assoc (-(2 * Real.pi * I) : ℂ)]
      ring
    rw [h'] at h
    change _ = _ * c F m at h
    have hb' : b j ^ n ≠ 0 := pow_ne_zero _ (hb j)
    constructor
    · intro h0
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.1 h.symm).resolve_left (Complex.exp_ne_zero _)
    · intro h0
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.1 h).resolve_left hb'
  let v : Fin N → (Fin g → Fin n) → ℂ := fun k r => c (f k) (fun i => ((r i : ℕ) : ℤ))
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro a ha
    apply hli a
    apply key
    · exact Differentiable.sum fun k _ => (hf k).1.const_smul (a k)
    · intro i z
      simp only [Finset.sum_apply, Pi.smul_apply, (hf _).2.1]
    · intro j z
      simp only [Finset.sum_apply, Pi.smul_apply, (hf _).2.2, Finset.mul_sum, smul_eq_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    · intro r
      have har := congrFun ha r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v, c] at har
      rw [← har]
      simp only [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← MeasureTheory.integral_const_mul]
        simp only [mul_assoc]
      · intro k _
        have hk := (hf k).1.continuous
        refine ContinuousOn.integrableOn_Icc (Continuous.continuousOn ?_)
        fun_prop
  have := hv.fintype_card_le_finrank
  simpa using this

end GlobalTheory.ClassicalTheta
end

section

open Complex Matrix Filter Topology
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory

theorem apply_add_intCast_of_periodic_single {g : ℕ} {β : Type*} {A : (Fin g → ℝ) → β}
    (hA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x) (n : Fin g → ℤ) (x : Fin g → ℝ) :
    A (x + fun i => (n i : ℝ)) = A x := by
  have h1 : (fun i => (n i : ℝ)) = ∑ i, n i • (Pi.single i 1 : Fin g → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h1]
  have h2 : ∀ s : Finset (Fin g),
      Function.Periodic A (∑ i ∈ s, n i • (Pi.single i 1 : Fin g → ℝ)) := fun s => by
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Function.Periodic.zsmul (hA a) (n a)).add_period ih
  exact h2 _ x

theorem eq_zero_of_cube_fourierCoeff_eq_zero {g : ℕ} {A : (Fin g → ℝ) → ℂ} (hc : Continuous A)
    (hA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x)
    (h : ∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) (y : Fin g → ℝ) :
    A y = 0 := by
  set p : (Fin g → ℝ) → UnitAddTorus (Fin g) := fun x i ↦ (x i : UnitAddCircle) with hp
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  set f₀ : UnitAddTorus (Fin g) → ℂ := fun z ↦ A (Function.surjInv hq.surjective z) with hf₀
  have hfp : ∀ x, f₀ (p x) = A x := fun x ↦ by
    set x' := Function.surjInv hq.surjective (p x)
    have h1 : p x' = p x := Function.surjInv_eq _ _
    have h2 : ∀ i, ∃ n : ℤ, (n : ℝ) = x' i - x i := fun i ↦ by
      have h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]; exact congrFun h1 i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
      exact ⟨n, by simpa using hn⟩
    choose n hn using h2
    rw [← apply_add_intCast_of_periodic_single hA n x]
    change A x' = _
    congr 1
    funext i
    simp [hn]
  let f : C(UnitAddTorus (Fin g), ℂ) := ⟨f₀,
    hq.isQuotientMap.continuous_iff.2 <| by
      rw [show f₀ ∘ p = A from funext hfp]; exact hc⟩
  have hchar : ∀ n x, UnitAddTorus.mFourier (-n) (p x) =
      cexp (-(2 * Real.pi * I) * ∑ i, (n i : ℂ) * (x i : ℂ)) := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  have hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = 0 := fun n ↦ by
    rw [UnitAddTorus.mFourierCoeff_eq_integral f n 0, ← h n]
    simp only [Pi.zero_apply, zero_add]
    have h2 : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ fun i ↦ Set.Ioc ((0 : Fin g → ℝ) i) ((1 : Fin g → ℝ) i) := by
      ext x; simp
    rw [h2, MeasureTheory.setIntegral_congr_set
      (μ := MeasureTheory.volume) MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
    change UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _
    simp only [hchar, hfp, smul_eq_mul, mul_comm]
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f)
    (by rw [funext hcoeff]; exact summable_zero) (p y)
  change HasSum _ (f₀ (p _)) at hsum
  simp only [hcoeff, zero_smul, hfp] at hsum
  exact hsum.unique hasSum_zero

theorem entire_periodic_eq_zero_of_fourierCoeff_eq_zero :
    (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → ∀ (m : Fin g → ℤ) (w : Fin g → ℂ), (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) * (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ)))) → (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) → f = 0) := by
  intro H g f hf hper h0
  funext w
  have hc := hf.continuous
  have := eq_zero_of_cube_fourierCoeff_eq_zero (A := fun x => f ((fun i => (x i : ℂ)) + w))
    (by fun_prop) (fun i x => by
      rw [← hper i ((fun i => (x i : ℂ)) + w)]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp; ring
      · simp [hj])
    (fun m => by rw [H g f hf hper m w, h0 m, mul_zero]) 0
  have h1 : (fun i => (((0 : Fin g → ℝ) i : ℝ) : ℂ)) + w = w := by
    funext j; simp
  rw [h1] at this
  exact this

end GlobalTheory
end
end
