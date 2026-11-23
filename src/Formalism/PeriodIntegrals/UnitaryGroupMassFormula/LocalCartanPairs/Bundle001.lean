module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

noncomputable section
open Matrix

namespace PI.SqPair.LCP

section Defs
variable {R : Type} [CommRing R] [StarRing R]

def hf {ι : Type} [Fintype ι] (A : Matrix ι ι R) (x y : ι → R) : R := star x ⬝ᵥ (A *ᵥ y)

def Unimod {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) : Prop :=
  Aᴴ = A ∧ IsUnit A.det

def hyp : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

structure Inert (R₀ : Subring R) (ϖ : R) : Prop where
  fix : ∀ x, x ∈ R₀ ↔ star x = x
  unr : ∃ θ : R, IsUnit (θ - star θ)
  pi_mem : ϖ ∈ R₀
  pi_ne : ϖ ≠ 0
  pi_nonunit : ¬ IsUnit ϖ
  dom : IsDomain R
  val : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u

def PHyp {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : R) (A A' h : Matrix ι ι R) (k : ℕ) : Prop :=
  Unimod A ∧ Unimod A' ∧ hᴴ * A * h = (ϖ ^ (2 * k)) • A'

def PConcl {ι : Type} [Fintype ι] [DecidableEq ι] (A h : Matrix ι ι R) : Prop :=
  ∃ e f : Matrix ι ι R, e * e = e ∧ eᴴ * A = A * (1 - e) ∧ e * h = h * f

def PGen (ϖ : R) (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (A A' h : Matrix ι ι R) (k : ℕ), PHyp ϖ A A' h k → PConcl A h

def IsBase {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : R) (h : Matrix ι ι R) (k : ℕ) : Prop :=
  ∃ h₁ : Matrix ι ι R, IsUnit h₁.det ∧ h = (ϖ ^ k) • h₁

def StepOut {κ : Type} [Fintype κ] [DecidableEq κ] (A A' h : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) :
    Prop :=
  ∃ (u u' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (A₁ A₁' h₂ : Matrix κ κ R) (d : Fin 2 → R),
    IsUnit u.det ∧ IsUnit u'.det ∧ uᴴ * A * u = fromBlocks hyp 0 0 A₁ ∧
    u'ᴴ * A' * u' = fromBlocks hyp 0 0 A₁' ∧ h * u' = u * fromBlocks (diagonal d) 0 0 h₂

end Defs

def Dichotomy : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R), (∀ x, x ∈ R₀ ↔ star x = x) →
    ∀ [IsDomain R₀] [IsDiscreteValuationRing R₀] [HenselianLocalRing R₀]
      [Finite (IsLocalRing.ResidueField R₀)],
    (∃ θ : R, IsUnit (θ - star θ)) → ∀ ϖ : R₀, Irreducible ϖ →
    (∃ ε : R, ε * ε = ε ∧ star ε = 1 - ε) ∨ Inert R₀ (ϖ : R)

def BaseLag : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) [HenselianLocalRing R₀]
    [Finite (IsLocalRing.ResidueField R₀)] (ϖ : R), Inert R₀ ϖ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Even (Fintype.card κ) →
    ∀ A : Matrix κ κ R, Unimod A → ∃ e : Matrix κ κ R, e * e = e ∧ eᴴ * A = A * (1 - e)

def Select : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) (ϖ : R), Inert R₀ ϖ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A A' h : Matrix ι ι R) (k : ℕ),
    PHyp ϖ A A' h k → ¬ IsBase ϖ h k →
    ∃ (a : ℕ) (x y : ι → R), 0 < a ∧ a ≤ k ∧ hf A x y = 1 ∧
      (∃ c, hf A x x = ϖ ^ (2 * a) * c) ∧
      (∃ v, h *ᵥ v = ϖ ^ (k - a) • x) ∧ (∃ w, h *ᵥ w = ϖ ^ (k + a) • y)

def Plane : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) [HenselianLocalRing R₀] (ϖ : R),
    Inert R₀ ϖ → ∀ α β : R₀, α ∈ IsLocalRing.maximalIdeal R₀ →
    ∃ w : Matrix (Fin 2) (Fin 2) R, IsUnit w.det ∧
      wᴴ * !![(α : R), 1; 1, (β : R)] * w = hyp ∧ ∃ s' : R, w 1 0 = (α : R) * s'

def SplitOff : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] [IsLocalRing R]
    (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ],
    Fintype.card κ + 2 = Fintype.card ι →
    ∀ (A : Matrix ι ι R), Aᴴ = A → ∀ x y : ι → R, hf A x x = 0 → hf A y y = 0 → hf A x y = 1 →
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks hyp 0 0 A₁

def Split : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) (ϖ : R), Inert R₀ ϖ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A A' h : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R)
      (k a : ℕ), PHyp ϖ A A' h k → a ≤ k →
    ∀ x y v w : Fin 2 ⊕ κ → R, hf A x x = 0 → hf A y y = 0 → hf A x y = 1 →
      h *ᵥ v = ϖ ^ (k - a) • x → h *ᵥ w = ϖ ^ (k + a) • y → StepOut A A' h

def Step : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) [HenselianLocalRing R₀] (ϖ : R),
    Inert R₀ ϖ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A A' h : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (k : ℕ),
    PHyp ϖ A A' h k → ¬ IsBase ϖ h k → StepOut A A' h

end PI.SqPair.LCP
end
end

section

noncomputable section

namespace PI.SqPair.LCP

open Polynomial IsLocalRing Matrix

theorem plane_isUnit_of_sub_one_mem {A : Type*} [CommRing A] [IsLocalRing A] {x : A}
    (h : x - 1 ∈ maximalIdeal A) : IsUnit x := by
  by_contra hx
  have hxm : x ∈ maximalIdeal A := (mem_maximalIdeal x).2 hx
  have h1 : (1 : A) ∈ maximalIdeal A := by
    have h2 := sub_mem hxm h
    rwa [sub_sub_cancel] at h2
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem plane_core {R : Type*} [CommRing R] (σ : R ≃+* R) (α β t s c : R)
    (hα : σ α = α) (h1 : β + t + σ t + t * σ t * α = 0)
    (h2 : s * (1 + t * α) + σ s * (1 + σ t * α) = -α) (h3 : c * (1 + t * α) = 1) :
    ((!![1 + s * t, c * t; s, c] : Matrix (Fin 2) (Fin 2) R).map σ)ᵀ * !![α, 1; 1, β]
        * !![1 + s * t, c * t; s, c] = !![0, 1; 1, 0] ∧
      (!![1 + s * t, c * t; s, c] : Matrix (Fin 2) (Fin 2) R).det = c := by
  have h3σ : σ c * (1 + σ t * α) = 1 := by
    have h4 := congrArg σ h3
    simpa only [map_mul, map_add (f := _), map_one, hα] using h4
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), map_mul, map_one]
    · linear_combination h2 + σ s * s * h1
    · linear_combination h3 + σ s * c * h1
    · linear_combination h3σ + σ c * s * h1
    · linear_combination σ c * c * h1
  · simp [Matrix.det_fin_two]
    ring

theorem plane_exists {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x)
    (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x) [HenselianLocalRing R₀]
    (τ : R) (hτ : τ + σ τ = 1) (α β : R₀) (hα : α ∈ maximalIdeal R₀) :
    ∃ t s c : R, β + t + σ t + t * σ t * α = 0 ∧
      s * (1 + t * α) + σ s * (1 + σ t * α) = -α ∧ c * (1 + t * α) = 1 ∧ ∃ s', s = α * s' := by
  have hfix : ∀ x : R₀, σ (x : R) = x := fun x => (hR₀ x).1 x.2
  have hNfix : σ (τ * σ τ) = τ * σ τ := by rw [map_mul, hσ, mul_comm]
  let N : R₀ := ⟨τ * σ τ, (hR₀ _).2 hNfix⟩
  have hN : (N : R) = τ * σ τ := rfl
  obtain ⟨w, hwroot, hw1⟩ := HenselianLocalRing.is_henselian (X ^ 2 - X + C (α * N * β))
    (by monicity!) 1
    (by
      simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, one_pow, sub_self, zero_add]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hα))
    (by
      simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_X, derivative_C,
        eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one, eval_zero]
      norm_num)
  have hr : w ^ 2 - w + α * N * β = 0 := by
    have h0 := hwroot.eq_zero
    simpa only [eval_add, eval_sub, eval_pow, eval_X, eval_C] using h0
  obtain ⟨wu, rfl⟩ := plane_isUnit_of_sub_one_mem hw1
  have hwv : (wu : R₀) * ↑wu⁻¹ = 1 := wu.mul_inv
  let x : R₀ := -β * ↑wu⁻¹
  have hx : β + x + α * N * x ^ 2 = 0 := by
    linear_combination (β * (↑wu⁻¹ : R₀) ^ 2) * hr -
      (β + β * ↑wu⁻¹ * ↑wu - β * ↑wu⁻¹) * hwv
  have hxR : (β : R) + x + α * (τ * σ τ) * (x : R) ^ 2 = 0 := by
    have h0 := congrArg (fun y : R₀ => (y : R)) hx
    simpa only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow, hN, ZeroMemClass.coe_zero]
      using h0
  let nR : R₀ := 1 + x * α + N * x ^ 2 * α ^ 2
  have hnm : nR - 1 ∈ maximalIdeal R₀ := by
    have e : nR - 1 = α * (x + N * x ^ 2 * α) := by ring
    rw [e]
    exact Ideal.mul_mem_right _ _ hα
  obtain ⟨nu, hnu⟩ := plane_isUnit_of_sub_one_mem hnm
  have hninv : ((nR : R₀) : R) * ((↑nu⁻¹ : R₀) : R) = 1 := by
    have h0 := congrArg (fun y : R₀ => (y : R)) nu.mul_inv
    simpa only [hnu, Subring.coe_mul, OneMemClass.coe_one] using h0
  set t : R := τ * x with ht
  have hσt : σ t = σ τ * x := by rw [ht, map_mul, hfix]
  have hnR : (1 + t * α) * (1 + σ t * α) = ((nR : R₀) : R) := by
    rw [hσt, ht]
    simp only [nR]
    push_cast
    linear_combination ((x : R) * α) * hτ - ((x : R) ^ 2 * (α : R) ^ 2) * hN
  set c : R := (1 + σ t * α) * ((↑nu⁻¹ : R₀) : R) with hc
  have h3 : c * (1 + t * α) = 1 := by
    rw [hc]
    linear_combination ((↑nu⁻¹ : R₀) : R) * hnR + hninv
  have hσc : σ c = (1 + t * α) * ((↑nu⁻¹ : R₀) : R) := by
    rw [hc, map_mul, map_add (f := _), map_one, map_mul, hσ, hfix, hfix]
  refine ⟨t, -((α : R) * τ * c), c, ?_, ?_, h3, -(τ * c), by ring⟩
  · rw [hσt, ht]
    linear_combination hxR + (x : R) * hτ
  · rw [map_neg, map_mul, map_mul, hfix, hσc]
    linear_combination (-((α : R) * τ)) * h3 + (-((α : R) * σ τ * ((↑nu⁻¹ : R₀) : R))) * hnR +
      (-((α : R) * σ τ)) * hninv + (-(α : R)) * hτ

theorem plane_w {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x)
    (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x) [HenselianLocalRing R₀]
    (τ : R) (hτ : τ + σ τ = 1) (α β : R₀) (hα : α ∈ maximalIdeal R₀) :
    ∃ w : Matrix (Fin 2) (Fin 2) R, IsUnit w.det ∧
      (w.map σ)ᵀ * !![(α : R), 1; 1, (β : R)] * w = !![0, 1; 1, 0] ∧ ∃ s', w 1 0 = (α : R) * s' := by
  obtain ⟨t, s, c, h1, h2, h3, s', hs'⟩ := plane_exists σ hσ R₀ hR₀ τ hτ α β hα
  obtain ⟨hform, hdet⟩ := plane_core σ (α : R) (β : R) t s c ((hR₀ _).1 α.2) h1 h2 h3
  refine ⟨!![1 + s * t, c * t; s, c], ?_, hform, s', ?_⟩
  · rw [hdet]
    exact IsUnit.of_mul_eq_one _ h3
  · simp [hs']

theorem tau_of_theta {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x) (θ : R)
    (hθ : IsUnit (θ - σ θ)) : ∃ τ : R, τ + σ τ = 1 := by
  obtain ⟨u, hu⟩ := hθ
  refine ⟨θ * ↑u⁻¹, ?_⟩
  have hσu : σ (↑u : R) = -↑u := by rw [hu, map_sub, hσ]; ring
  have h2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  have hσinv : σ (↑u⁻¹ : R) = -↑u⁻¹ := by
    have h1 : σ (↑u : R) * σ (↑u⁻¹ : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [hσu] at h1
    linear_combination (-σ (↑u⁻¹ : R)) * h2 + (-(↑u⁻¹ : R)) * h1
  rw [map_mul, hσinv]
  rw [hu] at h2
  linear_combination h2

end PI.SqPair.LCP
end
end

section

noncomputable section
open Matrix

namespace PI.SqPair.LCP

variable {R : Type} [CommRing R] [IsDomain R]

theorem sel_factor (ϖ : R) (hϖ0 : ϖ ≠ 0)
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι κ : Type} (h : Matrix ι κ R) (hh : h ≠ 0) :
    ∃ (m : ℕ) (h₁ : Matrix ι κ R) (i : ι) (j : κ), h = ϖ ^ m • h₁ ∧ IsUnit (h₁ i j) := by
  classical
  have hex : ∃ n : ℕ, ∃ i j, h i j ≠ 0 ∧ ∃ u : R, IsUnit u ∧ h i j = ϖ ^ n * u := by
    by_contra hne
    apply hh
    ext i j
    rw [Matrix.zero_apply]
    by_contra hij
    obtain ⟨n, u, hu, he⟩ := hval _ hij
    exact hne ⟨n, i, j, hij, u, hu, he⟩
  obtain ⟨i₀, j₀, _, u₀, hu₀, he₀⟩ := Nat.find_spec hex
  have hdiv : ∀ i j, ∃ z : R, h i j = ϖ ^ Nat.find hex * z := by
    intro i j
    by_cases hij : h i j = 0
    · exact ⟨0, by rw [hij, mul_zero]⟩
    · obtain ⟨n, u, hu, he⟩ := hval _ hij
      have hmn : Nat.find hex ≤ n := Nat.find_min' hex ⟨i, j, hij, u, hu, he⟩
      refine ⟨ϖ ^ (n - Nat.find hex) * u, ?_⟩
      rw [he, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
  choose h₁ hh₁ using hdiv
  refine ⟨Nat.find hex, Matrix.of h₁, i₀, j₀, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact hh₁ i j
  · have e : h₁ i₀ j₀ = u₀ :=
      mul_left_cancel₀ (pow_ne_zero _ hϖ0) ((hh₁ i₀ j₀).symm.trans he₀)
    simp only [Matrix.of_apply, e]
    exact hu₀

theorem sel_star_smul (σ : R ≃+* R) (ϖ : R) (hσϖ : σ ϖ = ϖ) (m : ℕ) {ι κ : Type}
    (h : Matrix ι κ R) : ((ϖ ^ m • h).map σ)ᵀ = ϖ ^ m • (h.map σ)ᵀ := by
  ext i j
  simp [Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hσϖ]

theorem sel_smul_cancel {ι κ : Type} {c : R} (hc : c ≠ 0) {X Y : Matrix ι κ R}
    (h : c • X = c • Y) : X = Y := by
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h'
  exact mul_left_cancel₀ hc h'

theorem sel_le (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) (m k : ℕ)
    (hrel : ((ϖ ^ m • h₁).map σ)ᵀ * A * (ϖ ^ m • h₁) = ϖ ^ (2 * k) • A') :
    m ≤ k ∧ (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' := by
  have hB : ϖ ^ (2 * m) • ((h₁.map σ)ᵀ * A * h₁) = ϖ ^ (2 * k) • A' := by
    rw [← hrel, sel_star_smul σ ϖ hσϖ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, two_mul]
  have hp0 : ∀ t : ℕ, ϖ ^ t ≠ 0 := fun t => pow_ne_zero _ hϖ0
  by_cases hmk : m ≤ k
  · refine ⟨hmk, sel_smul_cancel (hp0 (2 * m)) ?_⟩
    rw [hB, smul_smul, ← pow_add]
    congr 2
    omega
  · exfalso
    push_neg at hmk
    have h2 : ϖ ^ (2 * k) • (ϖ ^ (2 * (m - k)) • ((h₁.map σ)ᵀ * A * h₁)) = ϖ ^ (2 * k) • A' := by
      rw [smul_smul, ← pow_add, ← hB]
      congr 2
      omega
    have h3 := sel_smul_cancel (hp0 (2 * k)) h2
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_smul] at h4
    rw [← h4] at hA'
    have h5 : IsUnit ((ϖ ^ (2 * (m - k))) ^ Fintype.card ι) := isUnit_of_mul_isUnit_left hA'
    rw [← pow_mul] at h5
    have hpos : 2 * (m - k) * Fintype.card ι ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.mul_pos (by omega) Fintype.card_pos)
    exact hϖ ((isUnit_pow_iff hpos).mp h5)

theorem sel_unit_of_rel (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = A') : IsUnit h₁.det := by
  have e := congrArg Matrix.det hrel
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hA'
  exact isUnit_of_mul_isUnit_right hA'

theorem sel_comm {ι : Type} [Fintype ι] [DecidableEq ι] {c : R} (hc : c ≠ 0)
    (g h : Matrix ι ι R) (hgh : g * h = c • 1) : h * g = c • 1 := by
  have hdet : g.det * h.det = c ^ Fintype.card ι := by
    rw [← Matrix.det_mul, hgh, Matrix.det_smul, Matrix.det_one, mul_one]
  have hh0 : h.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero _ hc hdet.symm
  have key : (h * g - c • 1) * h = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hgh, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self]
  have key2 : h.det • (h * g - c • 1) = 0 := by
    have e := congrArg (· * h.adjugate) key
    simp only [Matrix.zero_mul] at e
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e
    exact e
  have e0 : h * g - c • 1 = 0 := by
    ext i j
    have e := congrFun (congrFun key2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e ⊢
    exact (mul_eq_zero.mp e).resolve_left hh0
  exact sub_eq_zero.mp e0

theorem sel_inv (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) {c : R} (hc : c ≠ 0)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = c • A') :
    (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 ∧ h₁ * (A'⁻¹ * (h₁.map σ)ᵀ * A) = c • 1 := by
  have h1 : (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ A h₁, hrel, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ hA']
  exact ⟨h1, sel_comm hc _ _ h1⟩

theorem sel_dual (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : IsUnit A.det) (x : ι → R) (i : ι) (hx : IsUnit (x i)) :
    ∃ y : ι → R, (fun l => σ (x l)) ⬝ᵥ (A *ᵥ y) = 1 := by
  obtain ⟨u, hu⟩ := hx.map σ
  refine ⟨A⁻¹ *ᵥ Pi.single i (↑u⁻¹ : R), ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec, dotProduct_single]
  simp [← hu]

theorem sel_form (σ : R ≃+* R) {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (M : Matrix ι κ R) (v w : κ → R) :
    (fun l => σ ((M *ᵥ v) l)) ⬝ᵥ (A *ᵥ (M *ᵥ w)) =
      (fun l => σ (v l)) ⬝ᵥ (((M.map σ)ᵀ * A * M) *ᵥ w) := by
  have e : (fun l => σ ((M *ᵥ v) l)) = (M.map σ) *ᵥ (fun l => σ (v l)) := by
    funext l
    exact RingHom.map_mulVec (σ : R →+* R) M v l
  rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end PI.SqPair.LCP
end
end
