module

public import Formalism.SatakeDualWeyl.Statement
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

@[expose] public section

section

namespace Formalism.L2.G.Cmp

open Formalism.UG

structure Fib {G Gp : Type} [Group G] [Group Gp] (K K' : Subgroup G) (Kp : Subgroup Gp) where
  j : Gp →* G
  pr : G →* Gp
  pr_j : ∀ g, pr (j g) = g
  j_mem : ∀ g, j g ∈ K'
  K_iff : ∀ x, x ∈ K ↔ x ∈ K' ∧ pr x ∈ Kp

namespace Fib

variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)

def mkC (S : Subgroup G) (a : G) : ClassSet H S :=
  Quotient.mk'' a

theorem mk_eq_iff (S : Subgroup G) (a b : G) :
    (mkC H S a = mkC H S b) ↔ ∃ h ∈ H, ∃ κ ∈ S, b = h * a * κ := by
  unfold mkC
  exact @DoubleCoset.eq _ _ _ _ a b

theorem K'_split (x : G) (hx : x ∈ K') : (X.j (X.pr x))⁻¹ * x ∈ K := by
  rw [X.K_iff]
  refine ⟨K'.mul_mem (K'.inv_mem (X.j_mem _)) hx, ?_⟩
  rw [map_mul, map_inv, X.pr_j, inv_mul_cancel]
  exact Kp.one_mem

variable (y : ClassSet H K' → G) (hy : ∀ i, mkC H K' (y i) = i) (hp : ∀ i, X.pr (y i) = 1)


include hy hp in
theorem cls_iff (i i' : ClassSet H K') (g g' : Gp)
    (hy : ∀ i, mkC H K' (y i) = i) (hp : ∀ i, X.pr (y i) = 1) :
    mkC H K (y i * X.j g) = mkC H K (y i' * X.j g') ↔
      i = i' ∧ ∃ γ ∈ H, (y i)⁻¹ * γ * y i ∈ K' ∧ g'⁻¹ * (X.pr γ * g) ∈ Kp := by
  rw [mk_eq_iff]
  constructor
  · rintro ⟨h, hh, κ, hκ, he⟩
    have hκ' := (X.K_iff κ).1 hκ
    have hi : i = i' := by
      rw [← hy i, ← hy i', mk_eq_iff]
      refine ⟨h, hh, X.j g * κ * (X.j g')⁻¹,
        K'.mul_mem (K'.mul_mem (X.j_mem g) hκ'.1) (K'.inv_mem (X.j_mem g')), ?_⟩
      calc y i' = (y i' * X.j g') * (X.j g')⁻¹ := by group
        _ = h * (y i * X.j g) * κ * (X.j g')⁻¹ := by rw [he]
        _ = h * y i * (X.j g * κ * (X.j g')⁻¹) := by group
    subst hi
    have hh' : h = (y i * X.j g') * κ⁻¹ * (y i * X.j g)⁻¹ := by rw [he]; group
    have hz : (y i)⁻¹ * h * y i = X.j g' * κ⁻¹ * (X.j g)⁻¹ := by rw [hh']; group
    refine ⟨rfl, h, hh, ?_, ?_⟩
    · rw [hz]
      exact K'.mul_mem (K'.mul_mem (X.j_mem _) (K'.inv_mem hκ'.1)) (K'.inv_mem (X.j_mem _))
    · rw [hh']
      simp only [map_mul, map_inv, X.pr_j, hp]
      convert Kp.inv_mem hκ'.2 using 1
      group
  · rintro ⟨rfl, γ, hγ, hz, hg⟩
    refine ⟨γ, hγ, (y i * X.j g)⁻¹ * γ⁻¹ * (y i * X.j g'), ?_, by group⟩
    rw [X.K_iff]
    have e : (y i * X.j g)⁻¹ * γ⁻¹ * (y i * X.j g') =
        (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i)⁻¹ * X.j g' := by group
    rw [e]
    refine ⟨K'.mul_mem (K'.mul_mem (K'.inv_mem (X.j_mem _)) (K'.inv_mem hz)) (X.j_mem _), ?_⟩
    simp only [map_mul, map_inv, X.pr_j, hp]
    convert Kp.inv_mem hg using 1
    group


include hy in
theorem cls_surj (x : G) (hy : ∀ i, mkC H K' (y i) = i) :
    ∃ i g, mkC H K (y i * X.j g) = mkC H K x := by
  obtain ⟨h, hh, κ, hκ, he⟩ := (mk_eq_iff H K' (y (mkC H K' x)) x).1 (hy _)
  refine ⟨mkC H K' x, X.pr κ, (mk_eq_iff H K _ _).2
    ⟨h, hh, (X.j (X.pr κ))⁻¹ * κ, X.K'_split κ hκ, ?_⟩⟩
  conv_lhs => rw [he]
  group


include hp in
theorem stab_iff (i : ClassSet H K') (g : Gp) (γ : G)
    (hp : ∀ i, X.pr (y i) = 1) :
    (y i * X.j g)⁻¹ * γ * (y i * X.j g) ∈ K ↔ (y i)⁻¹ * γ * y i ∈ K' ∧ g⁻¹ * (X.pr γ * g) ∈ Kp := by
  have hz : (y i * X.j g)⁻¹ * γ * (y i * X.j g) = (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g := by
    group
  rw [hz, X.K_iff]
  have hjg := X.j_mem g
  have h1 : (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g ∈ K' ↔ (y i)⁻¹ * γ * y i ∈ K' := by
    constructor
    · intro h
      have h2 := K'.mul_mem (K'.mul_mem hjg h) (K'.inv_mem hjg)
      have e : X.j g * ((X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g) * (X.j g)⁻¹ =
          (y i)⁻¹ * γ * y i := by group
      rwa [e] at h2
    · intro h
      exact K'.mul_mem (K'.mul_mem (K'.inv_mem hjg) h) hjg
  rw [h1]
  simp only [map_mul, map_inv, X.pr_j, hp, inv_one, one_mul, mul_one, mul_assoc]

end Fib

end Formalism.L2.G.Cmp
end

section

noncomputable section

open Matrix Formalism.UG

namespace Formalism.L2.G.Cmp

variable {T K : Type} [CommRing T] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
  (φ : T ≃+* K × K) (σ : T →+* T) (hσ : ∀ t, φ (σ t) = swapR K (φ t)) (Ov : Subring K) (S : Subring T)
  (hS : ∀ t, t ∈ S ↔ (φ t).1 ∈ Ov ∧ (φ t).2 ∈ Ov) (J : Matrix n n T) (Λ : Submodule S (n → T))
  (hΛ : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, hform σ J z y ∈ S)

include hσ in
theorem hform_fst (z y : n → T) :
    (φ (hform σ J z y)).1 = ∑ i, ∑ j, (φ (z i)).2 * (φ (J i j)).1 * (φ (y j)).1 := by

  simp [hform, map_sum, map_mul, Prod.fst_sum, hσ, swapR]

include hσ in
theorem hform_snd (z y : n → T) :
    (φ (hform σ J z y)).2 = ∑ i, ∑ j, (φ (z i)).1 * (φ (J i j)).2 * (φ (y j)).2 := by

  simp [hform, map_sum, map_mul, Prod.snd_sum, hσ, swapR]


include hσ Ov hS hΛ in
include hσ hS hΛ in
theorem map_of_first (x : GL n T) (hx : x ∈ UJ σ J)
    (h1 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ (((x : Matrix n n T) *ᵥ y) a)).1)
    (h2 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ ((((x⁻¹ : GL n T) : Matrix n n T) *ᵥ y) a)).1)
    (y : n → T) (hy : y ∈ Λ) : (x : Matrix n n T) *ᵥ y ∈ Λ := by
  have key : ∀ (K' : Matrix n n T) (a b : n → T), hform σ K' a b = (fun i => σ (a i)) ᵥ* K' ⬝ᵥ b := by
    intro K' a b
    simp only [hform, Matrix.vecMul, dotProduct, Finset.sum_mul]
    exact Finset.sum_comm
  have hgen : ∀ (M : Matrix n n T) (a b : n → T),
      hform σ J (M *ᵥ a) (M *ᵥ b) = hform σ (cT σ M * J * M) a b := by
    intro M a b
    have hmap : (fun i => σ ((M *ᵥ a) i)) = (M.map σ) *ᵥ (fun i => σ (a i)) := by
      funext i

      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [key, key, hmap, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      Matrix.vecMul_vecMul]
    simp only [Matrix.mul_assoc]
    rfl
  have hU : cT σ (x : Matrix n n T) * J * (x : Matrix n n T) = J := hx
  have hz' : ∀ z : n → T, z = (x : Matrix n n T) *ᵥ (((x⁻¹ : GL n T) : Matrix n n T) *ᵥ z) := by
    intro z
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hΛ]
  intro z hz
  rw [hS]
  have hinv : hform σ J z ((x : Matrix n n T) *ᵥ y) =
      hform σ J (((x⁻¹ : GL n T) : Matrix n n T) *ᵥ z) y := by
    nth_rewrite 1 [hz' z]
    rw [hgen, hU]
  refine ⟨?_, ?_⟩
  · obtain ⟨y', hy'Λ, hy'⟩ := h1 y hy
    have e : (φ (hform σ J z ((x : Matrix n n T) *ᵥ y))).1 = (φ (hform σ J z y')).1 := by
      rw [hform_fst φ σ hσ J, hform_fst φ σ hσ J]
      simp only [hy']
    rw [e]
    exact ((hS _).1 ((hΛ y').1 hy'Λ z hz)).1
  · obtain ⟨z', hz'Λ, hz'e⟩ := h2 z hz
    have e : (φ (hform σ J z ((x : Matrix n n T) *ᵥ y))).2 = (φ (hform σ J z' y)).2 := by
      rw [hinv, hform_snd φ σ hσ J, hform_snd φ σ hσ J]
      simp only [hz'e]
    rw [e]
    exact ((hS _).1 ((hΛ y).1 hy z' hz'Λ)).2


include hσ Ov hS hΛ in
include hσ hS hΛ in
theorem stab_of_first (x : GL n T) (hx : x ∈ UJ σ J)
    (h1 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ (((x : Matrix n n T) *ᵥ y) a)).1)
    (h2 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ ((((x⁻¹ : GL n T) : Matrix n n T) *ᵥ y) a)).1) :
    x ∈ stabGL Λ := by
  show ∀ y : n → T, y ∈ Λ ↔ (x : Matrix n n T) *ᵥ y ∈ Λ
  intro y
  constructor
  · exact map_of_first φ σ hσ Ov S hS J Λ hΛ x hx h1 h2 y
  · intro hxy
    have hxi : x⁻¹ ∈ UJ σ J := inv_mem hx
    have := map_of_first φ σ hσ Ov S hS J Λ hΛ x⁻¹ hxi h2 (by simpa using h1) _ hxy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem int_conj_iff {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n] (Ov : Subring K) (fr g : GL n K) :
    (∀ t : n → K, (∀ a, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ t) a ∈ Ov) →
      ∀ a, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((g : Matrix n n K) *ᵥ t)) a ∈ Ov) ↔
      ∀ a b, ((fr⁻¹ * g * fr : GL n K) : Matrix n n K) a b ∈ Ov := by
  have hmat : ∀ t : n → K, ((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((g : Matrix n n K) *ᵥ t) =
      ((fr⁻¹ * g * fr : GL n K) : Matrix n n K) *ᵥ (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ t) := by
    intro t
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  constructor
  · intro H a b
    have he : ((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((fr : Matrix n n K) *ᵥ Pi.single b 1) =
        Pi.single b 1 := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have h0 : ∀ c, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((fr : Matrix n n K) *ᵥ Pi.single b 1)) c ∈ Ov := by
      intro c
      rw [he]
      by_cases hc : c = b
      · subst hc; simp
      · simp [Pi.single_apply, hc]
    have := H _ h0 a
    rw [hmat, he] at this
    simpa [Matrix.mulVec_single] using this
  · intro H t ht a
    rw [hmat]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun b _ => mul_mem (H a b) (ht b)

end Formalism.L2.G.Cmp
end
end
