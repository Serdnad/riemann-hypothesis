module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.AdjoinRoot

@[expose] public section

section

open Polynomial

namespace GlobalTheory

noncomputable def awayLiftAlgHom {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) : Localization.Away P →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers P) (f := f)
    (by rintro ⟨_, n, rfl⟩; simpa using h.pow n)

theorem awayLiftAlgHom_algebraMap {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) (q : k[X]) :
    awayLiftAlgHom P f h (algebraMap k[X] (Localization.Away P) q) = f q := by
  simp [awayLiftAlgHom, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

theorem aeval_reverse_mul_pow_of_mul_eq_one {k : Type} [Field k] {B : Type} [CommRing B]
    [Algebra k B] (x y : B) (h : x * y = 1) (P : k[X]) :
    aeval y P.reverse * x ^ P.natDegree = aeval x P := by
  letI : Invertible x := invertibleOfRightInverse x y h
  have hinv : (⅟x : B) = y := invOf_eq_right_inv h
  have := eval₂_reverse_mul_pow (algebraMap k B) x P
  rw [hinv] at this
  simpa [aeval_def] using this

theorem algebraMap_eq_aeval_X {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    [Algebra k[X] B] [IsScalarTower k k[X] B] (p : k[X]) :
    algebraMap k[X] B p = aeval (algebraMap k[X] B X) p := by
  have : (IsScalarTower.toAlgHom k k[X] B) = aeval (algebraMap k[X] B X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun this p

theorem localizationAway_inv_coordinate (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    ∃ Q : Polynomial k, Q ≠ 0 ∧
      ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q)
        (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)),
        (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) =
            algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧
          τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) =
            (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
              IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  classical
  have hrev : P.reverse ≠ 0 := fun h => hP (reverse_eq_zero.mp h)
  refine ⟨X * P.reverse, mul_ne_zero X_ne_zero hrev, ?_⟩

  set C := Localization.Away (X * P)
  set u : C := IsLocalization.Away.invSelf (X * P)
  have hu : algebraMap k[X] C (X * P) * u = 1 := IsLocalization.Away.mul_invSelf _
  set xC : C := algebraMap k[X] C X
  set xi : C := algebraMap k[X] C P * u
  have hxC : xC * xi = 1 := by rw [← hu, map_mul]; ring
  have hPC : IsUnit (algebraMap k[X] C P) :=
    isUnit_iff_exists_inv.mpr ⟨xC * u, by rw [← hu, map_mul]; ring⟩
  have hxi : IsUnit xi := isUnit_iff_exists_inv'.mpr ⟨xC, hxC⟩
  have hτ : IsUnit (aeval xi (X * P.reverse)) := by
    rw [map_mul, aeval_X]
    refine hxi.mul ?_
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) xC xi hxC P
    rw [← algebraMap_eq_aeval_X] at key
    exact isUnit_of_mul_isUnit_left (key ▸ hPC)
  let τ := awayLiftAlgHom (X * P.reverse) (aeval xi) hτ

  set B := Localization.Away (X * P.reverse)
  set v : B := IsLocalization.Away.invSelf (X * P.reverse)
  have hv : algebraMap k[X] B (X * P.reverse) * v = 1 := IsLocalization.Away.mul_invSelf _
  set yB : B := algebraMap k[X] B X
  set yi : B := algebraMap k[X] B P.reverse * v
  have hyB : yB * yi = 1 := by rw [← hv, map_mul]; ring
  have hrevB : IsUnit (algebraMap k[X] B P.reverse) :=
    isUnit_iff_exists_inv.mpr ⟨yB * v, by rw [← hv, map_mul]; ring⟩
  have hyi : IsUnit yi := isUnit_iff_exists_inv'.mpr ⟨yB, hyB⟩
  have hσ : IsUnit (aeval yi P) := by
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) yi yB (by rw [mul_comm]; exact hyB) P
    rw [← algebraMap_eq_aeval_X] at key
    rw [← key]
    exact hrevB.mul (hyi.pow _)
  let σ := awayLiftAlgHom P (aeval yi) hσ
  have hτalg : ∀ q : k[X], τ (algebraMap k[X] B q) = aeval xi q :=
    awayLiftAlgHom_algebraMap _ _ _
  have hσalg : ∀ q : k[X], σ (algebraMap k[X] (Localization.Away P) q) = aeval yi q :=
    awayLiftAlgHom_algebraMap _ _ _
  refine ⟨σ, τ, ?_, ?_⟩
  · have hτyi : τ yi = xC := by
      have h1 : τ yB * τ yi = 1 := by rw [← map_mul, hyB, map_one]
      have h2 : τ yB = xi := by rw [hτalg, aeval_X]
      rw [h2] at h1
      calc τ yi = τ yi * (xC * xi) := by rw [hxC, mul_one]
        _ = xC * (xi * τ yi) := by ring
        _ = xC := by rw [h1, mul_one]
    have hext : ((τ.comp σ).comp (IsScalarTower.toAlgHom k k[X] (Localization.Away P))) =
        IsScalarTower.toAlgHom k k[X] C := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [hσalg, aeval_X, hτyi]
    exact RingHom.ext fun p => DFunLike.congr_fun hext p
  · exact RingHom.ext fun p => hτalg p

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem herm_form_identity (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h1 : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w)))
    (h2 : ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ))
    (z w : Fin g → ℂ) :
    z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by
  have hadd : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z u v : Fin g → ℂ),
      z ⬝ᵥ H.mulVec (star (u + v)) = z ⬝ᵥ H.mulVec (star u) + z ⬝ᵥ H.mulVec (star v) := by
    intro H z u v; rw [star_add, mulVec_add, dotProduct_add]
  have hsmul : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      z ⬝ᵥ H.mulVec (star (a • v)) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, star_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]
    simp
  have hsmulL : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      (a • z) ⬝ᵥ H.mulVec (star v) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, smul_dotProduct, smul_eq_mul]
  have hsum : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (f : Fin r → (Fin g → ℂ)),
      z ⬝ᵥ H.mulVec (star (∑ i, f i)) = ∑ i, z ⬝ᵥ H.mulVec (star (f i)) := by
    intro H z f
    rw [star_sum, mulVec_sum, dotProduct_sum]
  have hsa : ∀ (q : Polynomial ℚ) (z w : Fin g → ℂ),
      z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ q w)) =
        Polynomial.aeval γ q z ⬝ᵥ H₂.mulVec (star w) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro z w
      simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
      rw [hsmul, hsmulL]
    | add p q hp hq =>
      intro z w
      simp only [map_add (f := _), LinearMap.add_apply]
      rw [hadd, hp, hq, add_dotProduct]
    | monomial n a ih =>
      intro z w
      have e : Polynomial.C a * Polynomial.X ^ (n+1) =
          (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      have e' : Polynomial.C a * Polynomial.X ^ (n+1) =
          Polynomial.X * (Polynomial.C a * Polynomial.X ^ n) := by ring
      calc z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ (n+1)) w))
          = z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) (γ w))) := by
            rw [e, map_mul (Polynomial.aeval γ) (Polynomial.C a * Polynomial.X ^ n) Polynomial.X,
              Polynomial.aeval_X, Module.End.mul_apply]
        _ = Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z ⬝ᵥ H₂.mulVec (star (γ w)) :=
            ih _ _
        _ = γ (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z) ⬝ᵥ H₂.mulVec (star w) :=
            h2 _ _
        _ = _ := by
            rw [e', map_mul (Polynomial.aeval γ) Polynomial.X (Polynomial.C a * Polynomial.X ^ n),
              Polynomial.aeval_X, Module.End.mul_apply]
  have comm : ∀ q : Polynomial ℚ, (Polynomial.aeval γ q) ^ 2 * γ =
      γ * (Polynomial.aeval γ q * Polynomial.aeval γ q) := by
    intro q
    rw [show (Polynomial.aeval γ q) ^ 2 * γ = Polynomial.aeval γ (q ^ 2 * Polynomial.X) by
          simp [map_mul, map_pow],
      show q ^ 2 * Polynomial.X = Polynomial.X * (q * q) by ring]
    simp [map_mul]
  have hw : w = c₀ • γ w + ∑ i, c i • (γ (Polynomial.aeval γ (p i) (Polynomial.aeval γ (p i) w))) := by
    have := congrArg (fun f : Module.End ℂ (Fin g → ℂ) => f w) hid
    simp only [Module.End.one_apply, LinearMap.add_apply, LinearMap.smul_apply,
      comm] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
    exact this
  conv_lhs => rw [hw]
  rw [hadd, hsmul, hsum, ← h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsmul, ← h1, hsa]

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem nsmul_aeval_mem_lattice_of_intMatrix_basis (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ)
    (hT : Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ))
    (p : Polynomial ℚ) (D : ℕ) (hD : ∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) :
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by
  let φ : Module.End ℂ (Fin g → ℂ) →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := fun f => LinearMap.toMatrix e e (f.restrictScalars ℝ)
      map_one' := by
        rw [show ((1 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 1 from rfl]
        exact LinearMap.toMatrix_one e
      map_mul' := fun f h => by
        rw [show ((f * h).restrictScalars ℝ) = (f.restrictScalars ℝ) * (h.restrictScalars ℝ) from rfl]
        exact LinearMap.toMatrix_mul e _ _
      map_zero' := by
        rw [show ((0 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 0 from rfl]
        simp
      map_add' := fun f h => by
        rw [show ((f + h).restrictScalars ℝ) = (f.restrictScalars ℝ) + (h.restrictScalars ℝ) from rfl]
        simp
      commutes' := fun r => by
        have : ((algebraMap ℚ (Module.End ℂ (Fin g → ℂ)) r).restrictScalars ℝ) = algebraMap ℝ (Module.End ℝ (Fin g → ℂ)) (r : ℝ) := by
          refine LinearMap.ext fun x => funext fun i => ?_
          simp [Module.algebraMap_end_apply, Rat.smul_def]
        rw [this, LinearMap.toMatrix_algebraMap]
        ext i j
        simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
        }
  let ψ : Matrix (Fin n) (Fin n) ℚ →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ := (Algebra.ofId ℚ ℝ).mapMatrix
  have hψ : ∀ M : Matrix (Fin n) (Fin n) ℚ, ψ M = M.map (Rat.cast : ℚ → ℝ) := by
    intro M
    ext i j
    simp [ψ]
  have hφ : ∀ f : Module.End ℂ (Fin g → ℂ), φ f = LinearMap.toMatrix e e (f.restrictScalars ℝ) :=
    fun f => rfl
  have key : LinearMap.toMatrix e e ((Polynomial.aeval γ p).restrictScalars ℝ)
      = (Polynomial.aeval Tq p).map (Rat.cast : ℚ → ℝ) := by
    rw [← hφ, ← hψ, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hφ, hψ, hT]
  intro x hx
  choose m hm using (hΛ x).mp hx
  choose z hz using hD
  rw [hΛ]
  intro k
  refine ⟨∑ l, z k l * m l, ?_⟩
  have hv : ⇑(e.repr ((Polynomial.aeval γ p) x))
      = (Polynomial.aeval Tq p).map (Rat.cast : ℚ → ℝ) *ᵥ ⇑(e.repr x) := by
    rw [← key, LinearMap.toMatrix_mulVec_repr]
    rfl
  rw [LinearMap.smul_apply, map_nsmul, Finsupp.smul_apply, hv]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hm, nsmul_eq_mul, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  have := congrArg (Rat.cast : ℚ → ℝ) (hz k l)
  push_cast at this
  rw [← this]
  ring

theorem nsmul_aeval_mem_lattice_of_intMatrix : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ :=
  fun g n Λ e hΛ γ Tq hT p D hD => nsmul_aeval_mem_lattice_of_intMatrix_basis g n Λ e hΛ γ Tq hT p D hD

end GlobalTheory
end

section

namespace GlobalTheory

open Polynomial

theorem eigencharacters_finite_of_commuting_annihilated :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V))
      (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) →
      (∀ t ∈ T, p t ≠ 0) → ∃ X' : Set (Module.End ℂ V → ℂ), X'.Finite ∧ ∀ ψ : V,
        (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → ∀ (χ' : Module.End ℂ V → ℂ) (u : V),
        u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
          (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) → u ≠ 0 →
        (∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), z u = χ' z • u) →
        ∃ χ ∈ X', ∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), χ' z = χ z := by
  intro V _ _ T p hcomm hp
  classical
  set A := Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) with hA
  let X' : Set (Module.End ℂ V → ℂ) :=
    {χ | (∀ z, z ∉ A → χ z = 0) ∧ (∃ u : V, u ≠ 0 ∧ ∀ z ∈ A, z u = χ z • u) ∧
      ∀ t ∈ T, (p t).eval (χ t) = 0}

  have hdet : ∀ χ₁ ∈ X', ∀ χ₂ ∈ X', (∀ t ∈ T, χ₁ t = χ₂ t) → χ₁ = χ₂ := by
    rintro χ₁ ⟨h₁0, ⟨u₁, hu₁, he₁⟩, -⟩ χ₂ ⟨h₂0, ⟨u₂, hu₂, he₂⟩, -⟩ hT

    have key : ∀ (χ : Module.End ℂ V → ℂ) (u : V), u ≠ 0 → (∀ z ∈ A, z u = χ z • u) →
        (∀ r : ℂ, χ (algebraMap ℂ _ r) = r) ∧
        (∀ x ∈ A, ∀ y ∈ A, χ (x + y) = χ x + χ y) ∧
        (∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) := by
      intro χ u hu he
      have inj := smul_left_injective ℂ hu
      refine ⟨fun r => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
      · apply inj
        simp only
        rw [← he _ (Subalgebra.algebraMap_mem A r)]
        simp [Module.algebraMap_end_apply]
      · apply inj
        simp only
        rw [← he _ (add_mem hx hy), LinearMap.add_apply, he x hx, he y hy, add_smul]
      · apply inj
        simp only
        rw [← he _ (mul_mem hx hy), Module.End.mul_apply, he y hy, map_smul, he x hx,
          smul_smul, mul_comm]
    obtain ⟨m₁, a₁, p₁⟩ := key χ₁ u₁ hu₁ he₁
    obtain ⟨m₂, a₂, p₂⟩ := key χ₂ u₂ hu₂ he₂
    funext z
    by_cases hz : z ∈ A
    · induction hz using Algebra.adjoin_induction with
      | mem x hx => exact hT x hx
      | algebraMap r => rw [m₁, m₂]
      | add x y hx hy ihx ihy => rw [a₁ x hx y hy, a₂ x hx y hy, ihx, ihy]
      | mul x y hx hy ihx ihy => rw [p₁ x hx y hy, p₂ x hx y hy, ihx, ihy]
    · rw [h₁0 z hz, h₂0 z hz]
  refine ⟨X', ?_, ?_⟩
  ·
    let f : (Module.End ℂ V → ℂ) → (T → ℂ) := fun χ t => χ t
    apply Set.Finite.of_finite_image (f := f)
    · apply (Set.Finite.pi (t := fun t : T => ((p t).roots.toFinset : Set ℂ))
        (fun t => Finset.finite_toSet _)).subset
      rintro _ ⟨χ, ⟨-, -, hroot⟩, rfl⟩
      simp only [Set.mem_pi, Set.mem_univ, Finset.mem_coe, Multiset.mem_toFinset, true_implies]
      intro t
      rw [Polynomial.mem_roots (hp t t.2)]
      exact hroot t t.2
    · intro χ₁ h₁ χ₂ h₂ hf
      exact hdet χ₁ h₁ χ₂ h₂ fun t ht => congrFun hf ⟨t, ht⟩
  · intro ψ hψ χ' u hu hu0 he
    refine ⟨fun z => if z ∈ A then χ' z else 0, ⟨fun z hz => if_neg hz,
      ⟨u, hu0, fun z hz => by simp only [if_pos hz]; exact he z hz⟩, fun t ht => ?_⟩,
      fun z hz => (if_pos hz).symm⟩
    have htA : t ∈ A := Algebra.subset_adjoin ht
    simp only [if_pos htA]

    have hker : u ∈ LinearMap.ker (Polynomial.aeval t (p t)) := by
      refine (Submodule.span_le.mpr ?_) hu
      rintro _ ⟨z, hz, rfl⟩
      have hzt : Commute t z :=
        Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz (fun s hs => hcomm t ht s hs)
      have hc : Commute z (Polynomial.aeval t (p t)) :=
        Algebra.commute_of_mem_adjoin_singleton_of_commute
          (Polynomial.aeval_mem_adjoin_singleton ℂ t) hzt.symm
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hψ t ht, map_zero]
    have hev : t.HasEigenvector (χ' t) u :=
      Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (he t htA), hu0⟩
    have := Module.End.aeval_apply_of_hasEigenvector (p := p t) hev
    rw [LinearMap.mem_ker.mp hker] at this
    exact smul_left_injective ℂ hu0 (by simpa using this.symm)

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem noether_trick_monic {k : Type} [Field k] (f : Polynomial (Polynomial k)) (hf : f.Monic)
    (M : ℕ) (hM0 : M ≠ 0) (hM : ∀ i, (f.coeff i).natDegree < M) :
    (f.eval₂ (Polynomial.mapRingHom (Polynomial.C : k →+* Polynomial k))
      ((Polynomial.X : Polynomial (Polynomial k)) ^ M - Polynomial.C Polynomial.X)).Monic := by
  set r : Polynomial (Polynomial k) := X ^ M - C X with hr
  have hrm : r.Monic := monic_X_pow_sub_C _ hM0
  have hrd : r.natDegree = M := natDegree_X_pow_sub_C _
  rw [eval₂_eq_sum_range, Finset.sum_range_succ]
  have hlead : f.coeff f.natDegree = 1 := hf
  rw [hlead, map_one, one_mul]
  apply Monic.add_of_right (hrm.pow _)
  rw [degree_eq_natDegree (hrm.pow _).ne_zero, hrm.natDegree_pow, hrd]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  rw [Finset.mem_range] at hi
  refine lt_of_le_of_lt degree_le_natDegree ?_
  rw [Nat.cast_lt]
  have h1 : (mapRingHom (C : k →+* Polynomial k) (f.coeff i)).natDegree ≤ (f.coeff i).natDegree := by
    rw [coe_mapRingHom]; exact natDegree_map_le
  have h2 : (r ^ i).natDegree ≤ i * M := by
    rw [← hrd]; exact natDegree_pow_le
  have h3 := hM i
  have h4 : (i + 1) * M ≤ f.natDegree * M := Nat.mul_le_mul_right M hi
  calc _ ≤ _ := natDegree_mul_le
    _ ≤ (f.coeff i).natDegree + i * M := Nat.add_le_add h1 h2
    _ < f.natDegree * M := by nlinarith

theorem noether_trick : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (t a : A),
    (Polynomial.aeval (R := k) t).Finite → ∃ M : ℕ, (Polynomial.aeval (R := k) (t ^ M + a)).Finite := by
  intro k A _ _ _ t a ht
  have hint : (aeval (R := k) t).toRingHom.IsIntegral := RingHom.Finite.to_isIntegral ht
  obtain ⟨f, hfm, hf0⟩ := hint (-a)
  set M := 1 + ∑ i ∈ Finset.range (f.natDegree + 1), (f.coeff i).natDegree with hMdef
  have hM : ∀ i, (f.coeff i).natDegree < M := by
    intro i
    by_cases hi : i ≤ f.natDegree
    · have := Finset.single_le_sum (f := fun i => (f.coeff i).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      have h' : (f.coeff i).natDegree ≤ ∑ j ∈ Finset.range (f.natDegree + 1), (f.coeff j).natDegree := this
      omega
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp only [natDegree_zero]; omega
  refine ⟨M, ?_⟩
  set φ : Polynomial k →+* A := (aeval (R := k) (t ^ M + a)).toRingHom with hφ
  set q : Polynomial (Polynomial k) :=
    f.eval₂ (mapRingHom (C : k →+* Polynomial k)) (X ^ M - C X) with hqdef
  have hq : q.Monic := noether_trick_monic f hfm M (by omega) hM
  set ψ : Polynomial (Polynomial k) →+* A := eval₂RingHom φ t with hψ
  have hcomp : ψ.comp (mapRingHom C) = (aeval (R := k) t).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c; simp [ψ, φ]
    · simp [ψ, φ]
  have hψq : ψ q = 0 := by
    simp only [hqdef]
    rw [hom_eval₂, hcomp]
    have : ψ (X ^ M - C X) = -a := by simp [ψ, φ]
    rw [this]; exact hf0
  have hqt : q.eval₂ φ t = 0 := by simpa [ψ] using hψq
  let L : AdjoinRoot q →+* A := AdjoinRoot.lift φ t hqt
  have hL : L.comp (AdjoinRoot.mk q) = ψ := by
    ext g <;> simp [L, ψ, AdjoinRoot.lift_mk]
  have hψfin : ψ.Finite := by
    apply RingHom.Finite.of_comp_finite (f := mapRingHom (C : k →+* Polynomial k))
    rw [hcomp]; exact ht
  have hLfin : L.Finite := by
    apply RingHom.Finite.of_comp_finite (f := AdjoinRoot.mk q)
    rw [hL]; exact hψfin
  have hof : (AdjoinRoot.of q).Finite := by
    haveI : Module.Finite (Polynomial k) (AdjoinRoot q) := (AdjoinRoot.powerBasis' hq).finite
    exact RingHom.finite_algebraMap.mpr this
  have hφeq : L.comp (AdjoinRoot.of q) = φ := by
    ext c <;> simp [L, AdjoinRoot.lift_of]
  have : φ.Finite := by rw [← hφeq]; exact hLfin.comp hof
  exact this

end GlobalTheory
end
