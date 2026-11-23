module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Tactic.Continuity
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle011
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle013
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle015
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle005
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Subgroup.Finite

@[expose] public section

section

open GlobalTheory.UnitLemma

namespace GlobalTheory.TorusInteg

theorem torus_integral_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ α : G, τ α = α → (∀ i, 0 < Multiplicative.toAdd (w i α)) → ∀ (t : T) (k : ℕ), (∀ i, 0 ≤ Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))) ↔ ∀ j, |Multiplicative.toAdd (((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype t) j| ≤ ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ) := by
  intro G _ τ T hT ι s w hs r e hcov α hα hpos t k
  have hτt : τ (t : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_right ((hT _).1 t.2)
  have val1 : ∀ i, Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))
      = - Multiplicative.toAdd (w i t) + k * Multiplicative.toAdd (w i α) := by
    intro i
    simp [map_mul, map_inv, map_pow, toAdd_mul, toAdd_inv, toAdd_pow, nsmul_eq_mul]
  have val2 : ∀ i, Multiplicative.toAdd (w i (τ ((t : G)⁻¹ * α ^ k)))
      = Multiplicative.toAdd (w i t) + k * Multiplicative.toAdd (w i α) := by
    intro i
    rw [map_mul, map_inv, map_pow, hτt, hα, inv_inv]
    simp [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul]
  have rhs : ∀ j, ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ)
      = k * Multiplicative.toAdd (w (e j) α) := by
    intro j
    push_cast
    rw [Int.toNat_of_nonneg (hpos _).le]
  have lhs : ∀ j, Multiplicative.toAdd (((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype t) j
      = Multiplicative.toAdd (w (e j) t) := fun j => rfl
  constructor
  · intro h j
    rw [lhs, rhs, abs_le]
    have h1 := h (e j)
    have h2 := (hs (e j) _).1 (h (s (e j)))
    rw [val1] at h1
    rw [val2] at h2
    constructor <;> linarith
  · intro h i
    rcases hcov i with hi | ⟨j, rfl | rfl⟩
    · have hz : Multiplicative.toAdd (w i t) = 0 := by
        have := hs i (t : G)
        rw [hi, hτt, map_inv, toAdd_inv] at this
        rcases lt_trichotomy (Multiplicative.toAdd (w i t)) 0 with h' | h' | h'
        · exact absurd (this.2 (by linarith)) (not_le.2 h')
        · exact h'
        · exact absurd (this.1 h'.le) (not_le.2 (by linarith))
      rw [val1, hz]
      have := (hpos i).le
      positivity
    · have := h j
      rw [lhs, rhs, abs_le] at this
      rw [val1]; linarith [this.1]
    · have := h j
      rw [lhs, rhs, abs_le] at this
      apply (hs (e j) _).2
      rw [val2]; linarith [this.1]

end GlobalTheory.TorusInteg
end

section

open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

theorem valsAt_torus_surjective : ∀ (G : Type) [CommGroup G] (τ : G →* G), (∀ x, τ (τ x) = x) → ∀ (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → (∀ i (n : ℤ), ∃ y : G, w i y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ i → w j y = 1) → ∀ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) → (∀ j k, s (e j) ≠ e k) → Function.Surjective (((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype) := by
  intro G _ τ hττ T hT ι s w hsw hex r e he hs n
  choose y hy1 hy2 using fun j : Fin r => hex (e j) (Multiplicative.toAdd n j)
  have hτ : ∀ i j, w (e i) (τ (y j)) = 1 := by
    intro i j
    have h1 : w (s (e i)) (y j) = 1 := hy2 j _ (hs i j)
    have a := (hsw (e i) (y j)).1 (by rw [h1]; simp)
    have b := (hsw (e i) (y j)⁻¹).1 (by rw [map_inv, h1]; simp)
    rw [map_inv, map_inv, toAdd_inv] at b
    apply Multiplicative.toAdd.injective
    simp only [toAdd_one]
    omega
  have hu : ∀ j, y j * (τ (y j))⁻¹ ∈ T := by
    intro j
    rw [hT, map_mul, map_inv, hττ]
    group
  refine ⟨⟨∏ j, y j * (τ (y j))⁻¹, Subgroup.prod_mem T fun j _ => hu j⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  apply Multiplicative.toAdd.injective
  funext i
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.piMultiplicative_symm_apply, toAdd_ofAdd, MonoidHom.pi_apply, Function.comp_apply]
  rw [map_prod, toAdd_prod]
  have hc : ∀ j, Multiplicative.toAdd (w (e i) (y j * (τ (y j))⁻¹)) = if i = j then Multiplicative.toAdd n i else 0 := by
    intro j
    rw [map_mul, map_inv, hτ, inv_one, mul_one]
    split_ifs with hij
    · subst hij; rw [hy1]; rfl
    · rw [hy2 j (e i) fun h => hij (he _ _ h)]; rfl
  simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.UnitLemma
end

section

open GlobalTheory.UnitLemma

namespace GlobalTheory.TorusKer

theorem valsAt_torus_eq_one_iff (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G)
    (hT : ∀ t, t ∈ T ↔ t * τ t = 1) (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ)
    (hs : ∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x)))
    (r : ℕ) (e : Fin r → ι) (hcov : ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) (t : T) :
    ((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by
  have hinv : ∀ i (x : G), Multiplicative.toAdd (w i x⁻¹) = - Multiplicative.toAdd (w i x) := by
    intro i x; rw [map_inv, toAdd_inv]
  have hτ : τ (t : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_right ((hT t).1 t.2)
  have hτ' : τ ((t : G)⁻¹) = (t : G) := by rw [map_inv, hτ, inv_inv]
  constructor
  · intro h
    have he : ∀ j, Multiplicative.toAdd (w (e j) (t : G)) = 0 := by
      intro j
      have := congrArg (fun y : Multiplicative (Fin r → ℤ) => Multiplicative.toAdd y j) h
      simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.piMultiplicative_symm_apply, toAdd_ofAdd, MonoidHom.pi_apply, Function.comp_apply] using this
    intro i
    rcases hcov i with hi | ⟨j, hj | hj⟩
    · have h1 := hs i (t : G)
      rw [hi, hτ, hinv] at h1
      omega
    · subst hj; exact he j
    · subst hj
      have h1 := hs (e j) (t : G)
      have h2 := hs (e j) ((t : G)⁻¹)
      rw [hτ, hinv, he j] at h1
      rw [hτ', he j, hinv] at h2
      omega
  · intro h
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.piMultiplicative_symm_apply, toAdd_ofAdd, MonoidHom.pi_apply, Function.comp_apply]
    rw [h]
    rfl

end GlobalTheory.TorusKer
end

section

open Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.baseChange_polynomial_annihilates_descent : ∀ (Ks L0 KB WK ι : Type) [Field Ks] [Field L0] [Field KB] [Algebra Ks L0] [Algebra Ks KB] [AddCommGroup WK]
    [Module Ks WK] (rd : L0 →+* KB), (∀ a : Ks, rd (algebraMap Ks L0 a) = algebraMap Ks KB a) →
    ∀ (T0 : Module.End Ks WK) (s : Finset ι) (ρ : ι → Module.End Ks WK) (a : ι → L0) (q : L0[X]),
    (∀ z ∈ LinearMap.range (∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)),
      Polynomial.aeval (LinearMap.baseChange L0 T0) q z = 0) →
    ∀ y ∈ LinearMap.range (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)),
      Polynomial.aeval (LinearMap.baseChange KB T0) (q.map rd) y = 0 := by
  first | exact @GlobalTheory.baseChange_polynomial_kills_descent | exact GlobalTheory.baseChange_polynomial_kills_descent | (intros; apply GlobalTheory.baseChange_polynomial_kills_descent <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_common_denominator_aeval_of_fg' : ∀ (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A), (∀ x : A, ∃ p : E[X], aeval g p = x) → ∀ S : Submodule O A, S.FG → ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  first | exact @GlobalTheory.exists_common_denominator_aeval_of_fg | exact GlobalTheory.exists_common_denominator_aeval_of_fg | (intros; apply GlobalTheory.exists_common_denominator_aeval_of_fg <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.newtonPolygon_lastDominantIndex_mul_X_sub_C : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧ ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by
  first | exact @GlobalTheory.newton_step_root_in_disc | exact GlobalTheory.newton_step_root_in_disc | (intros; apply GlobalTheory.newton_step_root_in_disc <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.newtonPolygon_dominant_index_X_sub_C_mul : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ρ < ‖a‖ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d) ∧ ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
  first | exact @GlobalTheory.newton_step_root_outside_disc | exact GlobalTheory.newton_step_root_outside_disc | (intros; apply GlobalTheory.newton_step_root_outside_disc <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.not_X_pow_succ_dvd_det_of_first_order_kernel : ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (0 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m → ¬ (Polynomial.X : Polynomial K) ^ (m + 1) ∣ Ψ.det := by
  first | exact @GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero | exact GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero | (intros; apply GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.exp_integral_differentiable_real_re_pos : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ), Measurable f → Measurable t → (∀ y, 0 ≤ f y) →
    Integrable f ν → (∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) →
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  first | exact @GlobalTheory.exp_integral_entire_real_pos | exact GlobalTheory.exp_integral_entire_real_pos | (intros; apply GlobalTheory.exp_integral_entire_real_pos <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.tsum_setIntegral_eq_zero_of_stabilizer_integrals : ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant], SFinite ν → ∀ (Λ : Subgroup G), Countable Λ → ∀ 𝓖 : Set G, IsFundamentalDomain Λ 𝓖 ν → ∀ (a : Λ → X → X), (∀ x, a 1 x = x) → (∀ γ δ x, a (γ * δ) x = a γ (a δ x)) → ∀ F : X → G → ℂ, (∀ γ x g, F (a γ x) g = F x ((γ : G)⁻¹ * g)) → (∀ x, AEStronglyMeasurable (F x) ν) → ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν ≠ ⊤ → (∀ x (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x = x) → ∀ 𝓓 : Set G, IsFundamentalDomain Γ 𝓓 ν → IntegrableOn (F x) 𝓓 ν → ∫ g in 𝓓, F x g ∂ν = 0) → ∑' x, ∫ g in 𝓖, F x g ∂ν = 0 := by
  first | exact @GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer | exact GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer | (intros; apply GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.unfold_tsum_integral_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → ∀ (a b P : G → ℂ), Continuous a → Continuous b →
    (∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) → StronglyMeasurable P →
    ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤ →
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  first | exact @GlobalTheory.unfold_tsum_fundamentalDomain | exact GlobalTheory.unfold_tsum_fundamentalDomain | (intros; apply GlobalTheory.unfold_tsum_fundamentalDomain <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.norm_integral_star_mul_sq_le_mul : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ), AEStronglyMeasurable f μ → AEStronglyMeasurable h μ → Integrable (fun x => star (f x) * f x) μ → Integrable (fun x => star (h x) * h x) μ → ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re := by
  first | exact @GlobalTheory.norm_integral_star_mul_sq_le | exact GlobalTheory.norm_integral_star_mul_sq_le | (intros; apply GlobalTheory.norm_integral_star_mul_sq_le <;> assumption)
end
