module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle004
import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.RightOfFd
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.Pl :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.Kv :
    {F : Type} → [inst : Field F] → [NumberField F] → UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F → Type :=
    fun {F : Type} [Field F] [NumberField F] (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.cv :
    {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) → F →+* UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v :=
    fun {F : Type} [Field F] [NumberField F] (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) ↦ Algebra.algebraMap F (UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v)

open IsDedekindDomain NumberField Module

namespace UpperTheory.Reformulated.B.NormIndexQuadratic

private lemma exists_quad {K : Type} [Field K] [NumberField K] {θ : K} (h : ¬ IsSquare θ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (r : L) (σ : L ≃ₐ[K] L),
      r ^ 2 = algebraMap K L θ ∧ σ r = -r ∧
      (∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * r) ∧ finrank K L = 2 := by
  have : Fact (∀ r : K, r ^ 2 ≠ θ + 0 * r) := ⟨fun r hr => h ⟨r, by rw [← sq, hr]; simp⟩⟩
  have : NumberField (QuadraticAlgebra K θ 0) := NumberField.of_module_finite K _
  refine ⟨QuadraticAlgebra K θ 0, inferInstance, this, inferInstance, QuadraticAlgebra.omega,
    { (starRingAut : RingAut (QuadraticAlgebra K θ 0)) with commutes' := ?_ }, ?_, ?_, ?_,
    QuadraticAlgebra.finrank_eq_two _ _⟩
  · intro r; ext <;> simp
  · ext <;> simp [sq]
  · show star _ = _
    ext <;> simp
  · intro x
    exact ⟨x.re, x.im, by ext <;> simp⟩

end UpperTheory.Reformulated.B.NormIndexQuadratic

theorem UpperTheory.Reformulated.B.NormIndexQuadratic.glob_neg_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {Δ d : F},
      Δ ≠ (0 : F) →
        (∀ (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F),
            ∃ (a : UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v) (b : UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v),
              (-1 : UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v) =
                a ^ (2 : ℕ) - (UpperTheory.Reformulated.B.NormIndexQuadratic.cv v : F → UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v) Δ * b ^ (2 : ℕ)) →
          ∀ (σ₀ : F →+* ℝ),
            (∀ (σ : F →+* ℝ), (σ : F → ℝ) d < (0 : ℝ)) →
              ∃ (p₀ : F) (p₁ : F) (q₀ : F) (q₁ : F),
                p₀ ^ (2 : ℕ) + d * p₁ ^ (2 : ℕ) - Δ * (q₀ ^ (2 : ℕ) + d * q₁ ^ (2 : ℕ)) = (-1 : F) ∧ p₀ * p₁ = Δ * q₀ * q₁ := by
  intro F _ _ Δ d hΔ hloc σ₀ hd
  have hsq : ¬ IsSquare d := by
    rintro ⟨t, rfl⟩
    exact absurd (hd σ₀) (not_lt.2 (by rw [map_mul]; exact mul_self_nonneg _))
  obtain ⟨E, _, _, _, r, σ, hr, hσ, hbasis, -⟩ := exists_quad hsq
  -- Apply the quadratic Hasse norm theorem over F(√d). Negativity of d
  -- rules out real places, and the local witnesses extend to each finite place.
  obtain ⟨p, q, hpq⟩ := GlobalTheory.QNorm.hasseNormSt E (algebraMap F E Δ) (-1)
    ((map_ne_zero _).2 hΔ) (by simp) (fun τ => by
      have hneg := hd (τ.comp (algebraMap F E))
      rw [RingHom.comp_apply, ← hr, map_pow] at hneg
      exact (not_lt_of_ge (sq_nonneg _) hneg).elim) (fun w => by
      obtain ⟨v, φ, hφ⟩ := GlobalTheory.LocalQuad.exists_ringHom_adicCompletion F E w
      obtain ⟨a, b, hab⟩ := hloc v
      refine ⟨φ a, φ b, ?_⟩
      change (-1 : v.adicCompletion F) = a ^ 2 - algebraMap F _ Δ * b ^ 2 at hab
      simpa only [map_neg, map_one, map_sub, map_mul, map_pow, hφ] using congrArg φ hab)
  -- Comparing the equation with its conjugate recovers both coordinates over F.
  have hr0 : r ≠ 0 := by
    rintro rfl
    refine hsq ⟨0, (algebraMap F E).injective ?_⟩
    rw [← hr]; simp
  obtain ⟨p₀, p₁, rfl⟩ := hbasis p
  obtain ⟨q₀, q₁, rfl⟩ := hbasis q
  have hconj := congrArg σ hpq
  simp only [map_neg, map_one, map_sub, map_mul, map_add (f := _), map_pow, hσ, σ.commutes] at hconj
  refine ⟨p₀, p₁, q₀, q₁, (algebraMap F E).injective ?_, (algebraMap F E).injective ?_⟩
  · simp only [map_neg, map_one, map_sub, map_mul, map_add (f := _), map_pow, ← hr]
    linear_combination (-1 / 2) * hpq + (-1 / 2) * hconj
  · simp only [map_mul]
    refine mul_right_cancel₀ hr0 ?_
    linear_combination (-1 / 4) * hpq + (1 / 4) * hconj
end

section

theorem UpperTheory.Reformulated.B.ConjugateSubgroup.conj_sub :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    {Γ A : Subgroup G},
    IsClosed (↑A : Set G) →
      PositivityTheory.ThKEnd.Two.Lat (Γ.subgroupOf A) →
        ∀ {f c : G → ℂ},
          PositivityTheory.ThKEnd.Two.IsAv (Γ.subgroupOf A) Subtype.val f c →
            ∀ {γ : G},
              γ ∈ Γ →
                (∀ u ∈ A, γ⁻¹ * u * γ ∈ A) →
                  (∀ u ∈ A, γ * u * γ⁻¹ ∈ A) →
                    (∀ (x : G), f (γ * x) = f x) →
                      ∀ (x : G),
                        c (γ * x) =
                          c
                            x := by
  intro G _ _ _ _ _ _ _ _ Γ A hA L f c h γ hγ h1 h2 hf x
  haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology A := Topology.IsInducing.subtypeVal.secondCountableTopology
  let e : A ≃ₜ* A :=
    { toFun := fun u => ⟨γ⁻¹ * u * γ, h1 u u.2⟩
      invFun := fun u => ⟨γ * u * γ⁻¹, h2 u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk (by fun_prop) _
      continuous_invFun := Continuous.subtype_mk (by fun_prop) _ }
  refine PositivityTheory.ThKEnd.Two.IsAv.conj (ι := A.subtype) L h e (fun u => ?_) (fun u => ?_) hf x
  · exact (Γ.mul_mem_cancel_right hγ).trans (Γ.mul_mem_cancel_left (inv_mem hγ))
  · exact show (u : G) * γ = γ * (γ⁻¹ * u * γ) by group
end
