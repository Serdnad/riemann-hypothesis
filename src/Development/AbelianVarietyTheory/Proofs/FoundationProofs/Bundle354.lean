module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Formalism.ConjugateSelfDual.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA

theorem spec_approx_cocycle (l : ℕ) [Fact l.Prime] {Γ X : Type} [Group Γ] [CommGroup X] [Fintype X] (r : ℕ)
    (ρ : Γ → Matrix (Fin 2) (Fin 2) (Qbar l)) (κ : Γ →* X) (Y : Γ → X → Fin 2 → Qbar l) (η : X → Qbar l)
    (τ : Γ → Qbar l) (hY : ShCoc ρ κ Y) (hρ : ∀ s i j, ‖ρ s i j‖ ≤ 1) (hYi : ∀ s x i, ‖Y s x i‖ ≤ 1)
    (hη : ∀ x, ‖η x‖ ≤ 1) (happ : ∀ s x, ‖η (x * (κ s)⁻¹) - η x * τ s‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) :
    ∀ s t i, ‖spec η Y (s * t) i - (spec η Y s + τ s • (ρ s *ᵥ spec η Y t)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro s t i
  have hre : (∑ x, η x • Y t (x * κ s)) = ∑ x, η (x * (κ s)⁻¹) • Y t x := by
    exact Fintype.sum_equiv (Equiv.mulRight (κ s)) _ _ (fun x => by simp)
  have key : spec η Y (s * t) - (spec η Y s + τ s • (ρ s *ᵥ spec η Y t))
      = ρ s *ᵥ ∑ x, (η (x * (κ s)⁻¹) - η x * τ s) • Y t x := by
    have h1 : spec η Y (s * t) = spec η Y s + ρ s *ᵥ ∑ x, η x • Y t (x * κ s) := by
      simp only [spec, hY s t, smul_add, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul]
    rw [h1, hre, ← Matrix.mulVec_smul, add_sub_add_left_eq_sub, ← Matrix.mulVec_sub]
    congr 1
    simp only [spec, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, sub_smul, mul_comm (τ s)]
  have hC : (0 : ℝ) ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := norm_nonneg _
  rw [← Pi.sub_apply, key]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
  intro j _
  rw [norm_mul]
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hρ s i j)) ?_
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
  intro x _
  rw [norm_mul]
  exact le_trans (mul_le_of_le_one_right (norm_nonneg _) (hYi t x j)) (happ s x)

end GlobalTheory.KA
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA

theorem spec_cauchy : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (Y : ∀ r : ℕ, Γ → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l), (∀ r s x i, ‖Y r s x i‖ ≤ 1) → (∀ r x, ‖η r x‖ ≤ 1) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖η (r + 1) x - η r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ r s i, ‖spec (η (r + 1)) (Y (r + 1)) s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l _ Γ _ Y η hY hη hYp hηc r s i
  set red := (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) with hred
  have hpush : spec (η r) (Y r) s i = ∑ x', η r (red x') * Y (r + 1) s x' i := by
    simp only [spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hYp r s]
    simp only [push, Finset.sum_apply, Finset.mul_sum]
    rw [← Finset.sum_fiberwise (Finset.univ) red (fun x' => η r (red x') * Y (r + 1) s x' i)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' hx' => ?_
    rw [(Finset.mem_filter.mp hx').2]
  have hspec : spec (η (r + 1)) (Y (r + 1)) s i = ∑ x', η (r + 1) x' * Y (r + 1) s x' i := by
    simp only [spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpush, hspec, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x' _ => ?_
  rw [← sub_mul, norm_mul]
  calc ‖η (r + 1) x' - η r (red x')‖ * ‖Y (r + 1) s x' i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ * 1 :=
        mul_le_mul (hηc r x') (hY _ _ _ _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_one _

end GlobalTheory.KA
end
