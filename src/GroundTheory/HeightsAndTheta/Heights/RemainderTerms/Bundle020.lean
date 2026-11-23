module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle008
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

theorem FlagProdPrimesDvd.proof : FlagProdPrimesDvd.Statement := by
  intro R _ _ ι s p x
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert t s ht ih =>
    intro hp hne hdvd
    have hs : (∏ i ∈ s, p i) ∣ x :=
      ih (fun i hi => hp i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hne i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
        (fun i hi => hdvd i (mem_insert_of_mem hi))
    obtain ⟨y, hy⟩ := hs
    have hpt : Prime (p t) := hp t (mem_insert_self t s)
    have hnd : ¬ p t ∣ ∏ i ∈ s, p i := by
      rw [Prime.dvd_finsetProd_iff hpt]
      rintro ⟨j, hj, hdj⟩
      refine hne t (mem_insert_self t s) j (mem_insert_of_mem hj) ?_ hdj
      rintro rfl
      exact ht hj
    have hty : p t ∣ y := by
      have h := hdvd t (mem_insert_self t s)
      rw [hy] at h
      exact (hpt.dvd_or_dvd h).resolve_left hnd
    rw [prod_insert ht, hy, mul_comm (p t)]
    exact mul_dvd_mul_left _ hty

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem FlagRestrictHomogeneous.proof : FlagRestrictHomogeneous.Statement := by
  intro f N τ R k hR
  have h := hR.aeval (fun p : Fin f × Fin N => if p.1 = τ then X p.2 else 0) (n := 1) (by
    intro p
    split_ifs
    · exact isHomogeneous_X ℚ _
    · exact isHomogeneous_zero _ _ _)
  rw [one_mul] at h
  exact h

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagRestrictPowerSum.proof : FlagRestrictPowerSum.Statement := by
  intro f N k τ σ hk
  have hk0 : k ≠ 0 := by omega
  unfold blockPowerSum restrictToBlock

  simp only [map_sum, map_pow, aeval_X]
  split_ifs with h
  · subst h
    simp [psum]
  · simp [zero_pow hk0]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

noncomputable section

theorem FlagStaircaseOrbit.bijective_of_injective {f N : ℕ} (γ : Fin f × Fin N →₀ ℕ) (τ : Fin f)
    (hlt : ∀ i, γ (τ, i) < N) (hinj : Function.Injective fun i : Fin N => γ (τ, i)) :
    Function.Bijective fun i : Fin N => (⟨γ (τ, i), hlt i⟩ : Fin N) := by
  refine Finite.injective_iff_bijective.mp ?_
  intro i j h
  exact hinj (congrArg Fin.val h)

theorem FlagStaircaseOrbit.proof : FlagStaircaseOrbit.Statement := by
  intro f N α β hα hβ iα iβ
  let A : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective α τ (hα τ) (iα τ))
  let B : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective β τ (hβ τ) (iβ τ))
  refine ⟨fun τ => (B τ).trans (A τ).symm, fun τ i => ?_⟩
  have h : A τ ((A τ).symm (B τ i)) = B τ i := Equiv.apply_symm_apply _ _
  have h' := congrArg Fin.val h
  exact h'

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagSymmetricMulAntisym.proof : FlagSymmetricMulAntisym.Statement := by
  intro f N P H hP
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, hP w, mul_smul_comm]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ l ∈ Finset.Icc 1 N, g l = ∑ i : Fin N, g (i.val + 1) := by
  have hI : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1)), hI, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  exact Finset.sum_congr rfl (fun i _ => by rw [add_comm])

theorem FlagPowerSumPreimage.proof : FlagPowerSumPreimage.Statement := by
  intro N T hT
  choose Sf hSf using fun l => Flag.exists_powerSumHom_eq (hT l)
  refine ⟨∑ i : Fin N, X i * Sf (i.val + 1), ?_, ?_⟩

  · rw [sum_Icc_one_eq_sum_fin N (fun l => psum (Fin N) ℚ l * T l), map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, hSf]
    simp [powerSumHom]
  · intro k hk1 hkN
    set j : Fin N := ⟨k - 1, by omega⟩ with hj
    rw [coeff_sum, Finset.sum_eq_single j]
    · rw [coeff_X_mul', if_pos (by simp), tsub_self, ← constantCoeff_eq,
        ← Flag.constantCoeff_powerSumHom, hSf]
      have : j.val + 1 = k := by simp [hj]; omega
      rw [this]
    · intro i _ hij
      rw [coeff_X_mul', if_neg]
      simp only [Finsupp.mem_support_iff, ne_eq]
      rw [Finsupp.single_apply, if_neg (fun h => hij h.symm)]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem FlagQuotientHomogeneous.proof : FlagQuotientHomogeneous.Statement := by
  intro σ A R m k hA0 hA hAR
  have hzero : ∀ j, j ≠ k → homogeneousComponent j R = 0 := by
    intro j hj
    have h1 := HomogeneousComponentMul.proof σ ℚ A R m (m + j) hA
    rw [if_pos (Nat.le_add_right m j), Nat.add_sub_cancel_left] at h1
    have h2 : homogeneousComponent (m + j) (A * R) = 0 := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hAR),
        if_neg (by omega)]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hA0
  have hR : R = homogeneousComponent k R := by
    conv_lhs => rw [← sum_homogeneousComponent R]
    refine Finset.sum_eq_single k (fun j _ hj => hzero j hj) (fun hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    exact homogeneousComponent_eq_zero k R (by omega)
  rw [hR]
  exact homogeneousComponent_isHomogeneous k R

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem FlagVandermondeHomogeneous.proof : FlagVandermondeHomogeneous.Statement := by
  intro f N
  have hblock : ∀ τ : Fin f,
      (vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N))).IsHomogeneous
        (N * (N - 1) / 2) := fun τ =>
    VandermondeOfHomogeneous.proof _ _ N _ (fun i => isHomogeneous_X ℚ (τ, i))
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
    (fun τ => vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N)))
    (fun _ => N * (N - 1) / 2) (fun τ _ => hblock τ)
  simpa [blockVandermonde, topDegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] using h

end GroundTheory.Heights₂.Heights.RestTerms
end
