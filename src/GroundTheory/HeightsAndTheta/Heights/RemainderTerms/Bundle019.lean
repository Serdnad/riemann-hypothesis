module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

namespace FlagDiffPrime

variable {σ : Type} [DecidableEq σ]

def collapse (a b : σ) : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
  aeval fun i => if i = a then X b else X i

theorem collapse_X_sub (a b : σ) : collapse a b (X a - X b : MvPolynomial σ ℚ) = 0 := by
  simp [collapse]

theorem dvd_sub_collapse (a b : σ) (Q : MvPolynomial σ ℚ) :
    (X a - X b : MvPolynomial σ ℚ) ∣ Q - collapse a b Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [collapse]
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul]
    have e : p * X i - collapse a b p * collapse a b (X i) =
        (p - collapse a b p) * X i + collapse a b p * (X i - collapse a b (X i)) := by ring
    rw [e]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    by_cases h : i = a
    · rw [h]; simp [collapse]
    · simp [collapse, h]

theorem collapse_eq_zero_of_dvd (a b : σ) {P : MvPolynomial σ ℚ}
    (h : (X a - X b : MvPolynomial σ ℚ) ∣ P) : collapse a b P = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, collapse_X_sub, zero_mul]

theorem dvd_of_collapse_eq_zero (a b : σ) {P : MvPolynomial σ ℚ}
    (h : collapse a b P = 0) : (X a - X b : MvPolynomial σ ℚ) ∣ P := by
  simpa [h] using dvd_sub_collapse a b P

theorem proof : FlagDiffPrime.Statement := by
  intro σ _ a b hab
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_ne_zero]
    exact fun h => hab (X_injective h)
  · intro hu
    have hu' := hu.map (collapse a b)
    rw [collapse_X_sub] at hu'
    exact not_isUnit_zero hu'
  · intro A B h
    have h0 := collapse_eq_zero_of_dvd a b h
    rw [map_mul, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Or.inl (dvd_of_collapse_eq_zero a b h0)
    · exact Or.inr (dvd_of_collapse_eq_zero a b h0)

end FlagDiffPrime

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagRestrictConstantCoeff.proof : FlagRestrictConstantCoeff.Statement := by
  intro f N τ R
  induction R using MvPolynomial.induction_on with
  | C a => simp [restrictToBlock]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, constantCoeff_X, mul_zero]
    have hX : constantCoeff (restrictToBlock f N τ (X i)) = 0 := by
      simp only [restrictToBlock, aeval_X]
      split_ifs <;> simp
    rw [hX, mul_zero]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagSwapDivisible.dvd_sub_substitute {R σ : Type} [CommRing R] [DecidableEq σ] (a b : σ)
    (Q : MvPolynomial σ R) :
    (X a - X b : MvPolynomial σ R) ∣
      Q - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p k hp =>
    rw [map_mul, aeval_X]
    have hk : (X a - X b : MvPolynomial σ R) ∣
        X k - (if k = a then (X b : MvPolynomial σ R) else X k) := by
      split_ifs with h
      · subst h; exact dvd_rfl
      · simp
    have e : p * X k - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
          (if k = a then (X b : MvPolynomial σ R) else X k) =
        (p - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p) * X k +
          aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
            (X k - (if k = a then (X b : MvPolynomial σ R) else X k)) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)

theorem FlagSwapDivisible.proof : FlagSwapDivisible.Statement := by
  intro σ _ P a b hab hP
  set g : σ → MvPolynomial σ ℚ := fun v => if v = a then X b else X v with hg
  have hswap : g ∘ Equiv.swap a b = g := by
    funext v
    simp only [Function.comp_apply, hg]
    rcases eq_or_ne v a with rfl | hva
    · simp [Equiv.swap_apply_left, hab.symm]
    · rcases eq_or_ne v b with rfl | hvb
      · simp [Equiv.swap_apply_right, hva]
      · simp [Equiv.swap_apply_of_ne_of_ne hva hvb, hva]
  have hzero : aeval g P = 0 := by
    have h1 : aeval g P = -aeval g P := by
      calc aeval g P = aeval (g ∘ Equiv.swap a b) P := by rw [hswap]
        _ = aeval g (rename (Equiv.swap a b) P) := (aeval_rename _ _ _).symm
        _ = -aeval g P := by rw [hP, map_neg]
    have h2 : aeval g P + aeval g P = 0 := by
      nth_rewrite 2 [h1]; exact add_neg_cancel _
    have h3 : (2 : MvPolynomial σ ℚ) * aeval g P = 0 := by rw [two_mul]; exact h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hd := FlagSwapDivisible.dvd_sub_substitute a b P
  rw [← hg, hzero, sub_zero] at hd
  exact hd

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagRestrictDecomposition.proof (h1 : FlagRestrictPowerSum.Statement) :
    FlagRestrictDecomposition.Statement := by
  intro f N τ R

  rw [map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1

  rw [map_sum]
  simp only [map_mul, h1 f N l τ _ hl1, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ)]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem rename_comp_restrictToBlock (f N : ℕ) (τ : Fin f) (π : Equiv.Perm (Fin N)) :
    (rename π).comp (restrictToBlock f N τ) =
      (restrictToBlock f N τ).comp (blockPermute f N (Function.update 1 τ π)) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨σ, i⟩
  by_cases h : σ = τ
  · subst h
    simp [restrictToBlock, blockPermute]
  · simp [restrictToBlock, blockPermute, h]

theorem FlagRestrictSymmetric.proof : FlagRestrictSymmetric.Statement := by
  intro f N τ R hR π
  have key := congrArg (fun φ : RootRing f N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ R)
    (rename_comp_restrictToBlock f N τ π)
  simp only [AlgHom.comp_apply] at key
  rw [key, hR]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem FlagInjSumBound.finset_sum_bound (S : Finset ℕ) :
    ∑ i ∈ Finset.range S.card, i ≤ ∑ x ∈ S, x ∧
      (∑ x ∈ S, x = ∑ i ∈ Finset.range S.card, i → S ⊆ Finset.range S.card) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S' hlt ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hm : m ∉ S' := fun h => lt_irrefl m (hlt m h)
    have hsub : S' ⊆ Finset.range m := fun x hx => Finset.mem_range.2 (hlt x hx)
    have hcard : S'.card ≤ m := by simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hm, Finset.sum_range_succ, Finset.sum_insert hm]
    refine ⟨by omega, fun heq => ?_⟩
    have hmeq : m = S'.card := by omega
    have hS' := ih₂ (by omega)
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_range.2 (by omega)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hS' hx)))

theorem FlagInjSumBound.proof : FlagInjSumBound.Statement := by
  intro N g hg
  classical
  set S := Finset.univ.image g with hSdef
  have hcard : S.card = N := by
    rw [hSdef, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i, g i = ∑ x ∈ S, x := by
    rw [hSdef, Finset.sum_image (fun i _ j _ h => hg h)]
  obtain ⟨h₁, h₂⟩ := FlagInjSumBound.finset_sum_bound S
  rw [hcard, Finset.sum_range_id] at h₁ h₂
  rw [hsum]
  refine ⟨h₁, fun heq i => ?_⟩
  have hi : g i ∈ S := Finset.mem_image_of_mem g (Finset.mem_univ i)
  exact Finset.mem_range.1 (h₂ heq hi)

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem antisymmetrize_finset_sum (f N : ℕ) {ι : Type*} (s : Finset ι) (g : ι → RootRing f N) :
    antisymmetrize f N (∑ i ∈ s, g i) = ∑ i ∈ s, antisymmetrize f N (g i) := by

  simp only [antisymmetrize, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

theorem FlagAntisymDecomposition.proof (h1 : FlagSymmetricMulAntisym.Statement)
    (h2 : FlagPowerSumSymmetric.Statement) : FlagAntisymDecomposition.Statement := by
  intro f N F G Q R hF hR
  rw [hF, Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_left_comm, h1 f N _ _ (h2 f N l σ), hR, mul_left_comm]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagAntisymHomogeneous.proof : FlagAntisymHomogeneous.Statement := by
  intro f N H d hH
  have hmem : ∀ w : Fin f → Equiv.Perm (Fin N),
      blockSign f N w • blockPermute f N w H ∈ homogeneousSubmodule (Fin f × Fin N) ℚ d := by
    intro w
    refine Submodule.smul_mem _ _ ?_
    rw [mem_homogeneousSubmodule]
    exact hH.rename_isHomogeneous
  have hsum : antisymmetrize f N H ∈ homogeneousSubmodule (Fin f × Fin N) ℚ d :=
    Submodule.sum_mem _ (fun w _ => hmem w)
  rwa [mem_homogeneousSubmodule] at hsum

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

def blockPermuteEquiv (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    Fin f × Fin N ≃ Fin f × Fin N where
  toFun p := (p.1, w p.1 p.2)
  invFun p := (p.1, (w p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem FlagCoeffBlockPermute.proof : FlagCoeffBlockPermute.Statement := by
  intro f N w P α
  classical
  set E := blockPermuteEquiv f N w with hE
  set β : Fin f × Fin N →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2) with hβ
  have hmap : Finsupp.mapDomain E β = α := by
    ext q
    obtain ⟨p, rfl⟩ := E.surjective q
    rw [Finsupp.mapDomain_apply_of_injective E.injective]
    simp [hβ, hE, blockPermuteEquiv]
  have hren : blockPermute f N w P = rename E P := rfl
  rw [hren, ← hmap, coeff_rename_mapDomain E E.injective]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagDiffNotDvd.proof : FlagDiffNotDvd.Statement := by
  intro σ _ a b c d hab hcd h1 h2 hdvd
  let ψ : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
    aeval (fun i => X (if i = a then b else i))
  have hψ : ∀ i, ψ (X i) = X (if i = a then b else i) := fun i => by
    simp only [ψ, aeval_X]
  obtain ⟨q, hq⟩ := hdvd
  have h := congrArg ψ hq
  rw [map_mul, map_sub, map_sub, hψ, hψ, hψ, hψ, if_pos rfl, if_neg (Ne.symm hab), sub_self,
    zero_mul, sub_eq_zero] at h
  have hcd' := X_injective h
  by_cases hc : c = a <;> by_cases hd : d = a
  · exact hcd (hc.trans hd.symm)
  · rw [if_pos hc, if_neg hd] at hcd'
    exact h1 ⟨hc.symm, hcd'⟩
  · rw [if_neg hc, if_pos hd] at hcd'
    exact h2 ⟨hd.symm, hcd'.symm⟩
  · rw [if_neg hc, if_neg hd] at hcd'
    exact hcd hcd'

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralTopComponent.proof (h1 : FlagVandermondeHomogeneous.Statement) :
    FlagIntegralTopComponent.Statement := by
  intro f N Φ
  unfold flagIntegral
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdeg : α.degree = topDegree f N := by
    rw [Finsupp.degree_eq_weight_one]
    exact h1 f N (mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent, if_pos hdeg]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem FlagHomogeneousComponentMul.proof : FlagHomogeneousComponentMul.Statement := by
  intro σ P G k n hP
  exact HomogeneousComponentMul.proof σ ℚ P G k n hP

end GroundTheory.Heights₂.Heights.RestTerms
end
