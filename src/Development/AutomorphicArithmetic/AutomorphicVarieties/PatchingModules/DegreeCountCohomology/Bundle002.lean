module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle001
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem dd_sum_zero {X : Type} [CommRing X] {g : ℕ} (u v : DD X g) (ua : u.a = 0) (va : v.a = 0)
    (ue : u.ep' = 0) (ve : v.ep' = 0) : u * v = 0 := by
  apply DD.ext
  · simp [DD.mul_a, ua]
  · funext j
    simp [DD.mul_ep, ua, va]
  · funext j
    simp [DD.mul_ep', ue, ve]
  · simp [DD.mul_eta, ua, va, ue, ve]

private theorem epM_sq {X : Type} [CommRing X] {g n : ℕ} (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * DD.epM Z' = 0 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun c _ => dd_sum_zero _ _ rfl rfl rfl rfl

private theorem epM_tr {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    (DD.epM Z)ᵀ = DD.epM fun j => (Z j)ᵀ := rfl

private theorem epM_neg {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    (DD.epM fun j => -Z j) = -DD.epM Z := by
  ext a b <;> simp [DD.epM]

theorem UpperTheory.V.Pa.rho1 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ (∀ g, (k.ρ1 X g)ᵀ * k.ρ1 X (F.conj g) = algebraMap x.A (DD X k.g) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD X k.g))) ∧ (∀ v, k.wi1 X v * k.w1 X v = 1 ∧ k.w1 X v * k.wi1 X v = 1) ∧ ∀ u, ∀ g ∈ F.Iu u, k.ρ1 X g = 1 := by
  intro l _ F n x k X _ _
  obtain ⟨h1, hmul, -, hw⟩ := Det.rho1Hom k X
  refine ⟨h1, hmul, fun g => ?_, fun v => ⟨(hw v).2, (hw v).1⟩, fun u g hg => ?_⟩
  · have hc : (fun j => (k.κ j (F.conj g)).map (algebraMap x.A X)) =
        fun j => -(((k.κ j g).map (algebraMap x.A X))ᵀ) := by
      funext j
      rw [(k.mem j).2.2.2.1 g]
      ext a b
      simp
    have hA : ((DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) : Matrix (Fin n) (Fin n) (DD X k.g))ᵀ *
        DD.epM (fun j => -(((k.κ j g).map (algebraMap x.A X))ᵀ)) = 0 := by
      rw [epM_neg, Matrix.mul_neg, epM_tr, epM_sq, neg_zero]
    have hρ : (x.ρX (DD X k.g) g)ᵀ * x.ρX (DD X k.g) (F.conj g) =
        algebraMap x.A (DD X k.g) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) •
          (1 : Matrix (Fin n) (Fin n) (DD X k.g)) := by
      have hf := x.form g
      simp only [Units.val_one, Matrix.mul_one] at hf
      unfold NP.ρX
      rw [← Matrix.transpose_map, ← Matrix.map_mul, hf]
      refine Matrix.ext fun i j => ?_
      by_cases h : i = j
      · subst h
        simp [Matrix.one_apply]
      · simp [Matrix.one_apply, h]
    unfold Kap.ρ1
    rw [hc, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one]
    have h2 : (1 + (DD.epM fun j => (k.κ j g).map (algebraMap x.A X))ᵀ) *
        (1 + DD.epM (fun j => -(((k.κ j g).map (algebraMap x.A X))ᵀ))) = 1 := by
      rw [add_mul, one_mul, mul_add, mul_one, hA, add_zero, epM_neg, epM_tr]
      abel
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + _), h2, Matrix.one_mul, hρ]
  · have hz : ∀ j, k.κ j g = 0 := fun j => (k.mem j).2.2.2.2.1 u g hg
    have hm : (mat x.ρ) g = 1 := by simp [mat, x.ine u g hg]
    have he : (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) = 0 := by
      refine Matrix.ext fun a b => ?_
      ext <;> simp [hz, DD.epM]
    unfold Kap.ρ1 NP.ρX
    rw [hm, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, he, add_zero]
end

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.finAm :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m g : ℕ), Finite (x.Am m) ∧ Nat.card (x.Am m) = Nat.card x.K ^ m ∧ Finite (DD (x.Am m) g) ∧ (∀ y : x.Am m, l • y = 0) ∧ (∀ y : DD (x.Am m) g, l • y = 0) ∧ (algebraMap x.A (x.Am m) x.t) ^ m = 0 ∧ (algebraMap x.A (DD (x.Am m) g) x.t) ^ m = 0 ∧ (l ≠ 2 → IsUnit (2 : x.A)) ∧ CharP x.K l := by
  intro l _ F n x m g
  obtain ⟨h1, h2, -, -, h5, -⟩ := UpperTheory.V.Pa.am_fin l F n x m g
  have hA : (l : x.A) = 0 := h5
  have e : (l : x.K) = 0 := by
    have := congrArg (PowerSeries.constantCoeff (R := x.K)) hA
    rwa [map_natCast, map_zero] at this
  have hc : CharP x.K l := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 e
  have hAm : (l : x.Am m) = 0 := by
    rw [← map_natCast (algebraMap x.A (x.Am m)), hA, map_zero]
  have hDD : (l : DD (x.Am m) g) = 0 := by
    rw [← map_natCast (DD.C (X := x.Am m) (g := g)), hAm, map_zero]
  haveI := h1
  have ht : (algebraMap x.A (x.Am m) x.t) ^ m = 0 := by
    rw [← map_pow, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  refine ⟨h1, h2, Finite.of_equiv _ DD.equiv.symm, fun y => by rw [nsmul_eq_mul, hAm, zero_mul],
    fun y => by rw [nsmul_eq_mul, hDD, zero_mul], ht, ?_, ?_, hc⟩
  · show (DD.C (algebraMap x.A (x.Am m) x.t)) ^ m = 0
    rw [← map_pow, ht, map_zero]
  · intro hl
    show IsUnit (2 : PowerSeries x.K)
    rw [PowerSeries.isUnit_iff_constantCoeff, map_ofNat]
    apply Ne.isUnit
    intro h2
    have h2' : ((2 : ℕ) : x.K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff x.K l] at h2'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2')
end
