module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
public import Mathlib.NumberTheory.SumFourSquares
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

section

namespace PositivityTheory.PrwZar

theorem exists_quat (n : ℕ) : ∃ α : Matrix (Fin 4) (Fin 4) ℤ,
    α.transpose * α = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
    α * α.transpose = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  have hn : (n : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]
    push_cast
    ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩ <;>
  · rw [hn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

end PositivityTheory.PrwZar
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem idem_eq_zero {K H : Type} [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    {f : H} (hf : IsIdempotentElem f) (h : ∀ x : H →ₐ[K] K, x f = 0) : f = 0 := by
  by_contra hne
  have hne1 : Ideal.span {1 - f} ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    apply hne
    have h0 : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hf.eq, sub_self]
    exact htop.mul_left_eq_zero.1 h0
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne1
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (H ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  haveI : Algebra.IsIntegral K (H ⧸ M) := Algebra.IsIntegral.of_finite K (H ⧸ M)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := H ⧸ M)
  let e : K ≃ₐ[K] H ⧸ M := AlgEquiv.ofBijective (Algebra.ofId K (H ⧸ M)) hb
  let x : H →ₐ[K] K := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M)
  have h1 : Ideal.Quotient.mk M f = 1 := by
    have hmem : 1 - f ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : Ideal.Quotient.mk M (1 - f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  have hx1 : x f = 1 := by
    change e.symm (Ideal.Quotient.mkₐ K M f) = 1
    rw [Ideal.Quotient.mkₐ_eq_mk, h1, map_one]
  have hx := h x
  rw [hx1] at hx
  exact one_ne_zero hx

end PositivityTheory.PrwZar.Qi
end
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

def pw (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : ℕ → (H →ₐ[K] H)
  | 0 => (Algebra.ofId K H).comp ε
  | n + 1 => (Algebra.TensorProduct.lmul' K).comp ((Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H)).comp Δ)

def CounitL (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H)).comp Δ) = AlgHom.id K H

def CounitR (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε)).comp Δ) = AlgHom.id K H

def KilledCore : Prop :=
  ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K), CounitL Δ ε → CounitR Δ ε →
    (∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b)) →
    (∃ m : ℕ, 0 < m ∧ ∀ x : H →ₐ[K] K, x.comp (pw Δ ε m) = ε) →
    ∃ N : ℕ, 0 < N ∧ pw Δ ε N = pw Δ ε 0

end PositivityTheory.PrwZar.Qi
end
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem exists_stable_pow {K H : Type} [Field K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (I : Ideal H) : ∃ (k : ℕ) (e : H), IsIdempotentElem e ∧ I ^ k = Ideal.span {e} ∧ ∀ j, k ≤ j → I ^ j = I ^ k := by
  haveI : IsArtinianRing H := isArtinian_of_tower K inferInstance
  haveI : IsNoetherianRing H := isNoetherian_of_tower K inferInstance
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := H) (M := H)
    ⟨fun n => OrderDual.toDual (I ^ n), fun a b h => Ideal.pow_le_pow_right h⟩
  have hst : ∀ j, n ≤ j → I ^ j = I ^ n := fun j hj => congrArg OrderDual.ofDual (hn j hj).symm
  have hidem : IsIdempotentElem (I ^ n) := by
    unfold IsIdempotentElem
    rw [← pow_add]
    exact hst (n + n) (by omega)
  obtain ⟨e, he, hI⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).1 hidem
  exact ⟨n, e, he, hI.trans Ideal.submodule_span_eq, hst⟩

end PositivityTheory.PrwZar.Qi
end
end
