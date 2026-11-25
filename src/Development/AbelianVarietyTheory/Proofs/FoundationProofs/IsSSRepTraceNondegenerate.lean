module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRep

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory

open NumberField IsDedekindDomain in
open Polynomial Matrix in
private theorem eq_zero_of_mulVec_eq_self_of_trace_mul_eq_zero {K : Type} [Field K] [CharZero K]
    {a : ℕ} (B : Subalgebra K (Matrix (Fin a) (Fin a) K)) {z : Matrix (Fin a) (Fin a) K}
    (hzB : z ∈ B) (htr : ∀ y ∈ B, (z * y).trace = 0) {v : Fin a → K} (hv : z *ᵥ v = v) :
    v = 0 := by
  classical
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd z.charpoly
    (Matrix.charpoly_monic z).ne_zero 0
  set m := z.charpoly.rootMultiplicity 0 with hm
  simp only [map_zero, sub_zero] at hpq hq
  have hc : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  set c := q.coeff 0 with hcdef
  set R := aeval z q.divX with hR
  have hq' : aeval z q = z * R + c • 1 := by
    calc aeval z q = aeval z (X * q.divX + C (q.coeff 0)) := by rw [Polynomial.X_mul_divX_add]
      _ = z * R + c • 1 := by
        rw [map_add (f := _), map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have h0 : z ^ m * (z * R + c • 1) = 0 := by
    have := Matrix.aeval_self_charpoly z
    rwa [hpq, map_mul, map_pow, aeval_X, hq'] at this
  have hRz : z * R = R * z := by
    have := congrArg (aeval z) (mul_comm X q.divX)
    simpa [R] using this
  have h1 : z ^ (m + 1) * R = -(c • z ^ m) := by
    rw [pow_succ, mul_assoc]
    rw [mul_add, mul_smul_comm, mul_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hkey : z ^ m = z ^ (m + 1) * ((-c⁻¹) • R) := by
    rw [mul_smul_comm, h1, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hc, neg_smul, one_smul,
      neg_neg]
  set u := (-c⁻¹) • R with hu
  have hcomm : Commute z u := (show Commute z R from hRz).smul_right _
  have hstep : ∀ i, z ^ (m + i) = z ^ (m + i + 1) * u := by
    intro i
    rw [pow_add z m i, hkey, mul_assoc, ← (hcomm.pow_left i).eq, ← mul_assoc, ← pow_add,
      show m + 1 + i = m + i + 1 by omega]
  have hpow : ∀ k, z ^ (m + 1) = z ^ (m + 1 + k) * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, show m + 1 + k = m + (k + 1) by omega, hstep (k + 1), mul_assoc, ← pow_succ',
        show m + (k + 1) + 1 = m + 1 + (k + 1) by omega]
  have hRB : R ∈ B :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hzB) (Polynomial.aeval_mem_adjoin_singleton K z)
  have huB : u ∈ B := B.smul_mem hRB _
  set n := m + 1 with hn
  have hnn := hpow n
  have hc' : u ^ n * z ^ n = z ^ n * u ^ n := (hcomm.pow_pow n n).eq.symm
  have he : IsIdempotentElem (z ^ n * u ^ n) := by
    show z ^ n * u ^ n * (z ^ n * u ^ n) = z ^ n * u ^ n
    rw [mul_assoc, ← mul_assoc (u ^ n) (z ^ n) (u ^ n), hc', ← mul_assoc, ← mul_assoc, ← pow_add,
      ← hnn]
  have hez : z ^ n * u ^ n * z ^ n = z ^ n := by
    rw [mul_assoc, hc', ← mul_assoc, ← pow_add, ← hnn]
  have htre : (z ^ n * u ^ n).trace = 0 := by
    have : z ^ n * u ^ n = z * (z ^ m * u ^ n) := by
      show z ^ (m + 1) * u ^ n = _
      rw [pow_succ', mul_assoc]
    rw [this]
    exact htr _ (B.mul_mem (B.pow_mem hzB m) (B.pow_mem huB n))
  have he0 : z ^ n * u ^ n = 0 := by
    have h1 : IsIdempotentElem (Matrix.toLin' (z ^ n * u ^ n)) := by
      unfold IsIdempotentElem at he ⊢
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
    have h2 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff h1).1
      (by rw [Matrix.trace_toLin'_eq, htre])
    exact Matrix.toLin'.injective (by rw [h2, map_zero])
  have hzn : z ^ n = 0 := by rw [← hez, he0, zero_mul]
  have hvn : ∀ k, (z ^ k) *ᵥ v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  rw [← hvn n, hzn, Matrix.zero_mulVec]


open NumberField IsDedekindDomain in
open Polynomial Matrix in
theorem _root_.GlobalTheory.isSSRep_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] [CharZero K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), _root_.Formalism.MainNotions.N.IsSSRep ρ → (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  intro Γ K _ _ _ a ρ hρ x hx htrace
  exact _root_.GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero K Γ a ρ hρ x hx htrace

end GlobalTheory
