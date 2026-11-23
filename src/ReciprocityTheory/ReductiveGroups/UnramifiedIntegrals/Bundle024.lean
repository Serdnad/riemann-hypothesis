module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle004
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
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle016
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle010
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle023
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
import Formalism.TorsionNormIteration.InvIntegralOfClass
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle003
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle008

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

section MapLemmas

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem anIso_map_dblInt (e : PowerSeries K) :
    PowerSeries.map φ (C.dblInt e) = C.dblInt (PowerSeries.map φ e) := by
  ext n
  simp only [C.dblInt, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs
  · simp
  · simp [map_div₀]

theorem anIso_constantCoeff_dblInt (e : PowerSeries K) :
    PowerSeries.constantCoeff (C.dblInt e) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [C.dblInt]

theorem anIso_map_lam (e : PowerSeries K) (s2 : K) :
    PowerSeries.map φ (C.lam e s2) = C.lam (PowerSeries.map φ e) (φ s2) := by
  simp only [C.lam, map_add (f := _), map_mul, map_pow, anIso_map_dblInt, PowerSeries.map_C, PowerSeries.map_X,
    map_div₀, map_ofNat]

theorem anIso_constantCoeff_lam (e : PowerSeries K) (s2 : K) :
    PowerSeries.constantCoeff (C.lam e s2) = 0 := by
  simp [C.lam, anIso_constantCoeff_dblInt]

theorem anIso_map_sgStar [CharZero K] [CharZero K'] (e : PowerSeries K) (s2 : K) :
    PowerSeries.map φ (C.sgStar e s2) = C.sgStar (PowerSeries.map φ e) (φ s2) := by
  have h0 : PowerSeries.constantCoeff (-(C.lam e s2)) = 0 := by
    simp [anIso_constantCoeff_lam]
  have h1 : PowerSeries.map φ (C.mvExp (-(C.lam e s2)))
      = C.mvExp (-(C.lam (PowerSeries.map φ e) (φ s2))) := by
    unfold C.mvExp
    have := PowerSeries.map_subst (h := φ) (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      (PowerSeries.exp K)
    rw [PowerSeries.map_exp] at this
    rw [← anIso_map_lam, ← map_neg]
    exact this
  rw [C.sgStar, map_mul, PowerSeries.map_X, h1, C.sgStar]

theorem anIso_map_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.map φ (C.wpShift e c) = C.wpShift (PowerSeries.map φ e) (φ c) := by
  simp only [C.wpShift, map_add (f := _), map_one, map_mul, map_pow, map_sub, PowerSeries.map_C,
    PowerSeries.map_X]

end MapLemmas

theorem isogenyFormula_map {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
    (φ : K →+* K') (e : PowerSeries K) (s2 : K) {κ : Type} [Fintype κ] (c : κ → K) (al : K)
    (h : C.IsogenyFormula e s2 c al) :
    C.IsogenyFormula (PowerSeries.map φ e) (φ s2) (fun P => φ (c P)) (φ al) := by
  have h' := congrArg (PowerSeries.map φ) h
  unfold C.IsogenyFormula
  simp only [map_mul, map_pow, map_prod, PowerSeries.map_X, PowerSeries.map_C, anIso_map_wpShift,
    anIso_map_sgStar, ← PowerSeries.rescale_map] at h'
  rw [map_pow]
  exact h'

theorem iso_formula (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    C.IsogenyFormula (A.wpReg (A.shortW (ι L.g₂) (ι L.g₃))) (ι (F.s2 L))
      (fun P : S => ι (L.weierstrassP (P : ℂ))) (ι α) := by
  rw [wp_bridge]
  exact isogenyFormula_map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) (F.s2 L)
    (fun P : S => L.weierstrassP (P : ℂ)) α (F.isogenyFormulaInstance L α S hα hst hS)

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem wpNum_coeff_mem (k : Subfield ℂ) {g2 g3 : ℂ} (h2 : g2 ∈ k) (h3 : g3 ∈ k) (n : ℕ) :
    PowerSeries.coeff n (wpNum g2 g3) ∈ k := by
  have h := (seriesMap k ℂ k.subtype ⟨g2, h2⟩ ⟨g3, h3⟩ 0 0).1
  have h' : wpNum g2 g3 = PowerSeries.map k.subtype (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩) := h.symm
  rw [h', PowerSeries.coeff_map]
  exact (PowerSeries.coeff n (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩)).2

theorem kerPoly_mem (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (k : Subfield ℂ) (h2 : L.g₂ ∈ k) (h3 : L.g₃ ∈ k) (hk : α ∈ k) :
    ∀ i, (rootPoly (xsOf L T)).coeff i ∈ k := by
  apply sqrt_poly k _ (rootPoly_monic _)
  refine proj_trick k (wpNum L.g₂ L.g₃) (PowerSeries.rescale α (wpNum L.g₂ L.g₃))
    (wpNum_coeff_mem k h2 h3) ?_ ?_ (veluNum L.g₂ L.g₃ (xsOf L T)) (rootPoly (xsOf L T) ^ 2)
    (2 * (xsOf L T).card) (veluNum_natDegree_le _ _ _) ((rootPoly_monic _).pow 2) ?_
    (veluNum_coprime _ _ _ fun x hx => hT.fW_ne hx) (velu_series L α T hα hs hT)
  · intro n
    rw [PowerSeries.coeff_rescale]
    exact k.mul_mem (k.pow_mem hk n) (wpNum_coeff_mem k h2 h3 n)
  · simp [wpNum]
  · rw [(rootPoly_monic _).natDegree_pow, rootPoly_natDegree]

theorem prod_mem_of_rootPoly {E : Type} [Field E] (k : Subfield E) (xs : Finset E)
    (h : ∀ i, (rootPoly xs).coeff i ∈ k) : ∏ x ∈ xs, x ∈ k := by
  have h0 : (rootPoly xs).coeff 0 = (-1) ^ xs.card * ∏ x ∈ xs, x := by
    rw [Polynomial.coeff_zero_eq_eval_zero, rootPoly, Polynomial.eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => (neg_one_mul x).symm
  have h1 : ∏ x ∈ xs, x = (-1) ^ xs.card * (rootPoly xs).coeff 0 := by
    rw [h0, ← mul_assoc, ← mul_pow]
    simp
  rw [h1]
  exact k.mul_mem (k.pow_mem (k.neg_mem k.one_mem) _) (h 0)

end ReciprocityTheory.ChartRestriction.L1
end
end
