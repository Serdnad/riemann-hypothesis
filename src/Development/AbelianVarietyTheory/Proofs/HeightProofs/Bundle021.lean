module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticFormIdeleValuesMemNhdsOne
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.ToAdditive
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEquivCoverPointsPlacesBaseChange
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FdegEqFinrankResidueField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsIntegralIffMemSpanOneTmulIntegralClosure
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemIntegralClosureOfMemSpan
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize GlobalTheory.WeberCongruence
open scoped IntermediateField

namespace GlobalTheory.WeberCongruenceAnyOrder

theorem weber_congruences : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ (W : ValuationSubring ℂ) (π : 𝓞 K) (p : ℕ), p.Prime → 5 ≤ p → Ideal.absNorm (Ideal.span {π}) = p → ((π : K) : ℂ) ∈ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∈ W ∧ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ^ p ∈ W.nonunits ∧ ∀ (m : ℕ), ¬ p ∣ m → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ∈ W ∧ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (((π : K) : ℂ) * t)) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ^ p ∈ W.nonunits) ∧ ((L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∉ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - 1 ∉ W.nonunits → ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice) := by
  intro K _ _ hK L hL W π p hp h5 hN hπ
  have hcm : ∀ a : 𝓞 K, ∀ z ∈ L.lattice, ((a : K) : ℂ) * z ∈ L.lattice := fun a z hz ↦ by
    obtain ⟨b, rfl⟩ := (hL z).mp hz
    exact (hL _).mpr ⟨a * b, by simp⟩
  have hj := mem_of_isIntegral W
    (CMCurves.isIntegral_latticeJ hK (K.val : K →+* ℂ) L hcm)
  have hn : ‖((π : K) : ℂ)‖ ^ 2 = p := by
    rw [← hN]; exact norm_sq_eq_absNorm hK (K.val : K →+* ℂ) π
  have hπi : IsIntegral ℤ ((π : K) : ℂ) :=
    (RingOfIntegers.isIntegral_coe π).map (K.val : K →+* ℂ).toIntAlgHom
  have hpW : (p : ℂ) ∈ W.nonunits := by
    have := mul_mem_nonunits W hπ
      (mem_of_isIntegral W (hπi.map (starRingEnd ℂ).toIntAlgHom))
    convert this using 1
    change _ = _ * (starRingEnd ℂ) _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  have i2 : (2 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 2) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have i3 : (3 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 3) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have hΔ := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)
  have hc0 : c ≠ 0 := by rintro rfl; exact hΔ (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  generalize scalePeriods L c hc0 = L' at H
  have hΔ' : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = 1 := by
    rw [H.g₂_eq, H.g₃_eq]; field_simp; linear_combination -hc
  have eJ : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = L'.g₂ ^ 3 := by
    rw [H.g₂_eq, ← hc]; field_simp
  have eW : ∀ t, L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t =
      L'.g₂ * L'.g₃ * L'.weierstrassP (c * t) := fun t ↦ by
    rw [H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hc]; field_simp
  have hJ : L'.g₂ ^ 3 ∈ W := by
    have := mul_mem (mul_mem (pow_mem i2 6) (pow_mem i3 3)) hj
    convert this using 1
    rw [← eJ, CMCurves.latticeJ]; ring
  have hg := mem_of_pow_mem W three_ne_zero hJ
  have hh : L'.g₃ ∈ W := by
    refine mem_of_pow_mem W two_ne_zero ?_
    have := mul_mem (pow_mem i3 3) (sub_mem hJ (one_mem W))
    convert this using 1
    linear_combination (-1 / 27 : ℂ) * hΔ'
  have hD : (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)⁻¹ ∈ W := by rw [hΔ', inv_one]; exact one_mem W
  obtain ⟨a, ha, -, -, a2, a3, a4⟩ := GlobalTheory.T.weierstrassP_mul_congr_frobenius_of_primeNorm L' W ((π : K) : ℂ) p i2 i3 hg hh hD hp hpW hπ
    (fun l hl ↦ by
      obtain ⟨z, rfl⟩ : ∃ z, l = c * z := ⟨c⁻¹ * l, by field_simp⟩
      rw [mul_left_comm]
      exact (H _).mpr (hcm π z ((H z).mp hl))) hn
  obtain ⟨c1, c2⟩ := congruences W hp hpW hg hh ha hΔ' a2 a3
  simp only [eW]
  rw [eJ]
  refine ⟨hJ, c1, fun m hpm ↦ ?_⟩
  have hm : 0 < m := Nat.pos_of_ne_zero fun h ↦ hpm (h ▸ dvd_zero p)
  have im := inv_natCast_mem W hp hpW hpm
  obtain ⟨t1, t2⟩ := GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits L' W m i2 i3 hg hh hD hm im
  have s1 : ∀ t, (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (c * t) ∈ L'.lattice := fun t ht ↦ by
    rw [mul_left_comm]; exact (H _).mpr ht
  refine ⟨fun t ht ht' ↦ ?_, fun n1 n2 t t' ht ht0 ht' ht0' h ↦ ?_⟩
  · have hx := t1 (c * t) (s1 t ht) ((H t).not.mpr ht')
    refine ⟨mul_mem (mul_mem hg hh) hx, c2 _ _ hx ?_⟩
    rw [mul_left_comm]
    exact a4 m (c * t) hm im (s1 t ht) ((H t).not.mpr ht')
  · have n3 : L'.g₂ ∉ W.nonunits := fun h ↦ n1 (by
      simpa [pow_succ'] using mul_mem_nonunits W h (pow_mem hg 2))
    have n4 : L'.g₃ ∉ W.nonunits := fun h ↦ n2 (by
      have := mul_mem_nonunits W h (mul_mem (ofNat_mem W 27) hh)
      convert this using 1
      linear_combination hΔ')
    rw [← mul_sub, mul_assoc] at h
    have := t2 (c * t) (c * t') (s1 t ht) ((H t).not.mpr ht0) (s1 t' ht') ((H t').not.mpr ht0')
      (mem_nonunits_of_mul W n4 (mem_nonunits_of_mul W n3 h))
    rwa [← mul_sub, ← mul_add, H, H] at this

end GlobalTheory.WeberCongruenceAnyOrder
end

section

noncomputable section

namespace GlobalTheory.ConstCompare

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7}

theorem choose_two_add (p q : ℕ) :
    p * q + p * (p - 1) / 2 + q * (q - 1) / 2 = (p + q).choose 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← Nat.add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ← ih]
    simp only [Nat.choose_one_right]
    ring

end GlobalTheory.ConstCompare

end
end

section

open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open IsLocalRing GlobalTheory GlobalTheory.ResDegPlace in

theorem _root_.GlobalTheory.T.exists_equiv_coverPoints_places_baseChange : ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (ι : Type) [Finite ι] (L : ι → Type) [∀ c, Field (L c)] [∀ c, Algebra F (L c)] [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)] [∀ c, IsScalarTower R F (L c)] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif (A := A) ϖ → ∀ [∀ ζ : Pts R' A, IsDVRAt ζ] (Ψ : ∀ c, A →ₐ[R'] F' ⊗[F] L c), (∀ c, Function.Surjective (Ψ c)) → (∀ a, (∀ c, Ψ c a = 0) → a = 0) → (∀ c c', c ≠ c' → ∃ a, Ψ c a = 0 ∧ Ψ c' a = 1) → ∃ e : Pts R' A ≃ Σ c, ValPl.PlacesOver R (L c), ∀ ζ, fdeg ζ = (letI := resAlg (F := F) (e ζ).2.1; Module.finrank (IsLocalRing.ResidueField ((vRing (e ζ).2.1).comap (algebraMap F (L (e ζ).1)))) (IsLocalRing.ResidueField (vRing (e ζ).2.1))) ∧ ∃ u : AddValuation (F' ⊗[F] L (e ζ).1) (WithTop ℤ), (∀ g, u ((1 : F') ⊗ₜ[F] g) = (e ζ).2.1 g) ∧ ∀ a, ord ϖ ζ a = u (Ψ (e ζ).1 a) := by
  apply _root_.GlobalTheory.exists_equiv_pts_places_baseChange <;> assumption
end
