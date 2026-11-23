module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle005
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle002
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

theorem OrbitFiniteSum.proof (hD : OrbitDegreeRatio.Statement) (hL : OrbitLocalSum.Statement)
    (hZ : OrbitCenterZero.Statement) : OrbitFiniteSum.Statement := by
  classical
  intro ι _ _ _ n A x s hx hs
  obtain ⟨a, _, hsa, hsW⟩ := id hs
  have ht : evalCone (coordVec x) s ≠ 0 := evalCone_coordVec_ne_zero x s a hsa hsW
  have hsupp2 : (Function.support fun v : FinitePlace (coordField x) ↦
      Real.log (v (evalCone (coordVec x) s))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  have hS := ((finite_support_height A x hx).union hsupp2).subset
    (Function.support_sub (fun v : FinitePlace (coordField x) ↦ finiteTerm A v (coordVec x)) _)
  have hsubF : Function.support (fun v : FinitePlace (coordField x) ↦
      finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) ⊆ hS.toFinset := by
    simp
  have hK : (0 : ℝ) < Module.finrank ℚ (coordField x) := by exact_mod_cast Module.finrank_pos
  have hloc : ∀ V, ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ v ∈ hS.toFinset, if orbitCenter x v = V then
        finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) else 0 := by
    intro V
    rw [finsum_mem_def, finsum_eq_sum_of_support_subset _
      (by rw [Set.support_indicator]; exact Set.inter_subset_right.trans hsubF)]
    exact Finset.sum_congr rfl fun v _ ↦ by simp [Set.indicator_apply]
  have hterm : ∀ V ∈ (Geo.divSupp_finite (orbitIdeal x) s).toFinset,
      (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V)) =
        (∑ v ∈ hS.toFinset, if orbitCenter x v = V then
          finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) else 0) *
          (Module.finrank ℚ (ratioField x) / Module.finrank ℚ (coordField x) : ℝ) := fun V hV ↦ by
    have h := hL ι n A x s hx hs V ((Geo.divSupp_finite _ _).mem_toFinset.mp hV)
    rw [hloc V] at h
    rw [mul_div_assoc', eq_div_iff hK.ne', mul_comm _ (Module.finrank ℚ (ratioField x) : ℝ), ← h,
      mul_comm]
  rw [finsum_mem_eq_finite_toFinset_sum _ (Geo.divSupp_finite _ _), Finset.sum_congr rfl hterm,
    ← Finset.sum_mul, Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun v _ ↦ by
      split_ifs with h
      · rfl
      · exact (hZ ι n A x s hx hs v fun h' ↦ h ((Geo.divSupp_finite _ _).mem_toFinset.mpr h')).symm,
    ← finsum_eq_sum_of_support_subset _ hsubF, hD ι n x hx]
  ring

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem exists_int_poly_coeff_zero_ne_zero {τ : AlgebraicClosure ℚ} (hτ : τ ≠ 0) :
    ∃ P : Polynomial ℤ, P.coeff 0 ≠ 0 ∧ Polynomial.aeval τ P = 0 := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  obtain ⟨Q, hQ, hQτ⟩ :=
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic τ⁻¹).restrictScalars (R := ℤ)
  have : Invertible τ⁻¹ := invertibleOfNonzero (inv_ne_zero hτ)
  refine ⟨Q.reverse, by rw [Polynomial.coeff_zero_reverse]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ, ?_⟩
  have h := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℤ (AlgebraicClosure ℚ)) τ⁻¹ Q).mpr hQτ
  rwa [invOf_eq_inv, inv_inv] at h

theorem OrbitDivVertical.proof : OrbitDivVertical.Statement := by
  intro ι _ _ _ n A x s _ hs V hV hH
  obtain ⟨a, -, hsa, hsW⟩ := hs
  obtain ⟨hVmin, hVrel⟩ := hV
  have hVp : V.IsPrime := hVmin.1.1
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hsV : s ∈ V := hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  choose c hc using hVrel
  set M : MvPolynomial (Coord n) ℤ := chartMonomial c a with hMdef
  have hMV : M ∉ V := by
    rw [hMdef, chartMonomial]
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hVp)).mp h
    exact hc k (hVp.mem_of_pow_mem _ hk)
  have hMa : Geo.IsMultiHomog (ι := blockIdx n) M a :=
    (geoMultiHomog_iff _ a).mpr (isWeightedHomogeneous_chartMonomial c a)
  set y := flatCone x
  set T : MvPolynomial ι (AlgebraicClosure ℚ) := ∏ k, X k ^ a k
  set σ := eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) y s
  set μ := eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) y M
  have hφs : Geo.mConeMap (ι := blockIdx n) y s = C σ * T := mConeMap_of_isMultiHomog y s a hsa
  have hφM : Geo.mConeMap (ι := blockIdx n) y M = C μ * T := mConeMap_of_isMultiHomog y M a hMa
  have hσ : σ ≠ 0 := fun h ↦ hsW (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, hφs, h, map_zero, zero_mul])
  have hμ : μ ≠ 0 := fun h ↦ hMV (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, hφM, h, map_zero, zero_mul]))
  obtain ⟨P, hP0, hP⟩ := exists_int_poly_coeff_zero_ne_zero (div_ne_zero hσ hμ)
  set m := P.natDegree
  let f : ℕ → MvPolynomial (Coord n) ℤ := fun j ↦ C (P.coeff j) * s ^ j * M ^ (m - j)
  have hfW : ∑ j ∈ Finset.range (m + 1), f j ∈ orbitIdeal x := by

    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, map_sum]
    have hterm : ∀ j ∈ Finset.range (m + 1), Geo.mConeMap (ι := blockIdx n) y (f j) =
        C (algebraMap ℤ (AlgebraicClosure ℚ) (P.coeff j) * (σ / μ) ^ j * μ ^ m) * T ^ m := by
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have e1 : (σ / μ) ^ j * μ ^ m = σ ^ j * μ ^ (m - j) := by
        rw [← Nat.add_sub_cancel' hjm, pow_add, Nat.add_sub_cancel_left, div_pow, ← mul_assoc,
          div_mul_cancel₀ _ (pow_ne_zero _ hμ)]
      have e2 : T ^ m = T ^ j * T ^ (m - j) := by rw [← pow_add, Nat.add_sub_cancel' hjm]
      simp only [f, map_mul, map_pow, hφs, hφM, MvPolynomial.algHom_C, mul_assoc, e1, e2]
      simp only [eq_intCast, map_intCast, mul_pow]
      ring

    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, ← Finset.sum_mul]
    have hPτ : ∑ j ∈ Finset.range (m + 1), algebraMap ℤ (AlgebraicClosure ℚ) (P.coeff j) *
        (σ / μ) ^ j = 0 := by
      rw [← hP, Polynomial.aeval_eq_sum_range]
      simp [Algebra.smul_def]
      rfl
    rw [hPτ, zero_mul, map_zero, zero_mul]
  have hrest : ∑ j ∈ Finset.range m, f (j + 1) ∈ V :=
    Ideal.sum_mem _ fun j _ ↦ by
      simp only [f]
      rw [pow_succ]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hsV))
  have h0 : f 0 ∈ V := by
    have h := Ideal.sub_mem V (hWV hfW) hrest
    rwa [Finset.sum_range_succ', add_sub_cancel_left] at h
  simp only [f, pow_zero, mul_one, Nat.sub_zero] at h0
  rcases hVp.mem_or_mem h0 with hC | hM
  · apply hP0
    have : P.coeff 0 ∈ V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hC
    rw [show V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from hH] at this
    exact (Ideal.mem_bot).mp this
  · exact hMV (hVp.mem_of_pow_mem _ hM)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def CentredPlacesFinite.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    IsFractionRing O L → ∀ (m : Ideal O) [m.IsMaximal],
      {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}.Finite

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def LocalLengthPlaces.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    IsFractionRing O L → ∀ (m : Ideal O) [m.IsMaximal] (f : O), f ≠ 0 →
      (localQuotLength m f : ℝ) * Real.log (Nat.card (O ⧸ m)) =
        ∑ᶠ w ∈ {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}, -Real.log (w (f : L))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def LocalQuotCard.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    IsFractionRing O L → ∀ (m : Ideal O) [m.IsMaximal] (f : O), f ≠ 0 →
      Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) =
        Nat.card (O ⧸ m) ^ localQuotLength m f

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitCenterChart.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        ∀ v : FinitePlace (coordField x),
          orbitCenter x v = V ↔ AbsCentredAt (chartRing x c) (chartPoint x c V)
            fun t ↦ v (IntermediateField.inclusion (ratioField_le_coordField x) t)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartMax.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        (chartPoint x c V).IsMaximal

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartMult.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        ∀ [(chartPoint x c V).IsPrime],
          Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V =
            localQuotLength (chartPoint x c V) (chartEval x c s)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartQuot.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)), (∀ k, x k (c k) ≠ 0) →
    ∀ V : Ideal (MvPolynomial (Coord n) ℤ), orbitIdeal x ≤ V →
      Nonempty ((chartRing x c ⧸ chartPoint x c V) ≃+*
        (MvPolynomial (Coord n) ℤ ⧸
          (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1))))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartResidue.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        (Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V) =
          Real.log (Nat.card (chartRing x c ⧸ chartPoint x c V))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartRing.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)), (∀ k, x k (c k) ≠ 0) →
      Algebra.FiniteType ℤ (chartRing x c) ∧ IsFractionRing (chartRing x c) (ratioField x)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartTerm.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    Geo.IsSectionOn (orbitIdeal x) A.toGeo s → ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, x k (c k) ≠ 0) →
        chartEval x c s ≠ 0 ∧ ∀ v : FinitePlace (coordField x),
          (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ orbitCenter x v) →
            finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) =
              -Real.log (v (IntermediateField.inclusion (ratioField_le_coordField x)
                (chartEval x c s)))

end GroundTheory.Heights₂.Heights
end
