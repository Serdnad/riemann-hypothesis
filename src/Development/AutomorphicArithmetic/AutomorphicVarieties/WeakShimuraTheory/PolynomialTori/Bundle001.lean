module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinPow
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
import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

private theorem pow_le_of_primes {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (I : Ideal B)
    (h : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = maximalIdeal B) : ∃ n, maximalIdeal B ^ n ≤ I := by
  have hle : maximalIdeal B ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro Q ⟨hIQ, hQ⟩
    rw [h Q hQ hIQ]
  exact Ideal.exists_pow_le_of_le_radical_of_fg hle (IsNoetherian.noetherian _)

theorem UpperTheory.V.Ws.Po.dimOne :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B], ¬ Module.Finite O B →
      ∃ (P : Ideal B) (t : B) (n : ℕ), P.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ P ∧ t ∈ maximalIdeal B ∧ t ∉ P ∧
        maximalIdeal B ^ n ≤ P ⊔ Ideal.span {t} := by
  intro O _ _ _ B _ _ _ hnf
  haveI : IsLocalHom (algebraMap O B) := IsCO.isLocalHom
  have hIm : (maximalIdeal O).map (algebraMap O B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (algebraMap O B) x hx
  have hex : ∃ Q : Ideal B, Q.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ Q ∧
      Q ≠ maximalIdeal B := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨n, hn⟩ := pow_le_of_primes _ (fun Q hQ hIQ => hcon Q hQ hIQ)
    exact hnf (UpperTheory.V.Ws.Po.finPow hIm IsCO.res_surj n hn)
  obtain ⟨P, ⟨hP, hIP, hPm⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian B B)
      {Q : Ideal B | Q.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ Q ∧ Q ≠ maximalIdeal B} hex
  have hPle : P ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal hP.ne_top
  obtain ⟨t, htm, htP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPle hPm)
  obtain ⟨n, hn⟩ := pow_le_of_primes (P ⊔ Ideal.span {t}) (by
    intro Q hQ hPQ
    by_contra hQm
    have hPQ' : P ≤ Q := le_trans le_sup_left hPQ
    have htQ : t ∈ Q := hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
    exact hmax Q ⟨hQ, hIP.trans hPQ', hQm⟩
      (lt_of_le_of_ne hPQ' (fun e => htP (by rw [e]; exact htQ))))
  exact ⟨P, t, n, hP, hIP, htm, htP, hn⟩
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.Ws.Po.psFin :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsDomain B], (∀ a ∈ maximalIdeal O, algebraMap O B a = 0) →
      ∀ t ∈ maximalIdeal B, t ≠ 0 → ∀ n : ℕ, maximalIdeal B ^ n ≤ Ideal.span {t} →
      ∃ φ : PowerSeries (ResidueField O) →+* B, Function.Injective φ ∧ φ.Finite ∧ φ PowerSeries.X = t ∧
        ∀ a : O, φ (PowerSeries.C (residue O a)) = algebraMap O B a := by
  intro O _ _ B _ _ _ _ h0 t ht ht0 n hn
  classical
  let ι : ResidueField O →+* B := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O B) h0
  letI : UniformSpace (ResidueField O) := ⊥
  letI : WithIdeal B := ⟨maximalIdeal B⟩
  have hadic : IsAdic (maximalIdeal B) := rfl
  have hc : CompleteSpace B ∧ T2Space B := hadic.isAdicComplete_iff.mp (IsCO.complete (O := O))
  haveI := hc.1
  haveI := hc.2
  have hcont : Continuous ι := continuous_of_discreteTopology
  have hte : PowerSeries.HasEval t := by
    show Filter.Tendsto (fun m => t ^ m) Filter.atTop (nhds 0)
    rw [hadic.hasBasis_nhds_zero.tendsto_right_iff]
    intro i _
    filter_upwards [Filter.eventually_ge_atTop i] with m hm
    exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow ht m)
  let φ := PowerSeries.eval₂Hom hcont hte
  have hφX : φ PowerSeries.X = t := by simp [φ, PowerSeries.coe_eval₂Hom]
  have hφC : ∀ r, φ (PowerSeries.C r) = ι r := by
    intro r
    simp [φ, PowerSeries.coe_eval₂Hom]
  refine ⟨φ, ?_, ?_, hφX, fun a => by rw [hφC]; rfl⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have hu : IsUnit (PowerSeries.divXPowOrder f) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      exact Ne.isUnit (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hne)
    have h1 := congrArg φ (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
    rw [map_mul, map_pow, hφX, hf] at h1
    exact mul_ne_zero (pow_ne_zero _ ht0) (hu.map φ).ne_zero h1
  · letI : Algebra (PowerSeries (ResidueField O)) B := φ.toAlgebra
    haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField O))) (PowerSeries (ResidueField O)) := by
      rw [PowerSeries.maximalIdeal_eq_span_X]
      infer_instance
    have hmap : Ideal.map (algebraMap (PowerSeries (ResidueField O)) B)
        (maximalIdeal (PowerSeries (ResidueField O))) = Ideal.span {t} := by
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton,
        RingHom.algebraMap_toAlgebra, hφX]
    show Module.Finite _ _
    refine UpperTheory.V.Ws.Po.finPow ?_ ?_ n ?_
    · rw [hmap, Ideal.span_le, Set.singleton_subset_iff]
      exact ht
    · intro x
      obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
      exact ⟨PowerSeries.C (residue O a), by rw [RingHom.algebraMap_toAlgebra, hφC]; exact ha⟩
    · rw [hmap]
      exact hn
end
