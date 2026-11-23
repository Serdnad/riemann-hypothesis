module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.IntegerCount

theorem card_bounded_conjugates_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
    {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R}.Finite ∧
    (Set.ncard {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} : ℝ) ≤ C * R ^ Module.finrank ℚ E := by
  intro E _ _
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b : Module.Basis ι ℤ (𝓞 E) := RingOfIntegers.basis E
  let B := canonicalEmbedding.latticeBasis E

  let L : ι → (((E →+* ℂ) → ℂ) →L[ℂ] ℂ) := fun i => LinearMap.toContinuousLinearMap (B.coord i)
  let C₀ : ℝ := ∑ i, ‖L i‖
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoord : ∀ (β : 𝓞 E) (i : ι), L i (canonicalEmbedding E (β : E)) = ((b.repr β i : ℤ) : ℂ) := by
    intro β i
    have hx : canonicalEmbedding E (β : E) = ∑ j, ((b.repr β j : ℤ) : ℂ) • B j := by
      have h0 : (β : E) = ∑ j, ((b.repr β j : ℤ) : E) * ((b j : 𝓞 E) : E) := by
        conv_lhs => rw [← b.sum_repr β]

        simp [map_sum, zsmul_eq_mul]

      rw [h0, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext τ
      simp [B, b, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    change B.coord i _ = _

    rw [hx, map_sum]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have hbound : ∀ (R : ℝ), 1 ≤ R → ∀ β : 𝓞 E, (∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R) →
      ∀ i, |((b.repr β i : ℤ) : ℝ)| ≤ C₀ * R := by
    intro R hR β hβ i
    have hx : ‖canonicalEmbedding E (β : E)‖ ≤ R :=
      (pi_norm_le_iff_of_nonneg (by linarith)).2 fun τ => by simpa using hβ τ
    have h1 : ‖L i (canonicalEmbedding E (β : E))‖ ≤ ‖L i‖ * R :=
      ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    rw [hcoord, Complex.norm_intCast] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
    exact Finset.single_le_sum (f := fun i => ‖L i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hcard : Fintype.card ι = Module.finrank ℚ E := by
    rw [← RingOfIntegers.rank E]
    exact (Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 E)).symm
  refine ⟨(2 * C₀ + 1) ^ Module.finrank ℚ E, by positivity, fun R hR => ?_⟩
  set S : Set (𝓞 E) := {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} with hS
  let N : ℤ := ⌊C₀ * R⌋
  have hN0 : 0 ≤ N := Int.floor_nonneg.2 (by nlinarith)
  let box : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-N) N
  let f : 𝓞 E → (ι → ℤ) := fun β i => b.repr β i
  have hf : Function.Injective f := by
    intro x y hxy
    apply b.repr.injective
    ext i
    exact congrFun hxy i
  have hmaps : Set.MapsTo f S (box : Set (ι → ℤ)) := by
    intro β hβ
    simp only [box, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h := abs_le.1 (hbound R hR β hβ i)
    constructor
    · have h2 : -(b.repr β i) ≤ N := Int.le_floor.2 (by push_cast; linarith [h.1])
      change -N ≤ b.repr β i
      omega
    · exact Int.le_floor.2 h.2
  have hfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn box.finite_toSet
  refine ⟨hfin, ?_⟩
  have hle : S.ncard ≤ box.card := by
    have h := Set.ncard_le_ncard_of_injOn f hmaps hf.injOn box.finite_toSet
    rwa [Set.ncard_coe_finset] at h
  have hboxcard : (box.card : ℝ) = (2 * (N : ℝ) + 1) ^ Module.finrank ℚ E := by
    have h1 : ((Finset.Icc (-N) N).card : ℤ) = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega
    have h2 : ((Finset.Icc (-N) N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      exact_mod_cast h1
    simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hcard]
    push_cast
    rw [h2]
  have hNle : (N : ℝ) ≤ C₀ * R := Int.floor_le _
  calc (S.ncard : ℝ) ≤ box.card := by exact_mod_cast hle
    _ = (2 * (N : ℝ) + 1) ^ Module.finrank ℚ E := hboxcard
    _ ≤ ((2 * C₀ + 1) * R) ^ Module.finrank ℚ E := by
        have hN0' : (0 : ℝ) ≤ N := by exact_mod_cast hN0
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = (2 * C₀ + 1) ^ Module.finrank ℚ E * R ^ Module.finrank ℚ E := mul_pow _ _ _

end GlobalTheory.CompanionTheory.IntegerCount
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem summable_rpow_neg_of_polynomial_count :
    ∀ (Q : Type) (h : Q → ℝ), (∀ q, 1 ≤ h q) → ∀ (C : ℝ) (c : ℕ),
    (∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C * T ^ c) → ∀ s : ℝ, (c : ℝ) < s →
    Summable fun q => h q ^ (-s) := by
  intro Q h h1 C c hc s hs
  classical
  have hC : 0 ≤ C := by
    have h2 := (hc 1 le_rfl).2
    have h3 : (0:ℝ) ≤ (Set.ncard {q | h q ≤ 1} : ℝ) := Nat.cast_nonneg _
    simp only [one_pow, mul_one] at h2
    linarith
  set r : ℝ := (2:ℝ) ^ ((c:ℝ) - s) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable fun k : ℕ => C * 2 ^ c * r ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hg0 : ∀ k : ℕ, 0 ≤ C * 2 ^ c * r ^ k := fun k => by positivity
  set K : Q → ℕ := fun q => ⌊Real.logb 2 (h q)⌋₊ with hK
  have hlog0 : ∀ q, 0 ≤ Real.logb 2 (h q) := fun q =>
    Real.logb_nonneg (by norm_num) (h1 q)
  have hlow : ∀ q, (2:ℝ) ^ (K q : ℝ) ≤ h q := fun q => by
    have hq : (0:ℝ) < h q := lt_of_lt_of_le one_pos (h1 q)
    have : (K q : ℝ) ≤ Real.logb 2 (h q) := Nat.floor_le (hlog0 q)
    calc (2:ℝ) ^ (K q : ℝ) ≤ (2:ℝ) ^ (Real.logb 2 (h q)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = h q := Real.rpow_logb (by norm_num) (by norm_num) hq
  have hupp : ∀ q, h q ≤ (2:ℝ) ^ (K q + 1) := fun q => by
    have hq : (0:ℝ) < h q := lt_of_lt_of_le one_pos (h1 q)
    have : Real.logb 2 (h q) ≤ ((K q + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc h q = (2:ℝ) ^ (Real.logb 2 (h q)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hq).symm
      _ ≤ (2:ℝ) ^ (((K q + 1 : ℕ)) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = (2:ℝ) ^ (K q + 1) := Real.rpow_natCast _ _
  have hterm : ∀ q, h q ^ (-s) ≤ ((2:ℝ) ^ (K q : ℝ)) ^ (-s) := fun q =>
    Real.rpow_le_rpow_of_nonpos (by positivity) (hlow q) (by linarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)])
  have hfib : ∀ (u : Finset Q) (k : ℕ),
      ∑ q ∈ u with K q = k, h q ^ (-s) ≤ C * 2 ^ c * r ^ k := by
    intro u k
    have hT : (1:ℝ) ≤ (2:ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    obtain ⟨hfin, hcard⟩ := hc _ hT
    have hsub : ((u.filter fun q => K q = k : Finset Q) : Set Q) ⊆ {q | h q ≤ (2:ℝ) ^ (k + 1)} := by
      intro q hq
      have hq' : K q = k := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
      have := hupp q
      rw [hq'] at this
      exact this
    have hcard2 : ((u.filter fun q => K q = k : Finset Q).card : ℝ) ≤ C * ((2:ℝ) ^ (k + 1)) ^ c := by
      refine le_trans ?_ hcard
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    have hb : ∀ q ∈ u.filter (fun q => K q = k), h q ^ (-s) ≤ ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
      intro q hq
      have hq' : K q = k := (Finset.mem_filter.mp hq).2
      have := hterm q
      rw [hq'] at this
      exact this
    have hb0 : (0:ℝ) ≤ ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by positivity
    calc ∑ q ∈ u with K q = k, h q ^ (-s)
        ≤ ((u.filter fun q => K q = k : Finset Q).card : ℝ) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
          simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hb
      _ ≤ (C * ((2:ℝ) ^ (k + 1)) ^ c) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) :=
          mul_le_mul_of_nonneg_right hcard2 hb0
      _ = C * 2 ^ c * r ^ k := by
          have e1 : ((2:ℝ) ^ (k + 1)) ^ c = 2 ^ c * ((2:ℝ) ^ (k : ℝ)) ^ (c : ℝ) := by
            rw [Real.rpow_natCast, Real.rpow_natCast, pow_succ, mul_pow, mul_comm]
          have e2 : r ^ k = ((2:ℝ) ^ (k : ℝ)) ^ (c : ℝ) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
            rw [← Real.rpow_add (by positivity), hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num)]
            congr 1
            ring
          rw [e1, e2]
          ring
  refine summable_of_sum_le (c := ∑' k : ℕ, C * 2 ^ c * r ^ k) (fun q => Real.rpow_nonneg (by linarith [h1 q]) _) ?_
  intro u
  calc ∑ q ∈ u, h q ^ (-s)
      = ∑ k ∈ u.image K, ∑ q ∈ u with K q = k, h q ^ (-s) :=
        (Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem K hq) _).symm
    _ ≤ ∑ k ∈ u.image K, C * 2 ^ c * r ^ k := Finset.sum_le_sum fun k _ => hfib u k
    _ ≤ ∑' k : ℕ, C * 2 ^ c * r ^ k := hg.sum_le_tsum _ fun k _ => hg0 k

end GlobalTheory.CompanionTheory.GodementH
end
