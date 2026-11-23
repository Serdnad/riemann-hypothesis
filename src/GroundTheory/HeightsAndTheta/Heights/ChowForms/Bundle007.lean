module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle004
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealDim.proof (h₁ : IncidenceGeneric.Statement) (h₂ : GenericLinearTrdeg.Statement)
    (h₃ : AffineChartTrdeg.Statement) : IncIdealDim.Statement := by
  intro F _ n k d P hP hdim
  have := hP.isPrime
  obtain ⟨j, hj⟩ := hP.isRelevant
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := j.pos; omega⟩
  set K := FractionRing (MvPolynomial (Fin (n' + 1)) F ⧸ P)
  set ξ := genPt P
  have hξj : ξ j ≠ 0 := by
    simp only [ξ, genPt]
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  set c : Fin (n' + 1) → K := fun m => if m = j then (ξ j)⁻¹ else 0 with hc_def
  have hc : ∑ m, c m * ξ m = 1 := by
    simp [c, inv_mul_cancel₀ hξj]

  let τ : Fin k × Fin n' → Fin k × Fin (n' + 1) := fun im => (im.1, j.succAbove im.2)
  have hτ : Function.Injective τ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [τ, Prod.mk.injEq] at h
    exact Prod.ext h.1 (j.succAbove_right_injective h.2)
  let ψ : MvPolynomial (Fin k × Fin n') K →ₐ[F] MvPolynomial (Fin k × Fin (n' + 1)) K :=
    (rename τ).restrictScalars F
  have hψ : Function.Injective ψ := rename_injective τ hτ
  let η : Fin n' → K := fun m => -(ξ (j.succAbove m) * (ξ j)⁻¹)
  let G : Set (MvPolynomial (Fin k × Fin n') K) :=
    Set.range (fun ij => X ij) ∪ Set.range (fun i : Fin k => ∑ m, X (i, m) * C (η m))

  have hA : ∀ i m, genSubst ξ c (i, j.succAbove m) = ψ (X (i, m)) := by
    intro i m
    simp [ψ, τ, genSubst, c, Fin.succAbove_ne]
  have hB : ∀ i, genSubst ξ c (i, j) = ψ (∑ m, X (i, m) * C (η m)) := by
    intro i
    have h1 : (C (ξ j) * C (ξ j)⁻¹ : MvPolynomial (Fin k × Fin (n' + 1)) K) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hξj, map_one]
    have h2 : ψ (∑ m, X (i, m) * C (η m)) =
        -((∑ m, X (i, j.succAbove m) * C (ξ (j.succAbove m))) * C (ξ j)⁻¹) := by

      simp only [ψ, AlgHom.restrictScalars_apply, map_sum, map_mul, rename_X, rename_C, τ]
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [C_neg, C_mul]
      ring
    rw [h2]
    simp only [genSubst, c, if_pos rfl]
    rw [Fin.sum_univ_succAbove _ j]
    linear_combination (-(X (i, j) : MvPolynomial (Fin k × Fin (n' + 1)) K)) * h1
  have hrange : Set.range (genSubst ξ c) = ψ '' G := by
    ext p
    constructor
    · rintro ⟨⟨i, m⟩, rfl⟩
      by_cases hm : m = j
      · rw [hm]
        exact ⟨_, Or.inr ⟨i, rfl⟩, (hB i).symm⟩
      · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
        exact ⟨_, Or.inl ⟨(i, m'), rfl⟩, (hA i m').symm⟩
    · rintro ⟨q, (⟨⟨i, m⟩, rfl⟩ | ⟨i, rfl⟩), rfl⟩
      · exact ⟨(i, j.succAbove m), hA i m⟩
      · exact ⟨(i, j), hB i⟩

  have hη : Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = ((d : ℕ) : Cardinal) := by
    have heq : Algebra.adjoin F (Set.range η) =
        Algebra.adjoin F (Set.range fun m => ξ m * (ξ j)⁻¹) := by
      apply le_antisymm
      · rw [Algebra.adjoin_le_iff]
        rintro _ ⟨m, rfl⟩
        exact neg_mem (Algebra.subset_adjoin ⟨j.succAbove m, rfl⟩)
      · rw [Algebra.adjoin_le_iff]
        rintro _ ⟨m, rfl⟩
        by_cases hm : m = j
        · beta_reduce
          rw [hm, mul_inv_cancel₀ hξj]
          exact one_mem _
        · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
          have : ξ (j.succAbove m') * (ξ j)⁻¹ = -η m' := (neg_neg _).symm
          beta_reduce
          rw [this]
          exact neg_mem (Algebra.subset_adjoin ⟨m', rfl⟩)
    rw [heq]
    exact h₃ F (n' + 1) d P j hP hdim hj

  let φ : MvPolynomial (Fin k × Fin (n' + 1)) F →ₐ[F] MvPolynomial (Fin k × Fin (n' + 1)) K :=
    aeval (genSubst ξ c)
  have hker : incIdeal P k = RingHom.ker φ := by
    ext g
    rw [h₁ F (n' + 1) k P c hc g, RingHom.mem_ker]
  have hφrange : φ.range = (Algebra.adjoin F G).map ψ := by
    show (aeval (genSubst ξ c)).range = _
    rw [aeval_range, hrange, Algebra.adjoin_image]
  haveI : Algebra.FiniteType F φ.range :=
    Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have htr : Algebra.trdeg F φ.range = ((k * n' + min k d : ℕ) : Cardinal) := by
    rw [hφrange, ← AlgEquiv.trdeg_eq (A := ↥(Algebra.adjoin F G))
      (Subalgebra.equivMapOfInjective (Algebra.adjoin F G) ψ hψ)]
    exact h₂ F K n' k d η hη
  rw [hker, ringKrullDim_eq_of_ringEquiv (AlgEquiv.toRingEquiv (Ideal.quotientKerEquivRange φ)),
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := ↥φ.range), htr]
  have hnum : k * (n' + 1) - k + min k d = k * n' + min k d := by
    rw [Nat.mul_succ, Nat.add_sub_cancel]
  rw [hnum]
  simp

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IsChowForm.incIdeal_eq_span {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm P k f) : incIdeal P k = Ideal.span {f} := by
  ext g
  rw [Ideal.mem_span_singleton, ← hf.2 g]
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem constantCoeff_eq_zero_of_isHomogIdeal {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsHomogIdeal P) (htop : P ≠ ⊤)
    {g : MvPolynomial (Fin n) F} (hg : g ∈ P) : constantCoeff g = 0 := by
  by_contra h
  have h0 := hP g hg 0
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h0
  exact htop (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

theorem IsProjPrime.not_isField_quotient {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) :
    ¬ IsField (MvPolynomial (Fin n) F ⧸ P) := by
  intro hfield
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hx : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq] at hy
  have := constantCoeff_eq_zero_of_isHomogIdeal hP.isHomog hP.isPrime.ne_top hy
  simp at this

theorem ConeDimOfChowForm.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement) :
    ConeDimOfChowForm.Statement := by
  intro F _ n k P f hP hf
  have hspan := hf.incIdeal_eq_span
  have hprime : (Ideal.span {f}).IsPrime := hspan ▸ h₂ F n k P hP.isPrime hP.isRelevant
  have hnu : ¬ IsUnit f := fun hu => hprime.ne_top (Ideal.span_singleton_eq_top.mpr hu)
  have hht : (Ideal.span {f}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf.1) hnu
  have hdimS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) (Ideal.span {f})
  rw [hht, hdimS] at hform
  have := hP.isPrime
  obtain ⟨m, hm, -⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MvPolynomial (Fin n) F ⧸ P)
  cases m with
  | zero =>
    exfalso
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) F ⧸ P) := Ring.krullDimLE_iff.mpr (by rw [hm])
    exact hP.not_isField_quotient Ring.KrullDimLE.isField_of_isDomain
  | succ d =>
    have h := h₁ F n k d P hP hm
    rw [hspan] at h
    rw [h] at hform
    have h3 : ((1 + (k * n - k + min k d) : ℕ) : WithBot ℕ∞) = ((k * n : ℕ) : WithBot ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one]
      convert hform using 2
    replace h3 := Nat.cast_injective h3
    rw [hm]
    congr 1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      omega
    · have hkn := Nat.le_mul_of_pos_right k hn
      generalize k * n = N at h3 hkn
      omega

end GroundTheory.Heights₂.Heights
end
