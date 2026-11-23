module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem aeval_cone_of_isHomogeneous {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n d : ℕ}
    (y : Fin n → Ω) {p : MvPolynomial (Fin n) F} (hp : p.IsHomogeneous d) :
    aeval (fun j => Polynomial.C (y j) * Polynomial.X) p =
      Polynomial.C (aeval y p) * Polynomial.X ^ d := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]

  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, ← map_pow,
    ← map_prod, Polynomial.algebraMap_apply, map_mul, mul_assoc]

theorem ClosedPointConeCoord.proof : ClosedPointConeCoord.Statement := by
  intro F _ n I i hI hdim hXi Ω _ _ y hy hyI
  classical
  let φ : MvPolynomial (Fin n) F →ₐ[F] Polynomial Ω :=
    aeval fun j => Polynomial.C (y j) * Polynomial.X
  let P : Ideal (MvPolynomial (Fin n) F) := RingHom.ker φ
  have hPprime : P.IsPrime := RingHom.ker_isPrime _
  have hIP : I ≤ P := by
    intro g hg
    show φ g = 0

    rw [← sum_homogeneousComponent g, map_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [show φ (homogeneousComponent d g) = _ from
      aeval_cone_of_isHomogeneous y (homogeneousComponent_isHomogeneous d g),
      hyI _ (hI.isHomog g hg d), map_zero, zero_mul]
  let m : Ideal (MvPolynomial (Fin n) F) := RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F)
  have hmprime : m.IsPrime := RingHom.ker_isPrime _
  have key : (Polynomial.evalRingHom (0 : Ω)).comp (φ : MvPolynomial (Fin n) F →+* Polynomial Ω) =
      (algebraMap F Ω).comp constantCoeff := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp [φ]
  have hPm : P ≤ m := by
    intro g hg
    have hg' : φ g = 0 := hg
    have h0 := RingHom.congr_fun key g
    simp only [RingHom.comp_apply, RingHom.coe_coe, hg', map_zero] at h0
    show constantCoeff g = 0
    exact (algebraMap F Ω).injective (by rw [← h0, map_zero])
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have hXjP : X j ∉ P := by
    intro h
    have h' : φ (X j) = 0 := h
    simp only [φ, aeval_X] at h'
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hj) Polynomial.X_ne_zero h'
  have hXjm : X j ∈ m := by
    show constantCoeff (X j : MvPolynomial (Fin n) F) = 0
    simp
  have hPlt : P < m := lt_of_le_of_ne hPm fun h => hXjP (h ▸ hXjm)
  have hIeq : I = P := by
    by_contra hne
    have hIlt : I < P := lt_of_le_of_ne hIP hne
    have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
      rw [ringKrullDim_quotient, Order.le_krullDim_iff]
      let a : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨I, hI.isPrime⟩, fun _ h => h⟩
      let b : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨P, hPprime⟩, fun _ h => hIP h⟩
      let c : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨m, hmprime⟩, fun _ h => hPm (hIP h)⟩
      have hab : a < b := hIlt
      have hbc : b < c := hPlt
      exact ⟨LTSeries.mk 2 ![a, b, c]
        (Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; exacts [hab, hbc]), rfl⟩
    rw [hdim] at h2
    norm_num at h2
  intro hyi
  apply hXi
  rw [hIeq]
  show φ (X i) = 0
  simp [φ, hyi]

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeMassOfFibre.Statement : Prop :=
  ∀ (n m δ : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsProjPrime J →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = δ) →
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
        (δ : ENNReal) * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem not_isChowForm_zero (hPt : ProjPrimeHasPoint.Statement) {F : Type} [Field F] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) F)} (hW : IsProjPrime W) (g : MvPolynomial (Fin 0 × Fin n) F) :
    ¬ IsChowForm W 0 g := by
  intro hg
  obtain ⟨x, hx, hxW⟩ := hPt F n W hW
  have hunit : g ∣ 1 := by
    rw [eq_C_of_isEmpty g] at hg ⊢
    have hc : AddMonoidAlgebra.coeff g 0 ≠ 0 := fun h => hg.1 (by rw [h, map_zero])
    exact ⟨C (AddMonoidAlgebra.coeff g 0)⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hinc : (fun _ => 0 : Fin 0 × Fin n → AlgebraicClosure F) ∈ incidence W 0 :=
    ⟨x, hx, hxW, fun i => i.elim0⟩
  have := (hg.2 1).mpr hunit _ hinc
  simp at this

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ProjPrimeHasPoint.proof : ProjPrimeHasPoint.Statement := by
  intro F _ n W hW
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.isRelevant
  by_contra hcon
  push Not at hcon
  apply hj
  have hmem : (X j : MvPolynomial (Fin n) F) ∈
      vanishingIdeal F (zeroLocus (AlgebraicClosure F) W) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · obtain ⟨q, hq, hne⟩ := hcon x hx0
      exact absurd (hx q hq) hne
  rwa [IsPrime.vanishingIdeal_zeroLocus] at hmem

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChowFormDimLe

theorem coeff_zero_eq_zero_of_mem {F : Type} [Field F] {n : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    (hI : IsProjPrime I) {g : MvPolynomial (Fin n) F} (hg : g ∈ I) : AddMonoidAlgebra.coeff g 0 = 0 := by
  by_contra h
  have h0 := hI.isHomog g hg 0
  rw [homogeneousComponent_zero] at h0
  exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

theorem exists_prime_liesOver {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : ∀ g ∈ I, AddMonoidAlgebra.coeff g 0 = 0) :
    ∃ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime ∧
      P ≤ RingHom.ker (eval (0 : Fin n → K)) ∧
      P.comap (MvPolynomial.map (algebraMap F K)) = I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : Module.Flat (MvPolynomial (Fin n) F) (MvPolynomial (Fin n) K) :=
    Module.Flat.isBaseChange F (MvPolynomial (Fin n) F) K (MvPolynomial (Fin n) K)
      (Algebra.IsPushout.out (R := F) (S := MvPolynomial (Fin n) F) (R' := K)
        (S' := MvPolynomial (Fin n) K))
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K))
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  have hle : I ≤ Q.under (MvPolynomial (Fin n) F) := by
    intro g hg
    rw [Ideal.under, Ideal.mem_comap, MvPolynomial.algebraMap_def, RingHom.mem_ker, eval_map,
      eval₂_zero_apply, constantCoeff_eq, hI g hg, map_zero]
  obtain ⟨P, hPQ, hP, hPI⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
  refine ⟨P, hP, hPQ, ?_⟩
  rw [P.over_def I]
  rfl

theorem ringKrullDim_eq_of_comap {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F))
    (P : Ideal (MvPolynomial (Fin n) K)) (hPI : P.comap (MvPolynomial.map (algebraMap F K)) = I) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : P.LiesOver I := ⟨hPI.symm⟩
  exact GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
    (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) F ⧸ I) (MvPolynomial (Fin n) K ⧸ P))

theorem exists_ne_zero_common_zero {K : Type} [Field K] [IsAlgClosed K] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] (hPQ : P ≤ RingHom.ker (eval (0 : Fin n → K)))
    (hdim : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) K ⧸ P))
    (u : Fin k × Fin n → K) :
    ∃ x : Fin n → K, x ≠ 0 ∧ (∀ g ∈ P, eval x g = 0) ∧ ∀ i, ∑ j, u (i, j) * x j = 0 := by
  classical
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K)) with hQdef
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  let mk := Ideal.Quotient.mk P
  let ℓ : Fin k → MvPolynomial (Fin n) K := fun i => ∑ j, C (u (i, j)) * X j
  have hℓQ : ∀ i, ℓ i ∈ Q := by
    intro i
    simp [Q, ℓ, RingHom.mem_ker]
  set Mb : Ideal (MvPolynomial (Fin n) K ⧸ P) := Q.map mk
  have : Mb.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hPQ)
  let s : Finset (MvPolynomial (Fin n) K ⧸ P) := Finset.univ.image (fun i => mk (ℓ i))
  have hsM : Ideal.span (s : Set (MvPolynomial (Fin n) K ⧸ P)) ≤ Mb := by
    rw [Ideal.span_le]
    intro y hy
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact Ideal.mem_map_of_mem _ (hℓQ i)
  obtain ⟨q, hqmin, hqM⟩ := Ideal.exists_minimalPrimes_le hsM
  have : q.IsPrime := hqmin.1.1
  have hqht : q.height ≤ k := by
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hqmin).trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hMht : (Mb.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K ⧸ P) := by
    have h := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := K) Mb
    have hF : IsField ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient Mb).mp inferInstance
    have h0 : ringKrullDim ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) = 0 := by
      have h00 := ringKrullDim_eq_zero_of_isField (F := (MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) hF
      convert h00 using 2
    rwa [h0, add_zero] at h
  have hqne : q ≠ Mb := by
    intro hq
    rw [hq] at hqht
    have h1 : ((Mb.height : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hqht
    rw [hMht] at h1
    exact absurd h1 (not_le.mpr (by exact_mod_cast hdim))
  set Q' := q.comap mk
  have : Q'.IsPrime := Ideal.comap_isPrime mk q
  have hQQ' : ¬ Q ≤ Q' := by
    intro h
    apply hqne
    refine le_antisymm hqM ?_
    calc Mb = Q.map mk := rfl
      _ ≤ Q'.map mk := Ideal.map_mono h
      _ = q := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q
  have hnull := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q'
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ zeroLocus K Q', x ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hQQ'
    intro g hg
    rw [← hnull, mem_vanishingIdeal_iff]
    intro x hx
    rw [hcon x hx]
    simpa [Q, RingHom.mem_ker] using hg
  refine ⟨x, hx0, fun g hg => ?_, fun i => ?_⟩
  · have hgQ' : g ∈ Q' := by
      show mk g ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]
      exact q.zero_mem
    simpa using (mem_zeroLocus_iff.mp hx) g hgQ'
  · have hmem : ℓ i ∈ Q' := by
      show mk (ℓ i) ∈ q
      exact hqmin.1.2 (Ideal.subset_span (by simp [s]))
    simpa [ℓ] using (mem_zeroLocus_iff.mp hx) _ hmem

theorem proof : ChowFormDimLe.Statement := by
  intro F _ n k I f hI hf
  by_contra hdim
  rw [not_le] at hdim
  have := hI.isPrime
  obtain ⟨P, hP, hPQ, hPI⟩ := exists_prime_liesOver (AlgebraicClosure F) I
    (fun g hg => coeff_zero_eq_zero_of_mem hI hg)
  have hdimP : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure F) ⧸ P) := by
    rw [ringKrullDim_eq_of_comap (AlgebraicClosure F) I P hPI]
    exact_mod_cast hdim
  have hall : ∀ u : Fin k × Fin n → AlgebraicClosure F, u ∈ incidence I k := by
    intro u
    obtain ⟨x, hx0, hxP, hxu⟩ := exists_ne_zero_common_zero P hPQ hdimP u
    refine ⟨x, hx0, fun g hg => ?_, hxu⟩
    have hgP : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) g ∈ P := by
      rw [← hPI] at hg
      exact hg
    have := hxP _ hgP
    rwa [eval_map, ← aeval_def] at this
  apply hf.1
  apply map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F)).injective
  apply MvPolynomial.funext
  intro u
  rw [eval_map, ← aeval_def, ((hf.2 f).mpr dvd_rfl) u (hall u), map_zero, map_zero]

end ChowFormDimLe

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField Matrix

noncomputable section

variable {n : ℕ}

theorem HermNorm.norm_pairing_le (h : HermNorm n) (u y : Fin n → ℂ) :
    ‖∑ j, u j * y j‖ ≤ h.norm u * h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hpair : ∑ j, u j * y j = ∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i := by
    have e1 : (∑ j, u j * y j) = u ⬝ᵥ y := rfl
    have e2 : (∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i) = (h.mat *ᵥ u) ⬝ᵥ ((h.matᵀ)⁻¹ *ᵥ y) := rfl
    rw [e1, e2, dotProduct_comm (h.mat *ᵥ u), dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
      mul_nonsing_inv _ hinv, one_mulVec, dotProduct_comm]
  rw [hpair]
  calc ‖∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i‖
      ≤ ∑ i, ‖(h.mat *ᵥ u) i‖ * ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ √(∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2) * √(∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = h.norm u * h.dualNorm y := rfl

theorem HermNorm.dualNorm_pos (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  unfold HermNorm.dualNorm
  apply Real.sqrt_pos.mpr
  have hBy : (h.matᵀ)⁻¹ *ᵥ y ≠ 0 := by
    intro h0
    apply hy
    have := congrArg (fun x => h.matᵀ *ᵥ x) h0
    simp only [mulVec_mulVec, mul_nonsing_inv _ hinv, one_mulVec, mulVec_zero] at this
    exact this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hBy
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by
    have : 0 < ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := norm_pos_iff.mpr hi
    positivity⟩

theorem fsLog_le (h : HermNorm n) {u y : Fin n → ℂ} (hy : ∑ j, u j * y j ≠ 0) :
    fsLog h u y ≤ Real.log (h.norm u) := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hd := h.dualNorm_pos hy0
  have hnum : 0 < ‖∑ j, u j * y j‖ := norm_pos_iff.mpr hy
  unfold fsLog
  apply Real.log_le_log (div_pos hnum hd)
  rw [div_le_iff₀ hd]
  exact h.norm_pairing_le u y

theorem measurableSet_coneBall (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    MeasurableSet (coneBall h W) := by
  have hc : Continuous (h.pointOf) := by
    unfold HermNorm.pointOf
    fun_prop
  have hclosed : IsClosed {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} := by
    have : {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} =
        ⋂ q ∈ W, {y | eval (h.pointOf y) q = 0} := by
      ext y; simp
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq ((continuous_eval q).comp hc) continuous_const
  have hopen : MeasurableSet (Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 1) :=
    Metric.isOpen_ball.measurableSet
  have := hopen.inter hclosed.measurableSet
  convert this using 1
  ext y
  simp [coneBall, Metric.mem_ball]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeMeetNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W W' : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime → W'.IsPrime →
    W ≠ W' → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W') ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0

end

end GroundTheory.Heights₂.Heights
end
