module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle022
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle023
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle024
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
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Monic
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open NumberField


theorem _root_.GlobalTheory.T.integer_coordinates_bound : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)), Function.Surjective (fun i => InfinitePlace.mk (τ i)) → ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) → ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  first | exact @GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le | exact GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le | (intros; apply GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.product_neighbourhoods_shrink_compact_open : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | exact GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | (intros; apply GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.IdemLift

theorem sub_pow_three_eq {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : (a - b) ^ 3 = a - b := by
  have ha' : a * a = a := ha
  have hb' : b * b = b := hb
  linear_combination (a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'

theorem eq_of_isNilpotent_sub {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (h : IsNilpotent (a - b)) : a = b :=
  eq_of_isNilpotent_sub_of_isIdempotentElem ha hb h

theorem eq_of_sub_mem_jacobson {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a - b ∈ Ideal.jacobson (⊥ : Ideal R)) : a = b := by
  have hu : IsUnit ((a - b) * (-(a - b)) + 1) := Ideal.mem_jacobson_bot.1 h _
  have h3 := sub_pow_three_eq ha hb
  have hz : (a - b) * ((a - b) * (-(a - b)) + 1) = 0 := by
    linear_combination -h3
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hz)

theorem existsUnique_idempotent_lift {S : Type} [CommRing S] (ϖ : S)
    [IsAdicComplete (Ideal.span {ϖ}) S] (k : ℕ) (hk : k ≠ 0)
    (e : S ⧸ Ideal.span {ϖ ^ k}) (he : IsIdempotentElem e) :
    ∃! e' : S, IsIdempotentElem e' ∧ Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) e' = e := by
  have hJI : Ideal.span {ϖ ^ k} ≤ Ideal.span {ϖ} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self ϖ hk
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
  have haJ : a * a - a ∈ Ideal.span {ϖ ^ k} := by
    apply Ideal.Quotient.eq_zero_iff_mem.1
    have he' : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) a * Ideal.Quotient.mk _ a
        = Ideal.Quotient.mk _ a := he
    rw [map_sub, map_mul, he', sub_self]
  have haI : a * a - a ∈ Ideal.span {ϖ} := hJI haJ
  have hH : HenselianRing S (Ideal.span {ϖ}) := IsAdicComplete.henselianRing S _
  have hmon : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).Monic := by
    apply Polynomial.monic_X_pow_sub
    simpa using lt_of_le_of_lt Polynomial.degree_X_le (by norm_num : (1 : WithBot ℕ) < 2)
  have heval : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a ∈ Ideal.span {ϖ} := by
    have : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a = a * a - a := by
      simp [sq]
    rwa [this]
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ})
      (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X) |>.eval a)) := by
    have hd : (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X)).eval a
        = 2 * a - 1 := by
      simp
      ring
    rw [hd]
    have hsq : Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1)
        * Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1) = 1 := by
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {ϖ}))]
      apply Ideal.Quotient.eq.2
      have : (2 * a - 1) * (2 * a - 1) - 1 = 4 * (a * a - a) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ haI
    exact IsUnit.of_mul_eq_one _ hsq
  obtain ⟨y, hy, hya⟩ := hH.is_henselian _ hmon a heval hunit
  have hyid : IsIdempotentElem y := by
    have : y ^ 2 - y = 0 := by simpa [Polynomial.IsRoot] using hy
    have h2 : y * y - y = 0 := by rw [← sq]; exact this
    exact sub_eq_zero.1 h2
  have hlift : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) y = Ideal.Quotient.mk _ a := by
    apply eq_of_isNilpotent_sub (hyid.map (Ideal.Quotient.mk _)) he
    refine ⟨k, ?_⟩
    rw [← map_sub, ← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hya
    rw [hc, mul_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨y, ⟨hyid, hlift⟩, ?_⟩
  rintro z ⟨hz, hza⟩
  apply eq_of_sub_mem_jacobson hz hyid
  apply IsAdicComplete.le_jacobson_bot (Ideal.span {ϖ})
  apply hJI
  apply Ideal.Quotient.eq.1
  rw [hza, hlift]

end GlobalTheory.CompanionTheory.IdemLift
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.norm_map_congruence : ∀ (O S : Type) [CommRing O] [CommRing S] [Algebra O S] (I : Ideal O) [IsAdicComplete I S] (Q : ℕ → Ideal S) (N₀ : ℕ) (Nm : S → S) (t : S) (P₁ : Sˣ), (∀ m, Q (m + 1) ≤ Q m) → (∀ k, Q (N₀ * k + 1) ≤ Ideal.map (algebraMap O S) (I ^ k)) → Ideal.map (algebraMap O S) I ≤ Q 1 → (∀ x ∈ Q 1, IsUnit (1 + x)) → (∀ (k : ℕ) (x y : S), x - y ∈ Ideal.map (algebraMap O S) (I ^ k) → Nm x - Nm y ∈ Ideal.map (algebraMap O S) (I ^ k)) → t - Nm (P₁ : S) ∈ Q 1 → (∀ m, 1 ≤ m → ∀ P : Sˣ, t - Nm (P : S) ∈ Q m → ∃ P' : Sˣ, (P' : S) - (P : S) ∈ Q m ∧ t - Nm (P' : S) ∈ Q (m + 1)) → ∃ L : Sˣ, Nm (L : S) = t := by
  first | exact @GlobalTheory.CompanionTheory.AdicApprox.exists_unit_eq_of_successive_approximation | exact GlobalTheory.CompanionTheory.AdicApprox.exists_unit_eq_of_successive_approximation | (intros; apply GlobalTheory.CompanionTheory.AdicApprox.exists_unit_eq_of_successive_approximation <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.finite_module_adic_complete : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [AddCommGroup M] [Module O M] [Module.Finite O M], IsAdicComplete (IsLocalRing.maximalIdeal O) M := by
  first | exact @GlobalTheory.CompanionTheory.FiniteComplete.isAdicComplete_of_finite | exact GlobalTheory.CompanionTheory.FiniteComplete.isAdicComplete_of_finite | (intros; apply GlobalTheory.CompanionTheory.FiniteComplete.isAdicComplete_of_finite <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open MvPolynomial

theorem _root_.GlobalTheory.T.derivation_commutes_with_trace : ∀ (K F L : Type) [Field K] [CharZero K] [Field F] [Field L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [FiniteDimensional F L] (D : Derivation K L L) (D0 : Derivation K F F), (∀ x : F, D (algebraMap F L x) = algebraMap F L (D0 x)) → ∀ y : L, algebraMap F L (D0 (Algebra.trace F L y)) = algebraMap F L (Algebra.trace F L (D y)) := by
  first | exact @GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation | exact GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation | (intros; apply GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation <;> assumption)
end

section


theorem _root_.GlobalTheory.T.split_quadratic_order_principal : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O] (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  first | exact @GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq | exact GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq | (intros; apply GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.semistable_generic_fibre_localization : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → ∀ (F : Type) [Field F] [Algebra O F] [IsLocalization.Away ϖ F], (IsLocalization.Away.map F (Localization.Away (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ)) (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ})) ϖ).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Semistable.smooth_generic_fibre | exact GlobalTheory.CompanionTheory.Semistable.smooth_generic_fibre | (intros; apply GlobalTheory.CompanionTheory.Semistable.smooth_generic_fibre <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.Idem

theorem glue_idempotent_property :
    ∀ {S : Type} [CommRing S] (Q : S → Prop), Q 0 →
      (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → Q e → Q (e * e')) →
      (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → Q e → Q e' →
        Q (e + e')) →
      (∀ m : Ideal S, m.IsMaximal → ∃ e, IsIdempotentElem e ∧ e ∉ m ∧ Q e) → Q 1 := by
  intro S _ Q h0 hmul hadd hloc
  let I : Ideal S :=
    { carrier := {x | ∃ e : S, IsIdempotentElem e ∧ Q e ∧ e * x = x}
      zero_mem' := ⟨0, IsIdempotentElem.zero, h0, by simp⟩
      add_mem' := by
        rintro x y ⟨e, he, hQe, hex⟩ ⟨e', he', hQe', hey⟩
        have hee : e * e = e := he
        have hee' : e' * e' = e' := he'
        have h1e : IsIdempotentElem (1 - e) := he.one_sub
        have hg : IsIdempotentElem (e' * (1 - e)) :=
          IsIdempotentElem.mul he' h1e
        have horth : e * (e' * (1 - e)) = 0 := by
          have : e * (e' * (1 - e)) = e' * (e - e * e) := by ring
          rw [this, hee]; simp
        refine ⟨e + e' * (1 - e), ?_, hadd e _ he hg horth hQe (hmul e' _ he' h1e hQe'), ?_⟩
        · show (e + e' * (1 - e)) * (e + e' * (1 - e)) = e + e' * (1 - e)
          have hg' : (e' * (1 - e)) * (e' * (1 - e)) = e' * (1 - e) := hg
          have : (e + e' * (1 - e)) * (e + e' * (1 - e))
              = e * e + 2 * (e * (e' * (1 - e))) + (e' * (1 - e)) * (e' * (1 - e)) := by ring
          rw [this, hee, horth, hg']; simp
        · have h1 : (e + e' * (1 - e)) * x = x := by
            have : (e + e' * (1 - e)) * x = e * x + e' * (x - e * x) := by ring
            rw [this, hex]; simp
          have h2 : (e + e' * (1 - e)) * y = y := by
            have : (e + e' * (1 - e)) * y = e * y + (e' * y) - e * (e' * y) := by ring
            rw [this, hey]; ring
          rw [mul_add, h1, h2]
      smul_mem' := by
        rintro c x ⟨e, he, hQe, hex⟩
        refine ⟨e, he, hQe, ?_⟩
        show e * (c * x) = c * x
        calc e * (c * x) = c * (e * x) := by ring
          _ = c * x := by rw [hex]  }
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨e, he, hem, hQ⟩ := hloc m hm
    exact hem (hIm ⟨e, he, hQ, by rw [show e * e = e from he]⟩)
  have h1 : (1 : S) ∈ I := by rw [htop]; exact Submodule.mem_top
  obtain ⟨e, _, hQ, he1⟩ := h1
  have : e = 1 := by simpa using he1
  exact this ▸ hQ

end GlobalTheory.CompanionTheory.Idem
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo


open MvPolynomial in
theorem exists_monic_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (y : Fin m → MvPolynomial σ K)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (a : MvPolynomial σ K) :
    ∃ (s : ℕ) (C : ℕ → MvPolynomial (Fin m) K), 0 < s ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (C l) * a ^ l ∈ I := by
  by_cases htop : I = ⊤
  · exact ⟨1, 0, one_pos, by simp [htop]⟩
  haveI : Nontrivial (MvPolynomial σ K ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
  set B := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)) with hB
  haveI : Algebra.IsIntegral B (MvPolynomial σ K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  obtain ⟨p, hp, hroot⟩ := Algebra.IsIntegral.isIntegral (R := B) (Ideal.Quotient.mk I a)
  have hq : (p * Polynomial.X).Monic := hp.mul Polynomial.monic_X
  have hroot' : Polynomial.eval₂ (algebraMap B (MvPolynomial σ K ⧸ I)) (Ideal.Quotient.mk I a)
      (p * Polynomial.X) = 0 := by
    rw [Polynomial.eval₂_mul, hroot, zero_mul]
  have hdeg : 0 < (p * Polynomial.X).natDegree := by
    rw [hp.natDegree_mul Polynomial.monic_X, Polynomial.natDegree_X]
    omega
  generalize p * Polynomial.X = q at hq hroot' hdeg
  have hlift : ∀ l, ∃ c : MvPolynomial (Fin m) K,
      Ideal.Quotient.mk I (aeval y c) = ((q.coeff l : B) : MvPolynomial σ K ⧸ I) := by
    intro l
    have hmem : ((q.coeff l : B) : MvPolynomial σ K ⧸ I) ∈
        (aeval (fun k => Ideal.Quotient.mk I (y k)) :
          MvPolynomial (Fin m) K →ₐ[K] MvPolynomial σ K ⧸ I).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (q.coeff l).2
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    rw [← hc]
    have := MvPolynomial.comp_aeval_apply (R := K) (B := MvPolynomial σ K ⧸ I) y
      (Ideal.Quotient.mkₐ K I) c
    simpa using this
  choose C hC using hlift
  refine ⟨q.natDegree, C, hdeg, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hroot', Polynomial.eval₂_eq_sum_range,
    Finset.sum_range_succ, map_add, map_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hC, map_pow]
    rfl
  · simp [hq.coeff_natDegree]


open MvPolynomial in
theorem homogeneousComponent_aeval_mul {K σ : Type} [Field K] {m e : ℕ} (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (C : MvPolynomial (Fin m) K) (r t : ℕ) (b : MvPolynomial σ K) (hb : b.IsHomogeneous t) :
    homogeneousComponent (e * r + t) (aeval y C * b) = aeval y (homogeneousComponent r C) * b := by
  have key : ∀ r', homogeneousComponent (e * r + t) (aeval y (homogeneousComponent r' C) * b) =
      if r' = r then aeval y (homogeneousComponent r C) * b else 0 := by
    intro r'
    have h : (aeval y (homogeneousComponent r' C) * b).IsHomogeneous (e * r' + t) :=
      ((homogeneousComponent_isHomogeneous r' C).aeval y hy).mul hb
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    by_cases hr : r' = r
    · subst hr
      simp
    · have hne : e * r' + t ≠ e * r + t := fun h' =>
        hr (Nat.eq_of_mul_eq_mul_left he (Nat.add_right_cancel h'))
      rw [if_neg hne.symm, if_neg hr]
  conv_lhs => rw [← sum_homogeneousComponent C]

  rw [map_sum, Finset.sum_mul, map_sum]
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hmem)]
    simp


open MvPolynomial in
theorem exists_hom_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ n : ℕ, homogeneousComponent n f ∈ I) (e : ℕ) (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (w : ℕ) (a : MvPolynomial σ K) (ha : a.IsHomogeneous (e * w)) :
    ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (c l) * a ^ l ∈ I := by
  obtain ⟨s, C, hs, hmem⟩ := exists_monic_relation I y hfin a
  refine ⟨s, fun l => homogeneousComponent ((s - l) * w) (C l), hs,
    fun l => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hcomp := hI _ hmem (e * w * s)

  rw [map_add (f := _), map_sum] at hcomp
  convert hcomp using 2
  · have h := ha.pow s
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    simp
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have hdeg : e * w * s = e * ((s - l) * w) + e * w * l := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [hdeg, homogeneousComponent_aeval_mul he y hy (C l) _ _ _ (ha.pow l)]

end GlobalTheory.CompanionTheory.Geo
end

section


theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_reduced_quotient_localization : ∀ (A : Type) [CommRing A] [IsDomain A] (t : A), t ≠ 0 → IsReduced (A ⧸ Ideal.span {t}) → IsIntegrallyClosed (Localization.Away t) → IsIntegrallyClosed A := by
  first | exact @GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away | exact GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away | (intros; apply GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.local_finite_algebra_jacobson_radical : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Module.Finite O R], Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ (⊥ : Ideal R).jacobson ∧ ∃ N : ℕ, (⊥ : Ideal R).jacobson ^ N ≤ Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) := by
  first | exact @GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le | exact GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le | (intros; apply GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le <;> assumption)
end
