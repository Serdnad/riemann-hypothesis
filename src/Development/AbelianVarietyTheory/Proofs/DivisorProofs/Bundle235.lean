module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle133
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle141
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
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
public import Mathlib.Dynamics.Newton
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_eigen_projections_tensor_of_comaximal : ∀ (R F : Type) [CommRing R] [CommRing F] (a : ℕ) (t : Fin a → (F →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∃ e : Fin a → R ⊗[ℤ] F, ∀ (M : Type) [AddCommGroup M] (Θ : R ⊗[ℤ] F →+* AddMonoid.End M) (i l : Fin a) (m : M), (∀ c : F, Θ (1 ⊗ₜ c) m = Θ (t l c ⊗ₜ 1) m) → Θ (e i) m = if i = l then m else 0 := by
  first | (exact @GlobalTheory.eigenProjections_of_comaximal) | (exact GlobalTheory.eigenProjections_of_comaximal) | (intros; apply GlobalTheory.eigenProjections_of_comaximal  <;> assumption)
end

section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.annihilator_lift_of_mul_eq_p_alt : ∀ (p : ℕ) (O : Type) [CommRing O] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), (p : k) = 0 → (p : Λ) ^ 2 = 0 → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], (∀ m : M, (p : Λ) • m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ ϖ z : O, ϖ * z - (p : O) ∈ Ideal.span {(p : O) ^ 2} → ∀ n : N, ((1 : k) ⊗ₜ[ℤ] ϖ) • n = 0 → n ∈ Ideal.span {a : k ⊗[ℤ] O | ((1 : k) ⊗ₜ[ℤ] ϖ) * a = 0} • (⊤ : Submodule (k ⊗[ℤ] O) N) := by
  first | (exact @GlobalTheory.annihilator_lift_of_mul_eq_p) | (exact GlobalTheory.annihilator_lift_of_mul_eq_p) | (intros; apply GlobalTheory.annihilator_lift_of_mul_eq_p  <;> assumption)
end

section

open IsLocalRing


theorem _root_.GlobalTheory.T.localization_integralClosure_artinian_reduced_domain : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [IsArtinianRing A] [IsReduced A]
    (Q : Ideal (integralClosure R A)) [Q.IsPrime],
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed | exact GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed | (intros; apply GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧ (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  first | exact @GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span | exact GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span | (intros; apply GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | exact GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | (intros; apply GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_isIdempotentElem_tmul_one_eq_of_smooth :
    ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A],
      Algebra.Smooth R A → ∀ ε : A ⊗[R] FractionRing R, IsIdempotentElem ε →
        ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  first
  | exact @_root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq
  | exact _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq
  | (apply _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq ..)

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv {D C : Type*} [CommRing D]
    [CommRing C] (e : D ≃+* C)
    (h : ∀ (q : Ideal D) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (q : Ideal C) [hq : q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let q' : Ideal D := q.comap (e : D →+* C)
  haveI : q'.IsPrime := Ideal.comap_isPrime _ _
  have H : q'.primeCompl.map e.toMonoidHom = q.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe, q', Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by simpa using hx, by simp⟩
  let f : Localization.AtPrime q' ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q') (Localization.AtPrime q) e H
  obtain ⟨h1, h2⟩ := h q'
  exact ⟨f.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv f⟩

end GlobalTheory

namespace GlobalTheory


open Algebra.TensorProduct in
theorem exists_finset_mem_range_map_val {F A K : Type*} [Field F] [CommRing A] [Algebra F A]
    [Field K] [Algebra F K] (x : A ⊗[F] K) :
    ∃ T : Finset K, ∀ R : Subalgebra F K, (↑T : Set K) ⊆ (R : Set K) →
      x ∈ (Algebra.TensorProduct.map (AlgHom.id F A) R.val).range := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun R _ ↦ Subalgebra.zero_mem _⟩
  | tmul a k =>
    refine ⟨{k}, fun R hR ↦ ⟨a ⊗ₜ ⟨k, hR (by simp)⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨T₁, h₁⟩ := hx
    obtain ⟨T₂, h₂⟩ := hy
    refine ⟨T₁ ∪ T₂, fun R hR ↦ Subalgebra.add_mem _ (h₁ R ?_) (h₂ R ?_)⟩
    · exact fun z hz ↦ hR (by simp [hz])
    · exact fun z hz ↦ hR (by simp [hz])

theorem isDomain_and_isIntegrallyClosed_atPrime_tensor_field
    (hL1 : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K),
      ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R)
    (hL2 : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime],
      (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
        ∀ (q : Ideal C) [q.IsPrime],
          IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) →
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) :
    ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A],
      (∀ (P : Ideal A) [P.IsPrime],
        IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime],
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro F K A _ _ _ _ _ _ hA Q _
  classical
  refine hL2 (TensorProduct F A K) Q fun s ↦ ?_
  choose T hT using fun x : A ⊗[F] K ↦ exists_finset_mem_range_map_val (F := F) x
  obtain ⟨R, hR, hsm⟩ := hL1 F K (s.biUnion T)
  let φ : A ⊗[F] R →ₐ[F] A ⊗[F] K := Algebra.TensorProduct.map (AlgHom.id F A) R.val
  have hφ : ⇑φ = ⇑(LinearMap.lTensor A (R.val.toLinearMap)) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a k => simp [φ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hinj : Function.Injective φ := by
    rw [hφ]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  refine ⟨φ.range.toSubring, fun x hx ↦ hT x R (fun z hz ↦ hR ?_), ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨x, hx, hz⟩
  · let e : A ⊗[F] R ≃+* φ.range.toSubring := (AlgEquiv.ofInjective φ hinj).toRingEquiv
    exact isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv e fun q _ ↦
      isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_forall A hA q _

end GlobalTheory
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure : ∀ {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] {ι : Type} (z : ι → K), (∀ i, z i ∈ F) → ∀ (v : K), IsIntegral (Subring.closure (Set.range z)) v → ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧ f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by
  first | exact @GlobalTheory.trace_monic_over_mvPolynomial | exact GlobalTheory.trace_monic_over_mvPolynomial | (intros; apply GlobalTheory.trace_monic_over_mvPolynomial <;> assumption)
end

section

open scoped TensorProduct Polynomial

theorem _root_.GlobalTheory.T.extend_linear_independent_differentials : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.FiniteType R B] (d : ℕ) (ι : Type) (x : ι → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (x i)) → ∃ (t : Fin d → B) (e : ι ↪ Fin d), (∀ i, t (e i) = x i) ∧ LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) := by
  first | exact @GlobalTheory.kaehler_baseChange_independent_extend | exact GlobalTheory.kaehler_baseChange_independent_extend | (intros; apply GlobalTheory.kaehler_baseChange_independent_extend <;> assumption)
end

section

namespace GlobalTheory

theorem pow_idempotent_combination {R : Type} [CommRing R] {g : R} (hg : IsIdempotentElem g)
    (a b : R) (n : ℕ) : (g * a + (1 - g) * b) ^ n = g * a ^ n + (1 - g) * b ^ n := by
  induction n with
  | zero => ring
  | succ n ih =>
    rw [pow_succ, ih]
    linear_combination (a ^ n * a + b ^ n * b - a ^ n * b - b ^ n * a) * hg.eq

theorem exists_unit_pow_eq_of_krullDimLE_zero : ∀ (R : Type) [CommRing R] [Ring.KrullDimLE 0 R]
    (q : ℕ), 0 < q → IsUnit (q : R) → ∀ u : Rˣ,
    (∀ m : Ideal R, m.IsMaximal → ∃ x : R, x ^ q - (u : R) ∈ m) → ∃ v : Rˣ, v ^ q = u := by
  intro R _ _ q hq hqu u hloc
  have hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal := fun P hP => hP.isMaximal'
  let S : Set R := {g | IsIdempotentElem g ∧ ∃ x : R, IsNilpotent (g * (x ^ q - u))}
  have hjoin : ∀ g ∈ S, ∀ h ∈ S, g + h - g * h ∈ S := by
    rintro g ⟨hg, x, hx⟩ h ⟨hh, z, hz⟩
    refine ⟨?_, g * x + (1 - g) * z, ?_⟩
    · show (g + h - g * h) * (g + h - g * h) = g + h - g * h
      linear_combination (1 - 2 * h + h ^ 2) * hg.eq + (1 - g) * hh.eq
    · have key : (g + h - g * h) * ((g * x + (1 - g) * z) ^ q - u)
          = g * (x ^ q - u) + (1 - g) * (h * (z ^ q - u)) := by
        rw [pow_idempotent_combination hg]
        linear_combination (x ^ q - z ^ q - h * x ^ q + h * z ^ q) * hg.eq
      rw [key]
      exact Commute.isNilpotent_add (Commute.all _ _) hx ((Commute.all _ _).isNilpotent_mul_left (show IsNilpotent (h * (z ^ q - u)) from hz))
  have hcover : ∀ m : Ideal R, m.IsMaximal → ∃ g ∈ S, g ∉ m := by
    intro m hm
    obtain ⟨x, hx⟩ := hloc m hm
    obtain ⟨e, b, he, hab, hep⟩ := exists_isIdempotentElem_mul_of_forall_isMaximal hR (x ^ q - u)
    refine ⟨1 - e, ⟨he.one_sub, x, ?_⟩, ?_⟩
    · rw [nilpotent_iff_mem_prime]
      intro p hp
      by_cases ha : x ^ q - (u : R) ∈ p
      · exact p.mul_mem_left _ ha
      · have hep' := hep p hp ha
        have h0 : e * (1 - e) ∈ p := by
          have : e * (1 - e) = 0 := by linear_combination -he.eq
          rw [this]; exact p.zero_mem
        rcases hp.mem_or_mem h0 with h | h
        · exact absurd h hep'
        · exact p.mul_mem_right _ h
    · intro h
      have hem : e ∈ m := hab ▸ m.mul_mem_right b hx
      apply hm.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using m.add_mem h hem
  have hspan : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgS, hgm⟩ := hcover m hm
    exact hgm (hle (Ideal.subset_span hgS))
  have hfin : ∀ T : Finset R, (↑T ⊆ S) → ∃ G ∈ S, ∀ g ∈ T, g * G = g := by
    classical
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, ⟨IsIdempotentElem.zero, 0, by simp⟩, by simp⟩
    | insert a T ha ih =>
      intro hT
      have haS : a ∈ S := hT (by simp)
      obtain ⟨G, hG, hGT⟩ := ih (fun y hy => hT (by simp [hy]))
      refine ⟨a + G - a * G, hjoin a haS G hG, ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · linear_combination (1 - G) * haS.1.eq
      · have := hGT g hg
        linear_combination (1 - a) * this
  have h1 : (1 : R) ∈ Ideal.span S := by rw [hspan]; trivial
  obtain ⟨n, f, g, hf⟩ := Submodule.mem_span_set'.mp h1
  classical
  obtain ⟨G, hG, hGT⟩ := hfin (Finset.univ.image fun i => (g i : R)) (by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact (g i).2)
  have hG1 : G = 1 := by
    have : (∑ i, f i • (g i : R)) * G = ∑ i, f i • (g i : R) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, hGT _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    rw [hf, one_mul] at this
    exact this
  obtain ⟨x, hx⟩ := hG.2
  rw [hG1, one_mul] at hx
  have hxq : IsUnit (x ^ q) := by
    have := hx.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)
    simpa using this
  have hxu : IsUnit x := (isUnit_pow_iff hq.ne').mp hxq
  let P : Polynomial R := Polynomial.X ^ q - Polynomial.C (u : R)
  have hP : ∀ y : R, Polynomial.aeval y P = y ^ q - u := by
    intro y; simp [P]
  have hdP : Polynomial.aeval x (Polynomial.derivative P) = (q : R) * x ^ (q - 1) := by
    simp [P, Polynomial.derivative_X_pow]
  obtain ⟨v, ⟨-, hv⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (P := P) (x := x)
    (by rw [hP]; exact hx) (by rw [hdP]; exact hqu.mul (hxu.pow _))
  rw [hP, sub_eq_zero] at hv
  have hvu : IsUnit v := (isUnit_pow_iff hq.ne').mp (hv ▸ u.isUnit)
  exact ⟨hvu.unit, Units.ext (by simp [hv])⟩

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.cokernel_torsion_of_finiteLength_mod_element : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (f : R), 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) → ∀ (A B : Type) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Finite R B] (ψ : A →ₐ[R] B), (∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c) → ∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range := by
  first | exact @GlobalTheory.cokernel_torsion_of_finiteLength_mod | exact GlobalTheory.cokernel_torsion_of_finiteLength_mod | (intros; apply GlobalTheory.cokernel_torsion_of_finiteLength_mod <;> assumption)
end

section

namespace GlobalTheory

theorem exists_prime_notMem_ringKrullDim_quotient_eq_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (h : R),
      h ≠ 0 → h ∈ IsLocalRing.maximalIdeal R →
      ∃ q : Ideal R, q.IsPrime ∧ h ∉ q ∧ ringKrullDim (R ⧸ q) = 1 := by
  intro R _ _ _ _ h h0 hhm
  obtain ⟨q, hq, -, h1⟩ := exists_mem_height_map_le_one (IsLocalRing.maximalIdeal R)
    (PrimeSpectrum.basicOpen h).isOpen ⟨⟨⊥, inferInstance⟩, by simpa using h0, bot_le⟩
  have hq' : h ∉ q.asIdeal := hq
  refine ⟨q.asIdeal, q.isPrime, hq', ?_⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hqm : q.asIdeal ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal q.isPrime.ne_top
  have hmax : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have h2 : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro e
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk q.asIdeal) hhm
    rw [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hq' this
  have h3 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  have : IsLocalRing (R ⧸ q.asIdeal) := IsLocalRing.of_surjective' _ hsurj
  have he : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal) =
      IsLocalRing.maximalIdeal (R ⧸ q.asIdeal) := IsLocalRing.eq_maximalIdeal hmax
  rw [he] at h3
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h3]
  rfl

end GlobalTheory
end
