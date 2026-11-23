module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle188
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
public import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle678
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open scoped TensorProduct

theorem GlobalTheory.PDivGroup.exists_coords_of_isConn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n) (ev : ∀ n, MvPowerSeries (Fin d) O →ₐ[O] G.A n), (∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N) ∧ (∀ n, IsEval p (x n) (ev n)) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n, Function.Surjective (ev n)) ∧ ∀ m N : ℕ, ∃ n, ∀ f, ev n f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, hcou, hres, hspan, hl⟩ := GlobalTheory.T.exists_compatible_pDivGroup_level_coordinates p C v O hv G
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (Fact.out : ¬IsUnit (p : O))
  have hmem : ∀ n i, ¬IsUnit (x n i) := by
    intro n i hu
    have h1 := hu.map (Bialgebra.counitAlgHom O (G.A n))
    rw [Bialgebra.counitAlgHom_apply, hcou n i] at h1
    exact not_isUnit_zero h1
  have hnil : ∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N := fun n i => by
    haveI := hG n
    exact GlobalTheory.T.maximalIdeal_pow_natCast_dvd_finite_integers_algebra p hp0 C v O hv (G.A n) (x n i) ((IsLocalRing.mem_maximalIdeal _).2 (hmem n i))
  have hex : ∀ n, ∃ E : MvPowerSeries (Fin d) O →ₐ[O] G.A n, IsEval p (x n) E := fun n => by
    haveI := GlobalTheory.T.isAdicComplete_span_natCast_finite_projective_algebra p O (G.A n)
    exact ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O (G.A n) (Fin d) (x n) (hnil n)).1).exists
  choose ev hev using hex
  have hpoly : ∀ n (P : MvPolynomial (Fin d) O),
      ev n (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (x n) P := by
    intro n P
    have h : (ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (x n) :=
      MvPolynomial.algHom_ext fun i => by
        simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, (hev n).1 i]
    exact DFunLike.congr_fun h P
  refine ⟨d, x, ev, hnil, hev, hres, hcou, fun n => ?_, fun m N => ?_⟩
  · haveI := hG n
    intro a
    obtain ⟨P, hP⟩ := GlobalTheory.T.aeval_surjective_of_cotangent_span_top O (G.A n) (p : O) hpm (Bialgebra.counitAlgHom O (G.A n)) d (x n)
      (fun i => by rw [Bialgebra.counitAlgHom_apply]; exact hcou n i)
      (fun i => by simpa [map_natCast] using hnil n i) (hspan n) a
    exact ⟨P, (hpoly n P).trans hP⟩
  · obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.coeff_annihilated_of_aeval_mem_ker_pow d N
    obtain ⟨e, u, hu, hKu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0.ne' p (Fact.out : p.Prime).ne_one
    refine ⟨m + e, fun f hf α hα => ?_⟩
    obtain ⟨P, hPdeg, hPco, hPmem⟩ := GlobalTheory.T.exists_truncation_congr_of_padicContinuousEval_eq_zero p O (G.A (m + e)) d (x (m + e)) (ev (m + e)) (hev _) (m + e) N f hf
    obtain ⟨l, hlx⟩ := hl (m + e)
    let I : Ideal O := Ideal.span {(p : O) ^ (m + e)}
    let l' : Fin d → (G.A (m + e) →ₗ[O] O ⧸ I) :=
      fun i => l i ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (G.A (m + e)))
    obtain ⟨D, hD⟩ := GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra O (G.A (m + e)) I d l' (fun i a b => by
      simp only [l', LinearMap.comp_apply, AugCot.d_mul, map_add (f := _), map_smul, Bialgebra.counitAlgHom_apply])
    let φ : G.A (m + e) →ₐ[O] (O ⧸ I) ⊗[O] G.A (m + e) := Algebra.TensorProduct.includeRight
    have hy0 : ∀ j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (φ (x (m + e) j)) = 0 := by
      intro j
      simp [φ, Algebra.TensorProduct.includeRight_apply, TensorProduct.counit_tmul, hcou]
    have hDy : ∀ i j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (D i (φ (x (m + e) j))) =
        if i = j then 1 else 0 := fun i j => (hD i _).trans (hlx i j)
    have hdeg : ∀ β : Fin d →₀ ℕ, N ≤ β.degree →
        AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap O (O ⧸ I)) P) β = 0 := fun β hβ => by
      rw [MvPolynomial.coeff_map, hPdeg β hβ, map_zero]
    have hmemB : MvPolynomial.aeval (fun j => φ (x (m + e) j)) (MvPolynomial.map (algebraMap O (O ⧸ I)) P) ∈
        RingHom.ker (Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e))) ^ N := by
      rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval, AlgHom.comp_apply]
      refine (Ideal.map_le_iff_le_comap.1 ?_) hPmem
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span]
      refine sup_le (Ideal.pow_right_mono ?_ N) ?_
      · rw [Ideal.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        exact hy0 j
      · rw [Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
        have h0 : φ ((p : G.A (m + e)) ^ (m + e)) = 0 := by
          rw [map_pow, map_natCast]
          have h1 : ((p : (O ⧸ I) ⊗[O] G.A (m + e))) ^ (m + e) =
              algebraMap (O ⧸ I) _ (Ideal.Quotient.mk I ((p : O) ^ (m + e))) := by
            rw [map_pow, map_pow, map_natCast, map_natCast]
          rw [h1, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
        rw [SetLike.mem_coe, h0]
        exact zero_mem _
    have key := hK (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) _ _ D hy0 hDy _ hdeg hmemB α
    rw [MvPolynomial.coeff_map, ← map_natCast (algebraMap O (O ⧸ I)), ← map_mul,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at key
    rw [← hPco α hα]
    have hpO : (p : O) ≠ 0 := by
      intro h
      have h2 := congrArg (algebraMap O C) h
      rw [map_natCast, map_zero] at h2
      exact hp0 (by exact_mod_cast h2)
    have hunit : IsUnit (u : O) := by
      by_contra hnu
      have hcop : IsCoprime (u : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2
        ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hu)))
      obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom O)
      have h3 : a * Int.castRingHom O u + b * Int.castRingHom O p ∈ IsLocalRing.maximalIdeal O := by
        refine add_mem (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
        · simpa using (IsLocalRing.mem_maximalIdeal _).2 hnu
        · simpa using hpm
      rw [hab] at h3
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
    rw [hKu, Nat.cast_mul, Nat.cast_pow, pow_add, mul_assoc, mul_comm ((p : O) ^ m)] at key
    have key2 := (mul_dvd_mul_iff_left (pow_ne_zero e hpO)).1 key
    exact (hunit.dvd_mul_left).1 key2
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isMapOf_existsUnique_and : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ f : G ⟶ H, (∃! φ, c.IsMapOf c' f φ) ∧ ∀ (φ : Fin e → MvPowerSeries (Fin d) k), c.IsMapOf c' f φ → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n, (∀ g, c.ev n (subst φ g) = f.app n (c'.ev n g)) ∧ ∀ s, c.ev₂ n (pull2 φ s) = pullbackTwo (f.app n) (c'.ev₂ n s) := by
  intro p k _ d e G H c c' f
  have hone := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.2
  have hcomp : ∀ j n, G.res n (f.app (n + 1) (c'.x (n + 1) j)) = f.app n (c'.x n j) := fun j n => by
    rw [res_app, c'.res]
  refine ⟨?_, ?_⟩
  · choose φ hφ _ using fun j => hone (fun n => f.app n (c'.x n j)) (hcomp j)
    refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => ?_⟩
    obtain ⟨g, -, hg⟩ := hone (fun n => f.app n (c'.x n j)) (hcomp j)
    exact (hg (ψ j) fun n => hψ n j).trans (hg (φ j) fun n => hφ j n).symm
  intro φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d (G.A 0) (c.x 0) (c.nil 0) (c.aug 0) (φ j)).1
    change Coalgebra.counit (R := k) (c.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, CoalgHomClass.counit_comp_apply, c'.aug]
  refine ⟨hconst, fun n => ⟨fun g => ?_, fun s => ?_⟩⟩
  · have hy : ∀ j, IsNilpotent (f.app n (c'.x n j)) := fun j => (c'.nil n j).map (f.app n)
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (G.A n)).1 (Fin d) (c.ev n)
      (fun t => by
        change IsNilpotent (evA k (c.x n) (c.nil n) (X t))
        rw [evA_X]; exact c.nil n t) φ hconst _ hy (fun j => hφ n j) g
    rw [h1]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (H.A n)).2 (G.A n) (f.app n : H.A n →ₐ[k] G.A n) (c'.x n)
      (c'.nil n) _ hy (fun _ => rfl) g).symm
  · let F : H.A n ⊗[k] H.A n →ₐ[k] G.A n ⊗[k] G.A n :=
      Algebra.TensorProduct.map (f.app n : H.A n →ₐ[k] G.A n) (f.app n : H.A n →ₐ[k] G.A n)
    have hy : ∀ i, IsNilpotent (F (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map F
    have hev := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n
    have ha : ∀ i, constantCoeff ((Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) :
        Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k) i) = 0 := by
      intro i
      have hc := hev.2.2.2
      cases i with
      | inl j =>
        rw [Sum.elim_inl, ← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
      | inr j =>
        rw [Sum.elim_inr, ← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n)
      (fun t => by
        change IsNilpotent (evA k (c.x₂ n) (c.nil₂ n) (X t))
        rw [evA_X]; exact c.nil₂ n t) _ ha _ hy
      (fun i => by
        cases i with
        | inl j =>
          simp only [Sum.elim_inl]
          rw [hev.1, hφ n j]
          show _ = F (c'.x n j ⊗ₜ 1)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
        | inr j =>
          simp only [Sum.elim_inr]
          rw [hev.2.1, hφ n j]
          show _ = F (1 ⊗ₜ c'.x n j)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl) s
    have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n ⊗[k] G.A n) F
      (c'.x₂ n) (c'.nil₂ n) _ hy (fun _ => rfl) s
    have h3 : pullbackTwo (f.app n) (c'.ev₂ n s) = F (c'.ev₂ n s) := by
      induction (c'.ev₂ n s) with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b => rfl
    unfold pull2 at2
    rw [h1, h3]
    exact h2.symm

end GlobalTheory.Katz
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.LawCoord

theorem evA_X {k : Type} [CommRing k] {σ : Type} [Finite σ] {A : Type} [CommRing A] [Algebra k A]
    (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ) : evA k x hx (X i) = x i := by
  have ha : HasSubst (fun i => (C (x i) : MvPowerSeries Empty A)) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  change constantCoeff (substAlgHom (R := k) ha (X i : MvPowerSeries σ k)) = x i
  rw [substAlgHom_apply, subst_X ha]
  simp

theorem main : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d),
    (∃ μ, c.IsLawOf μ) ∧ ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
      (∀ i, constantCoeff (μ i) = 0) ∧ ∀ n f, c.ev₂ n (subst μ f) = Coalgebra.comul (R := k) (c.ev n f) ∧
        c.ev₂ n (cob1 μ f) = cobOne k (G.A n) (c.ev n f) := by
  intro p k _ d G c
  refine ⟨?_, fun μ hμ => ?_⟩
  · have h := fun i => ((GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => Coalgebra.comul (R := k) (c.x n i))
      (fun n => by rw [pullTwo_comul]; exact congrArg _ (c.res n i))).exists
    choose μ hμ using h
    exact ⟨μ, fun n i => hμ i n⟩
  have hconst : ∀ i, constantCoeff (μ i) = 0 := by
    intro i
    have h := (GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c 0).2.2.2 (μ i)
    rw [← h, hμ 0 i]
    have key : ∀ t : G.A 0 ⊗[k] G.A 0, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A 0))
        (Bialgebra.counitAlgHom k (G.A 0)) (fun _ _ => Commute.all _ _) t =
        Coalgebra.counit (R := k) (TensorProduct.lid k (G.A 0)
          (LinearMap.rTensor (G.A 0) (Coalgebra.counit (R := k) (A := G.A 0)) t)) := by
      intro t
      induction t with
      | tmul a b => simp [Algebra.TensorProduct.lift_tmul, Bialgebra.counitAlgHom_apply]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [key, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]
    exact c.aug 0 i
  refine ⟨hconst, fun n f => ?_⟩
  have hs : c.ev₂ n (subst μ f) = Coalgebra.comul (R := k) (c.ev n f) := by
    have hy : ∀ i, IsNilpotent (Coalgebra.comul (R := k) (c.x n i)) := fun i =>
      (c.nil n i).map (Bialgebra.comulAlgHom k (G.A n))
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n)
      (fun t => by rw [Chart.ev₂, evA_X]; exact c.nil₂ n t) μ hconst _ hy (fun i => hμ n i) f
    have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      (Bialgebra.comulAlgHom k (G.A n)) (c.x n) (c.nil n) _ hy (fun i => rfl) f
    rw [h1, ← h2]
    rfl
  refine ⟨hs, ?_⟩
  have he := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n
  rw [cob1, map_sub, map_sub, hs, he.1, he.2.1, cobOne_apply]

end GlobalTheory.LawCoord
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.restr_injective_acyclic : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I]
    (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) ((restr φ).obj I) n) := by
  intro R S _ _ φ I _ P n hn
  obtain ⟨J, hJ, i, r, hir⟩ := GlobalTheory.T.injective_etaleSheaf_retract_of_coinduced R S φ I
  obtain ⟨C, ε, hC0, hCi, hqi, hCz⟩ := GlobalTheory.T.exists_coinducedSheaf_injectiveResolution_freeExact R S φ J (GlobalTheory.T.moduleInjective_hom_free_etaleSheaf_injective R J)
  have h1 : Subsingleton (HK R (sgl ((free R).obj P)) ((restr φ).obj ((coind φ).obj J)) n) := by
    obtain ⟨e⟩ := GlobalTheory.T.etaleHypercohomology_iso_of_injective_resolution R _ C ε hC0 hCi hqi (sgl ((free R).obj P)) n
    have := hCz P n hn
    exact e.injective.subsingleton
  have h2 : Subsingleton (HK R (sgl ((free R).obj P)) ((restr φ).obj I) n) :=
    GlobalTheory.T.subsingleton_etaleHypercohomology_of_retract R _ _ ((restr φ).map i) ((restr φ).map r)
      (by rw [← Functor.map_comp, hir]; exact (restr φ).map_id I) _ n h1
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  exact (GlobalTheory.T.quasiIso_hypercohomology_bijective R (e P).hom ((restr φ).obj I) n).1.subsingleton
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem cechAug_eqv_of_section : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Y),
    s ≫ f = 𝟙 X → Eqv R (GlobalTheory.EtC.cechAug f) F := by
  intro R _ F Y X f s hs
  have hsec : yoneda.map s ≫ yoneda.map f = 𝟙 (yoneda.obj X) := by
    rw [← yoneda.map_comp, hs, yoneda.map_id]
  have hls : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f) :=
    (GlobalTheory.T.isLocallySurjective_etale_baseChange).2.1 _ _ (yoneda.map f) (yoneda.map s) hsec
  have hq := GlobalTheory.T.quasiIso_chains_cech_of_isLocallySurjective' R (yoneda.obj Y) (yoneda.obj X) (yoneda.map f) hls
  exact ((GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.1 _ _ (GlobalTheory.EtC.cechAug f)) hq

end GlobalTheory
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory

theorem glBasis_sum_sq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)), ∀ (A : Type) [Ring A] [Algebra ℝ A] (ρ : glL E a →ₗ[ℝ] A), ∑ k, ρ (b k) * ρ (b k) = ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) := by
  intro E _ _ _ a
  classical
  let b0 : Module.Basis (Σ _ : InfinitePlace E, Fin 2) ℝ (Cinf E) := Pi.basis fun _ => Complex.basisOneI
  have hb0 : ∀ w s, b0 ⟨w, s⟩ = Pi.single w (Complex.basisOneI s) := by
    intro w s; simp [b0]
  let b1 := b0.matrix (Fin a) (Fin a)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hu : ∀ _ : Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2), IsUnit (Real.sqrt 2) :=
    fun _ => IsUnit.mk0 _ hs.ne'
  let b2 := (b1.isUnitSMul hu).map (Submodule.topEquiv (R := ℝ) (M := Matrix (Fin a) (Fin a) (Cinf E))).symm
  let e := Fintype.equivFin (Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2))
  refine ⟨_, b2.reindex e, ?_⟩
  intro A _ _ ρ
  let F : InfinitePlace E → Fin a → Fin a → A := fun w i j =>
    ρ ⟨Matrix.single i j (Pi.single w 1), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w Complex.I), Submodule.mem_top⟩ ^ 2
  let G : InfinitePlace E → A := fun w => ∑ i, ∑ j, F w i j
  have hsm : ∀ (r : ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)),
      ρ ⟨r • X, Submodule.mem_top⟩ = r • ρ ⟨X, Submodule.mem_top⟩ := by
    intro r X
    rw [← map_smul]; rfl
  have hb2 : ∀ i j w s, ρ (b2 (i, j, ⟨w, s⟩)) * ρ (b2 (i, j, ⟨w, s⟩)) =
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 := by
    intro i j w s
    have : b2 (i, j, ⟨w, s⟩) = ⟨Real.sqrt 2 • Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ := by
      apply Subtype.ext
      simp [b2, b1, Module.Basis.isUnitSMul_apply, hb0]
    rw [this, hsm, smul_mul_smul, Real.mul_self_sqrt (by norm_num), two_smul, sq]
  have hL : ∑ k, ρ (b2.reindex e k) * ρ (b2.reindex e k) = ∑ w, (G w + G w) := by
    simp only [Module.Basis.reindex_apply]
    rw [Equiv.sum_comp e.symm (fun x => ρ (b2 x) * ρ (b2 x))]
    simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fin.sum_univ_two, hb2, Complex.coe_basisOneI,
      Matrix.cons_val_zero, Matrix.cons_val_one, G, F]
    simp only [← Finset.sum_add_distrib]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
    abel
  have hτ : ∀ τ : E →+* ℂ, ∀ i j,
      ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 = F (InfinitePlace.mk τ) i j := by
    intro τ i j
    have hA1 : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
      unfold atEmb; split_ifs <;> simp
    have hAI : ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 =
        ρ ⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ ^ 2 := by
      unfold atEmb
      split_ifs with h
      · rfl
      · have h1 : (⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) (starRingEnd ℂ Complex.I)), Submodule.mem_top⟩ : glL E a) =
            -⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ := by
          apply Subtype.ext
          simp [Pi.single_neg, Matrix.single_neg]
        rw [h1, map_neg, neg_sq]
    simp only [F, hAI, hA1]
  have hR : ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
      (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) = ∑ w, (G w + G w) := by
    simp only [hτ]
    change ∑ τ : E →+* ℂ, G (InfinitePlace.mk τ) = _
    rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun τ => G (InfinitePlace.mk τ))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => G w) (fun τ hτ' => by rw [(Finset.mem_filter.1 hτ').2]),
      Finset.sum_const, InfinitePlace.card_filter_mk_eq]
    have : w.mult = 2 := by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
    rw [this, two_smul]
  rw [hL, hR]

end GlobalTheory
end

section

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem hasSum_movedPoint : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (z : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → (∀ i, 1 + z i * c ≠ 0 ∧ 0 < (τ + t * z i / (1 + z i * c)).im) → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t z hk ha hz
  have hw : (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) ∈ upperHalf F := fun i ↦ (hz i).2
  have h1 := GlobalTheory.T.hasSum_hilbertEisenstein_shiftedLattice_fourier F k 𝔞 𝔟 a₀ a x _ hk ha hw
  have h2 := GlobalTheory.T.hilbertEisensteinValue_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 x) (LinearEquiv.refl F _)
    (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) (fun i ↦ τ + t * z i / (1 + z i * c)) 1
    (fun i ↦ 1 + z i * c) hk (fun _ ↦ Iff.rfl) (fun i ↦ (hz i).1) (fun v i ↦ by
      have := (hz i).1
      simp only [coord, LinearEquiv.refl_apply, Pi.one_apply]
      field_simp
      ring)
  have h3 := h1.mul_left ((∏ i, (1 + z i * c))⁻¹ ^ k)
  rw [h2]
  convert (preTransparency := .reducible) h3 using 1
  · rfl
  · funext ξ
    have hq : qPow ξ (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) =
        Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) *
          ∏ i : Emb F, Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)) := by
      rw [← Complex.exp_sum, ← Complex.exp_add, ← GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal F ξ]
      unfold qPow
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hq, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib]
    ring
  · ring

end GlobalTheory.HilbFam
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_eq_range_mul_ker : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A]
    [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (f : C →ₐc[k] A),
    Module.finrank k A = Module.finrank k (LinearMap.range (f : C →ₐ[k] A).toLinearMap) *
      Module.finrank k (A ⧸ kerIdeal f) := by
  intro k _ A _ _ _ _ C _ _ _ _ f
  rw [GlobalTheory.PDiv.finrank_eq_ker_mul_range k A C f, mul_comm]

end GlobalTheory.Dieu
end
