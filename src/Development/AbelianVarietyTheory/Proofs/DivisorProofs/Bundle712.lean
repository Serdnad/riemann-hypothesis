module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.EtaleCohomology.EtaleSheaves.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle678
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Polynomial IntermediateField

namespace GlobalTheory.LadicDenom

theorem norm_natCast_padicComplex (l : ℕ) [Fact l.Prime] (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  have h : (n : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (n : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_ratCast_padicComplex (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : ℂ_[l])‖ = ‖(q : ℚ_[l])‖ := by
  have h : (q : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_prime_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_padicComplex, Padic.norm_p]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem not_dvd_den_of_norm_le_one (l : ℕ) [hl : Fact l.Prime] (q : ℚ) (h : ‖(q : ℚ_[l])‖ ≤ 1) : ¬ l ∣ q.den := by
  apply GlobalTheory.LocalData.not_dvd_den <;> assumption



theorem norm_root_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (β : ℂ_[l]) (hβ : β ∈ (minpoly ℚ α).aroots ℂ_[l]) :
    ‖β‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  let φ := (algHomAdjoinIntegralEquiv ℚ hα).symm ⟨β, hβ⟩
  letI : Algebra ℚ⟮α⟯ ℂ_[l] := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ⟮α⟯ (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let ψ : algebraicClosure ℚ ℂ →ₐ[ℚ⟮α⟯] ℂ_[l] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have e : ψ α = β := by
    have h1 := ψ.commutes (AdjoinSimple.gen ℚ α)
    rw [AdjoinSimple.algebraMap_gen] at h1
    rw [h1]
    exact algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hα ⟨β, hβ⟩
  rw [← e]
  exact h ψ.toRingHom

theorem coeff_norm_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (i : ℕ) :
    ‖(((minpoly ℚ α).coeff i : ℚ) : ℂ_[l])‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set P := (minpoly ℚ α).map (algebraMap ℚ ℂ_[l]) with hP
  let S := (NormedField.valuation (K := ℂ_[l])).integer
  have memS : ∀ z : ℂ_[l], z ∈ S ↔ ‖z‖ ≤ 1 := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast Iff.rfl
  have hmon : P.Monic := (minpoly.monic hα).map _
  have hroots : ∀ β ∈ P.roots, β ∈ S := fun β hβ => (memS β).2 (norm_root_le_one l α h β hβ)
  have hc : (((minpoly ℚ α).coeff i : ℚ) : ℂ_[l]) = P.coeff i := by
    rw [hP, coeff_map, eq_ratCast]
  rw [hc, ← memS]
  by_cases hi : i ≤ P.natDegree
  · rw [coeff_eq_esymm_roots_of_card IsAlgClosed.card_roots_eq_natDegree hi, hmon.leadingCoeff, one_mul]
    refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) ?_
    unfold Multiset.esymm
    refine S.multiset_sum_mem _ fun z hz => ?_
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hz
    exact S.multiset_prod_mem _ fun w hw => hroots w (Multiset.mem_of_le (Multiset.mem_powersetCard.1 ht).1 hw)
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact S.zero_mem

theorem intAt_of_forall_norm_le_one (l : ℕ) [hl : Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) : IntAt l (α : ℂ) := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set p := minpoly ℚ α with hp
  have hmon : p.Monic := minpoly.monic hα
  have hden : ∀ i, ¬ l ∣ (p.coeff i).den := fun i =>
    not_dvd_den_of_norm_le_one l _ (by rw [← norm_ratCast_padicComplex]; exact coeff_norm_le_one l α h i)
  set D : ℕ := ∏ i ∈ Finset.range p.natDegree, (p.coeff i).den with hD
  have hDc : D.Coprime l := Nat.Coprime.prod_left fun i _ =>
    ((Nat.Prime.coprime_iff_not_dvd hl.out).2 (hden i)).symm
  refine ⟨D, hDc, ?_⟩
  set q := p.scaleRoots (D : ℚ) with hq
  have hql : q ∈ lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hq, coeff_scaleRoots]
    rcases lt_trichotomy n p.natDegree with hn | hn | hn
    · obtain ⟨e, he⟩ : (p.coeff n).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hn)
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - n = k + 1 := ⟨p.natDegree - n - 1, by omega⟩
      have h1 : p.coeff n * ((p.coeff n).den : ℚ) = (p.coeff n).num := Rat.mul_den_eq_num _
      refine ⟨(p.coeff n).num * e * D ^ k, ?_⟩
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [hk, pow_succ, ← h1]
      have h2 : (D : ℚ) = (p.coeff n).den * e := by exact_mod_cast he
      rw [h2]
      ring
    · refine ⟨1, ?_⟩
      rw [hn, hmon.coeff_natDegree, Nat.sub_self, pow_zero, mul_one, map_one]
    · refine ⟨0, ?_⟩
      rw [coeff_eq_zero_of_natDegree_lt hn, zero_mul, map_zero]
  have hqm : q.Monic := by
    rw [Monic, hq, leadingCoeff_scaleRoots]; exact hmon
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hql hqm
  have hroot : aeval ((D : algebraicClosure ℚ ℂ) * α) q = 0 := by
    have := scaleRoots_aeval_eq_zero (r := (D : ℚ)) (minpoly.aeval ℚ α)
    simpa using this
  have hint : IsIntegral ℤ ((D : algebraicClosure ℚ ℂ) * α) := by
    refine ⟨Q, hQm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ, algebraMap_int_eq, hQ]
    exact hroot
  have := map_isIntegral_int (algebraicClosure ℚ ℂ).val.toRingHom hint
  simpa using this

theorem valGe_iff_forall_sz (l : ℕ) [hl : Fact l.Prime] (r : ℝ) (x : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r x ↔ ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], Sz l lam r x := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  constructor
  · intro hv lam
    obtain ⟨N, hN, hi⟩ := hv ⌈r⌉ 1 one_pos (by simpa using Int.le_ceil r)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hN
      exact hl.out.one_lt.ne' hN
    have hmem : x ∈ algebraicClosure ℚ ℂ := by
      have h1 : (N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1) ∈ algebraicClosure ℚ ℂ :=
        mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic
      have h2 : ((N : ℂ) * (l : ℂ) ^ ⌈r⌉) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 hN0) (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
      have h3 : x = ((N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1)) * ((N : ℂ) * (l : ℂ) ^ ⌈r⌉)⁻¹ := by
        rw [pow_one, ← mul_assoc, mul_right_comm, mul_inv_cancel₀ h2, one_mul]
      rw [h3]
      exact mul_mem h1 (inv_mem (mul_mem (IntermediateField.natCast_mem _ _) (zpow_mem (IntermediateField.natCast_mem _ _) _)))
    refine ⟨hmem, ?_⟩
    set t := ‖lam ⟨x, hmem⟩‖ with ht
    have key : ∀ (m : ℤ) (n : ℕ), 0 < n → r ≤ (m : ℝ) / n → t ^ n ≤ (l : ℝ) ^ m := by
      intro m n hn hmn
      obtain ⟨N, hN, hi⟩ := hv m n hn hmn
      set β : algebraicClosure ℚ ℂ := (N : algebraicClosure ℚ ℂ) * ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)
      have hiβ : IsIntegral ℤ β := by
        refine (isIntegral_algHom_iff ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) Subtype.val_injective).1 ?_
        have e : ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) β = (N : ℂ) * ((l : ℂ) ^ m * x ^ n) :=
          Complex.ext rfl rfl
        rw [e]; exact hi
      have h1 := norm_le_one_of_isIntegral (map_isIntegral_int lam hiβ)
      simp only [β, map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow] at h1
      rw [norm_natCast_padicComplex, Padic.norm_natCast_eq_one_iff.2 hN.symm, norm_prime_padicComplex, one_mul,
        inv_zpow', zpow_neg, inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one] at h1
      exact h1
    by_contra hgt
    rw [not_le] at hgt
    have htp : 0 < t := (Real.rpow_pos_of_pos hl0 r).trans hgt
    have hr : r < Real.logb l t := (Real.lt_logb_iff_rpow_lt hl1 htp).2 hgt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr
    have hq3 : (l : ℝ) ^ (q : ℝ) < t := (Real.lt_logb_iff_rpow_lt hl1 htp).1 hq2
    have hqe : (q : ℝ) = (q.num : ℝ) / (q.den : ℕ) := by exact_mod_cast (Rat.num_div_den q).symm
    have hk := key q.num q.den q.den_pos (by rw [← hqe]; exact hq1.le)
    have h4 : ((l : ℝ) ^ (q : ℝ)) ^ q.den < t ^ q.den :=
      pow_lt_pow_left₀ hq3 (Real.rpow_nonneg hl0.le _) q.den_pos.ne'
    have h5 : ((l : ℝ) ^ (q : ℝ)) ^ q.den = (l : ℝ) ^ q.num := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le, ← Real.rpow_intCast, hqe,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.2 q.den_pos.ne')]
    rw [h5] at h4
    exact absurd hk (not_le.2 h4)
  · intro h
    let lam₀ : algebraicClosure ℚ ℂ →+* ℂ_[l] := (IsAlgClosed.lift : algebraicClosure ℚ ℂ →ₐ[ℚ] ℂ_[l]).toRingHom
    obtain ⟨hmem, -⟩ := h lam₀
    intro m n hn hmn
    have hmn' : r * n ≤ m := by rwa [le_div_iff₀ (Nat.cast_pos.2 hn)] at hmn
    have hb : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l],
        ‖lam ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)‖ ≤ 1 := by
      intro lam
      obtain ⟨h', hle⟩ := h lam
      rw [map_mul, map_zpow₀, map_pow, map_natCast, norm_mul, norm_zpow, norm_pow, norm_prime_padicComplex,
        inv_zpow', zpow_neg]
      have h2 : ‖lam ⟨x, hmem⟩‖ ^ n ≤ (l : ℝ) ^ m := by
        calc ‖lam ⟨x, hmem⟩‖ ^ n ≤ ((l : ℝ) ^ r) ^ n := pow_le_pow_left₀ (norm_nonneg _) hle n
          _ = (l : ℝ) ^ (r * n) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
          _ ≤ (l : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hl1.le hmn'
          _ = (l : ℝ) ^ m := Real.rpow_intCast _ _
      rw [inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one]
      exact h2
    have := intAt_of_forall_norm_le_one l _ hb
    have e : (((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n : algebraicClosure ℚ ℂ) : ℂ) = (l : ℂ) ^ m * x ^ n :=
      Complex.ext rfl rfl
    rwa [e] at this

end GlobalTheory.LadicDenom
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

open Polynomial

namespace AICStalk

theorem isIntegrallyClosed_of_aic {A : Type} [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  apply LateralTheory.E.LocalIntegralClosureRoots.isIntegrallyClosed_of_aic <;> assumption

theorem aic_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : GlobalTheory.EtC.AIC R) :
    GlobalTheory.EtC.AIC S := by
  intro p hpm hdeg
  have hm : (p.map (e.symm : S →+* R)).Monic := hpm.map _
  have hd : (p.map (e.symm : S →+* R)).natDegree = p.natDegree :=
    natDegree_map_eq_of_injective e.symm.injective p
  obtain ⟨a, ha⟩ := h _ hm (hd ▸ hdeg)
  refine ⟨e a, ?_⟩
  have hp : p = (p.map (e.symm : S →+* R)).map (e : R →+* S) := by
    rw [Polynomial.map_map]; ext n; simp
  rw [hp, Polynomial.eval_map, show e a = (e : R →+* S) a from rfl, Polynomial.eval₂_at_apply, ha, map_zero]

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : GlobalTheory.EtC.AIC K := by
  intro p _ hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hdeg)]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem algebraMap_injective_of_indEt {A O : Type} [CommRing A] [IsDomain A] [CommRing O]
    [Nontrivial O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : Function.Injective (algebraMap A O) := by
  haveI : Module.Flat A O := GlobalTheory.IndEtaleLocal.flat_of_isIndEtale h
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hmem : (1 : O) ∈ Submodule.torsion A O := by
    rw [Submodule.mem_torsion_iff]
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, by simp [Algebra.smul_def, ha]⟩
  rw [Module.Flat.torsion_eq_bot] at hmem
  exact one_ne_zero ((Submodule.mem_bot A).mp hmem)

theorem isDomain_of_indEt {A O : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing O] [IsLocalRing O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : IsDomain O := by
  refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
  let I : Ideal (MvPolynomial (Fin 2) A) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
  haveI : Algebra.FinitePresentation A (MvPolynomial (Fin 2) A ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  let g : (MvPolynomial (Fin 2) A ⧸ I) →ₐ[A] O :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hxy])
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
  have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
    have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
    exact this.trans (MvPolynomial.aeval_X _ i)
  have h0 : w 0 * w 1 = 0 := by
    have : Ideal.Quotient.mkₐ A I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ A I (MvPolynomial.X 1) = 0 := by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [w, ← map_mul, this, map_zero]
  let q : Ideal W := (IsLocalRing.maximalIdeal O).comap v
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨hdom, -⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A W q
  have hq : ∀ t ∈ q.primeCompl, IsUnit (v t) := fun t ht => by
    by_contra hc
    exact ht (IsLocalRing.mem_maximalIdeal _ |>.mpr hc)
  have hm : algebraMap W (Localization.AtPrime q) (w 0) * algebraMap W (Localization.AtPrime q) (w 1) = 0 := by
    rw [← map_mul, h0, map_zero]
  rcases mul_eq_zero.mp hm with h1 | h1
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inl (((hq t ht).mul_right_eq_zero).mp this)
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inr (((hq t ht).mul_right_eq_zero).mp this)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem isIntegral_tmul_one {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [Algebra A O]
    (h : GlobalTheory.EtC.IndEt A O) (o : O) :
    IsIntegral (FractionRing A) (o ⊗ₜ[A] (1 : FractionRing A)) := by
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h (Polynomial.aeval (R := A) o)
  haveI : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.Etale.baseChange A W _
  haveI : Module.Finite (FractionRing A) (FractionRing A ⊗[A] W) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  haveI : Algebra.IsIntegral (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.IsIntegral.of_finite _ _
  let χ : W →ₐ[A] O ⊗[A] FractionRing A := (Algebra.TensorProduct.includeLeft (S := A)).comp v
  let Χ : FractionRing A ⊗[A] W →ₐ[FractionRing A] O ⊗[A] FractionRing A :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) χ (fun _ _ => Commute.all _ _)
  have hX : Χ (1 ⊗ₜ (u Polynomial.X)) = o ⊗ₜ 1 := by
    have := DFunLike.congr_fun huv Polynomial.X
    simp only [AlgHom.comp_apply, Polynomial.aeval_X] at this
    simp [Χ, χ, this]
  rw [← hX]
  exact (Algebra.IsIntegral.isIntegral _).map Χ

end AICStalk


open AICStalk in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem isField_aic_tensor_fractionRing_of_strictlyHenselian :
    ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], GlobalTheory.EtC.AIC A →
      GlobalTheory.EtC.SH O → GlobalTheory.EtC.IndEt A O →
      IsField (O ⊗[A] FractionRing A) ∧ GlobalTheory.EtC.AIC (O ⊗[A] FractionRing A) := by
  intro A O _ _ _ _ hA hO h
  haveI := isIntegrallyClosed_of_aic hA
  obtain ⟨hH, -⟩ := hO
  haveI := hH
  haveI := isDomain_of_indEt h
  haveI : IsAlgClosed (FractionRing A) := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors A))
      (O ⊗[A] FractionRing A) := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) (FractionRing A)]
    infer_instance
  have hinj := algebraMap_injective_of_indEt h
  haveI : IsDomain (O ⊗[A] FractionRing A) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors A)) (O ⊗[A] FractionRing A) (by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))
  have hall : ∀ x : O ⊗[A] FractionRing A, IsIntegral (FractionRing A) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul o k =>
      have : o ⊗ₜ[A] k = (o ⊗ₜ[A] (1 : FractionRing A)) * algebraMap (FractionRing A) _ k := by
        rw [show algebraMap (FractionRing A) (O ⊗[A] FractionRing A) k = 1 ⊗ₜ k from rfl,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact (isIntegral_tmul_one h o).mul isIntegral_algebraMap
    | add x y hx hy => exact hx.add hy
  haveI : Algebra.IsIntegral (FractionRing A) (O ⊗[A] FractionRing A) := ⟨hall⟩
  let e := RingEquiv.ofBijective _
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := FractionRing A) (K := O ⊗[A] FractionRing A))
  exact ⟨MulEquiv.isField (Field.toIsField (FractionRing A)) e.symm.toMulEquiv,
    aic_of_ringEquiv e (aic_of_isAlgClosed _)⟩

end GlobalTheory
end

section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ α : 𝓞 K, α ≠ 0 → Integrable (GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K))) ∧ 2 ^ Fintype.card I * ∫ y, GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.wt φ n (α : K) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℂ) ^ (-s) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y‖ = (∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2)) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) ^ (-s.re) := by
  first | exact @GlobalTheory.HeckeMellinOne.mellin_term | exact GlobalTheory.HeckeMellinOne.mellin_term | (intros; apply GlobalTheory.HeckeMellinOne.mellin_term <;> assumption)
end

section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.classMean_log_norm_disc_chowlaSelberg : ∀ (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → discr K = -(D.host.d : ℤ) → 4 < D.host.d → ∀ (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : ClassGroup (𝓞 K) → PeriodPair), (∀ c, ClassGroup.mk K (rep c) = c) → (∀ c, IsLatOf φK (rep c : FractionalIdeal (𝓞 K)⁰ K) (L c)) → (∑ c, Real.log (nrm (rep c : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (L c)‖)) / (classNumber K : ℝ) = 12 * Real.log (2 * Real.pi) - 6 * Real.log D.host.d + 6 * Real.eulerMascheroniConstant - 6 * Formalism.BasicNotions.dlogL D 1 := by
  first | exact @GlobalTheory.ClassMeanDisc.classMean_log_norm_disc | exact GlobalTheory.ClassMeanDisc.classMean_log_norm_disc | (intros; apply GlobalTheory.ClassMeanDisc.classMean_log_norm_disc <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.differentiableOn_hilbertEisensteinWeightTwoSeries : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (fun z => ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  first | exact @GlobalTheory.QHolo.qholo | exact GlobalTheory.QHolo.qholo | (intros; apply GlobalTheory.QHolo.qholo <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.thetaSeriesTerm_smul_add_decomposition : ∀ (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt) (y : N.X), h ^ m = N.io y → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S) → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S) → ∀ a b : N.X, ∃ w : Oˣ, (w : O) ∈ S ∧ N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  first | exact @GlobalTheory.theta_term_smul_add | exact GlobalTheory.theta_term_smul_add | (intros; apply GlobalTheory.theta_term_smul_add <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_perm_transport_modular_families_values : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∃ ρ : Equiv.Perm ι, ∀ s i, g (f s i τ₀ / ω₀ ^ m s) = f' s (ρ i) τ₁ / ω₁ ^ m s := by
  first | exact @GlobalTheory.QFam.exists_perm_transport_families | exact GlobalTheory.QFam.exists_perm_transport_families | (intros; apply GlobalTheory.QFam.exists_perm_transport_families <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.qConj_torsion_points : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), ZetaAct g N a → ∀ x : Fin 2 → ZMod N, QConj g N (wp N x) (wp N (vmul x (dg a))) ∧ QConj g N (wpd N x) (wpd N (vmul x (dg a))) ∧ (x ≠ 0 → QConj g N (wB N x) (wB N (vmul x (dg a)))) := by
  first | exact @GlobalTheory.WpFam.ConjExp.qConj_torsion | exact GlobalTheory.WpFam.ConjExp.qConj_torsion | (intros; apply GlobalTheory.WpFam.ConjExp.qConj_torsion <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.norm_map_surjective_finite_field : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), ∃ δ : GL (Fin n) F', (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧ nrm s δ = incl F F' n γ := by
  first | (exact @GlobalTheory.Shin.NormSurj.nrm_surj_adjoin) | (exact GlobalTheory.Shin.NormSurj.nrm_surj_adjoin) | (intros; apply GlobalTheory.Shin.NormSurj.nrm_surj_adjoin  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.green_function_character_sum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) (S : F[X] → ℂ), 0 < m → ((Nat.card F : ℂ) ^ m - 1) * ∑ᶠ x, psiG (rootSum θ k) m x * star (chG S m x) = (Nat.card (GL (Fin m) F) : ℂ) * ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ m - 1) = 1}, θ α ^ k * star (S (minpoly F α ^ (m / (minpoly F α).natDegree))) := by
  first | (exact @GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus) | (exact GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus) | (intros; apply GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus  <;> assumption)
end
