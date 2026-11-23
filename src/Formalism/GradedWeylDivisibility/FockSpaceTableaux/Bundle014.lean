module

public import Formalism.GradedWeylDivisibility.Bundle001
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle011
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle009
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lfockq_mat {r : ℕ} (a b : Fin r) (t : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun c d => (if c = d then 1 else 0) + (if c = b ∧ d = a then t else 0)

lemma lfockq_mat_conjTranspose {r : ℕ} (a b : Fin r) (t : ℂ) :
    (lfockq_mat a b t).conjTranspose = lfockq_mat b a (star t) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, lfockq_mat, star_add]
  split_ifs <;> first
    | (simp_all; done)
    | grind
    | (obtain ⟨h1, h2⟩ := ‹_ ∧ _›; subst h1; simp_all)

lemma lfockq_eval_rowGen {r n : ℕ} (a b : Fin r) (t : ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    Polynomial.eval (C t) (rowGen ℂ a b f) = rowAct ℂ (lfockq_mat a b t) f := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp [rowGen, rowAct]
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.eval_add, hp, hq, map_add (f := _)]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul]
    congr 1
    rcases v with ⟨i, j⟩
    simp only [rowGen, rowAct, MvPolynomial.aeval_X, lfockq_mat]
    by_cases hv : i = b
    · subst hv
      simp [add_mul, Finset.sum_add_distrib, apply_ite (C : ℂ → MvPolynomial (Fin r × Fin n) ℂ),
        ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
      exact mul_comm _ _
    · simp [hv, add_mul, Finset.sum_add_distrib, apply_ite (C : ℂ → MvPolynomial (Fin r × Fin n) ℂ),
        ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma lfockq_eval_C {σ : Type*} (P : Polynomial (MvPolynomial σ ℂ)) (N : ℕ) (hN : P.natDegree < N)
    (t : ℂ) : Polynomial.eval (C t) P = ∑ i ∈ Finset.range N, C (t ^ i) * P.coeff i := by
  rw [Polynomial.eval_eq_sum_range' hN]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, mul_comm]

private lemma fockF_add_left_lemma {σ : Type*} (f f' g : MvPolynomial σ ℂ) :
    fockF (f + f') g = fockF f g + fockF f' g := by
  classical
  unfold fockF
  have key : ∀ h : MvPolynomial σ ℂ, ∀ s : Finset (σ →₀ ℕ), h.support ⊆ s →
      ∑ m ∈ h.support, h.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
        ∑ m ∈ s, h.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    intro h s hs
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [MvPolynomial.notMem_support_iff.mp hm]
    simp
  rw [key (f + f') (f.support ∪ f'.support) MvPolynomial.support_add,
    key f (f.support ∪ f'.support) Finset.subset_union_left,
    key f' (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

private lemma fockF_sum_left_lemma_2 {σ ι : Type*} (s : Finset ι) (h : ι → MvPolynomial σ ℂ)
    (g : MvPolynomial σ ℂ) : fockF (∑ i ∈ s, h i) g = ∑ i ∈ s, fockF (h i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockF]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fockF_add_left_lemma, ih]

lemma lfockq_fockF_eval_left {σ : Type*} (P : Polynomial (MvPolynomial σ ℂ)) (N : ℕ)
    (hN : P.natDegree < N) (t : ℂ) (G : MvPolynomial σ ℂ) :
    fockF (Polynomial.eval (C t) P) G = ∑ i ∈ Finset.range N, t ^ i * fockF (P.coeff i) G := by
  rw [lfockq_eval_C P N hN t, fockF_sum_left_lemma_2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LFocks_C_mul_left]

private lemma fockF_add_right_lemma_3 {σ : Type*} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

private lemma fockF_sum_right_lemma_4 {σ ι : Type*} (s : Finset ι) (h : ι → MvPolynomial σ ℂ)
    (f : MvPolynomial σ ℂ) : fockF f (∑ i ∈ s, h i) = ∑ i ∈ s, fockF f (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockF]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fockF_add_right_lemma_3, ih]

lemma lfockq_fockF_eval_right {σ : Type*} (P : Polynomial (MvPolynomial σ ℂ)) (N : ℕ)
    (hN : P.natDegree < N) (t : ℂ) (F : MvPolynomial σ ℂ) :
    fockF F (Polynomial.eval (C t) P) = ∑ i ∈ Finset.range N, star (t ^ i) * fockF F (P.coeff i) := by
  rw [lfockq_eval_C P N hN t, fockF_sum_right_lemma_4]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LFocks_C_mul_right]

lemma lfockq_adjC {r n : ℕ} (a b : Fin r) (k : ℕ) (F G : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (rowDiv ℂ a b k F) G = fockF F (rowDiv ℂ b a k G) := by
  classical
  set N := max (max (rowGen ℂ a b F).natDegree (rowGen ℂ b a G).natDegree) k + 1 with hNdef
  have h1 : (rowGen ℂ a b F).natDegree < N := by omega
  have h2 : (rowGen ℂ b a G).natDegree < N := by omega
  have hk : k < N := by omega
  have key : ∀ t : ℂ, ∑ i ∈ Finset.range N, t ^ i * fockF ((rowGen ℂ a b F).coeff i) G =
      ∑ i ∈ Finset.range N, t ^ i * fockF F ((rowGen ℂ b a G).coeff i) := by
    intro t
    have hadj : fockF (rowAct ℂ (lfockq_mat a b t) F) G =
        fockF F (rowAct ℂ (lfockq_mat a b t).conjTranspose G) := by
      rw [LFocks_rowAct_eq_sub, LFocks_rowAct_eq_sub, LFocks_subAdj, LFocks_rowMat_conjTranspose]
    rw [lfockq_mat_conjTranspose, ← lfockq_eval_rowGen, ← lfockq_eval_rowGen,
      lfockq_fockF_eval_left _ N h1, lfockq_fockF_eval_right _ N h2] at hadj
    rw [hadj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_pow, star_star]
  let p : Polynomial ℂ := ∑ i ∈ Finset.range N,
    Polynomial.C (fockF ((rowGen ℂ a b F).coeff i) G) * Polynomial.X ^ i
  let q : Polynomial ℂ := ∑ i ∈ Finset.range N,
    Polynomial.C (fockF F ((rowGen ℂ b a G).coeff i)) * Polynomial.X ^ i
  have hpq : p = q := by
    apply Polynomial.funext
    intro t
    simp only [p, q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    calc _ = ∑ i ∈ Finset.range N, t ^ i * fockF ((rowGen ℂ a b F).coeff i) G :=
          Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = ∑ i ∈ Finset.range N, t ^ i * fockF F ((rowGen ℂ b a G).coeff i) := key t
      _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc := congrArg (fun s : Polynomial ℂ => s.coeff k) hpq
  simp only [p, q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq] at hc
  simpa [rowDiv, Finset.mem_range.mpr hk] using hc

lemma lfockq_cast {σ : Type*} (f g : MvPolynomial σ ℚ) :
    ((fockQ f g : ℚ) : ℂ) = fockF (map (Rat.castHom ℂ) f) (map (Rat.castHom ℂ) g) := by
  unfold fockQ fockF
  rw [MvPolynomial.support_map_of_injective _ (Rat.castHom ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.coeff_map]

lemma lfockq_map_rowGen {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    rowGen ℂ a b (map (Rat.castHom ℂ) f) =
      Polynomial.map (map (Rat.castHom ℂ)) (rowGen ℚ a b f) := by
  have h : ((rowGen ℂ a b).toRingHom.comp (map (Rat.castHom ℂ)) :
      MvPolynomial (Fin r × Fin n) ℚ →+* Polynomial (MvPolynomial (Fin r × Fin n) ℂ)) =
      (Polynomial.mapRingHom (map (Rat.castHom ℂ))).comp (rowGen ℚ a b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp [rowGen]
    · intro v
      simp only [rowGen, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.map_X, MvPolynomial.aeval_X, Polynomial.coe_mapRingHom]
      split_ifs <;> simp
  exact RingHom.congr_fun h f

lemma lfockq_map_rowDiv {r n : ℕ} (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    map (Rat.castHom ℂ) (rowDiv ℚ a b k f) = rowDiv ℂ a b k (map (Rat.castHom ℂ) f) := by
  unfold rowDiv
  rw [lfockq_map_rowGen, Polynomial.coeff_map]

theorem fock_space_row_divided_adjoint : FockQRowDivAdj := by
  intro r n a b k f g
  have h := lfockq_adjC a b k (map (Rat.castHom ℂ) f) (map (Rat.castHom ℂ) g)
  rw [← lfockq_map_rowDiv, ← lfockq_map_rowDiv, ← lfockq_cast, ← lfockq_cast] at h
  exact_mod_cast h

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial
open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem toLex_lt_of_eq_of_lt_at {N : ℕ} {a b : Fin N →₀ ℕ} (i : Fin N)
    (h1 : ∀ i', i' < i → a i' = b i') (h2 : a i < b i) : toLex a < toLex b := by
  exact Finsupp.lex_def.2 ⟨i, h1, h2⟩

private theorem domCongr_cmIdx_apply_eq {r n : ℕ} (m : Fin r × Fin n →₀ ℕ)
    (x : Fin r × Fin n) :
    Finsupp.domCongr (cmIdx r n) m (cmIdx r n x) = m x := by
  simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]

private theorem toSyn_le_toSyn_degree_of_mem_support {σ R : Type*} [CommSemiring R] (M : MonomialOrder σ)
    {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    M.toSyn d ≤ M.toSyn (M.degree f) := by
  exact M.le_degree hd

theorem sliceLeading : PeelLead := by
  unfold PeelLead
  intro B _ _ r n l j hlj a0 ω g K hg hω hK htop
  have hlj' : l ≠ j := ne_of_lt hlj
  have hd : (colLex r n).degree (peel l j a0 K g) ∈
      (peel l j a0 K g).support :=
    (colLex r n).degree_mem_support hK
  obtain ⟨m0, hm0, hm0K, hd_eq⟩ := lcplead_mem_support_peel a0 K hd
  have hm0_eq := lcplead_recon hlj' a0 hg hm0
  rw [hm0K, ← hd_eq] at hm0_eq
  rw [← hm0_eq]
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hm0
  have hup : ∀ m ∈ g.support, (colLex r n).toSyn m ≤ (colLex r n).toSyn m0 := by
    intro m hm
    rcases lt_trichotomy (m (a0, l)) K with hlt | heq | hgt
    · apply le_of_lt
      apply colLex_lt_iff.2
      refine toLex_lt_of_eq_of_lt_at (cmIdx r n (a0, l)) ?_ ?_
      · intro i' hi'
        obtain ⟨⟨b, t⟩, rfl⟩ := (cmIdx r n).surjective i'
        rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq]
        rcases lcplead_cmIdx_lt hi' with ht | ⟨ht, hb⟩
        · have htl : t ≠ l := ne_of_lt ht
          have htj : t ≠ j := ne_of_lt (lt_trans ht hlj)
          rw [lcplead_hom_off hlj' hg hm b t htl htj,
            lcplead_hom_off hlj' hg hm0 b t htl htj]
        · rw [ht]
          have h1 := lcplead_hom_row hlj' hg hm b
          have h2 := lcplead_hom_row hlj' hg hm0 b
          have h3 := hω b hb
          omega
      · rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq, hm0K]
        exact hlt
    · have hc := lcplead_coeff_peel hlj' a0 hg hm
      rw [heq] at hc
      have he : (m.erase (a0, l)).erase (a0, j) ∈ (peel l j a0 K g).support := by
        rw [mem_support_iff, hc]
        exact mem_support_iff.1 hm
      have hle := toSyn_le_toSyn_degree_of_mem_support (colLex r n) he
      have hm_eq := lcplead_recon hlj' a0 hg hm
      rw [heq] at hm_eq
      rw [hm_eq, hm0_eq]
      simp only [map_add (f := _)]
      exact add_le_add le_rfl hle
    · exfalso
      have hc := lcplead_coeff_peel hlj' a0 hg hm
      simp only [htop _ hgt, AddMonoidAlgebra.coeff_zero] at hc
      exact mem_support_iff.1 hm hc.symm
  exact (colLex r n).toSyn.injective
    (le_antisymm (hup _ ((colLex r n).degree_mem_support hg0))
      (toSyn_le_toSyn_degree_of_mem_support (colLex r n) hm0))

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem nabla_weight_le : NablaLLe := by
  intro R K _ _ _ k n ν g hg F hF
  unfold nablaL at hF
  rw [Submodule.mem_comap, Submodule.mem_map] at hF
  obtain ⟨G, hG, hGF⟩ := hF
  have hGF' : map (algebraMap R K) G = rowAct K g F := hGF

  have hGK : map (algebraMap R K) G ∈ dualWeyl K k n ν := by
    unfold dualWeyl at hG ⊢
    rw [Submodule.mem_inf] at hG ⊢
    obtain ⟨hG1, hG2⟩ := hG
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hG1 ⊢
      intro d hd
      apply hG1
      intro h0
      apply hd
      rw [coeff_map, h0, map_zero]
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hG2 ⊢
      intro l j hlj
      have e := hG2 l j hlj
      have hc : ∀ p : MvPolynomial (Fin k × Fin n) R,
          colAddGen K l j (map (algebraMap R K) p) = map (algebraMap R K) (colAddGen R l j p) := by
        intro p
        induction p using MvPolynomial.induction_on
        · rename_i a
          simp [colAddGen]
        · rename_i p q hp hq
          simp only [map_add (f := _), hp, hq]
        · rename_i p v hp
          simp only [map_mul, hp]
          congr 1
          simp only [colAddGen, map_X, aeval_X]
          split_ifs <;> simp
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      rw [hc, ← map_rename, ← map_sub, e, map_zero]

  have hinv : ∀ (A : Matrix (Fin k) (Fin k) K) (P : MvPolynomial (Fin k × Fin n) K),
      P ∈ dualWeyl K k n ν → rowAct K A P ∈ dualWeyl K k n ν := by
    intro A P hP
    unfold dualWeyl at hP ⊢
    rw [Submodule.mem_inf] at hP ⊢
    obtain ⟨hP1, hP2⟩ := hP
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hP1 ⊢
      have hXw : ∀ v : Fin k × Fin n,
          IsWeightedHomogeneous (colW k n) (rowAct K A (X v)) (colW k n v) := by
        intro v
        simp only [rowAct, aeval_X]
        apply IsWeightedHomogeneous.sum
        intro b _
        have h := (isWeightedHomogeneous_C (colW k n) (A v.1 b)).mul
          (isWeightedHomogeneous_X K (colW k n) (b, v.2))
        simpa [colW] using h

      rw [P.as_sum, map_sum]
      apply IsWeightedHomogeneous.sum
      intro d hd
      rw [← hP1 (mem_support_iff.mp hd), monomial_eq, map_mul, map_finsuppProd, Finsupp.weight_apply]
      simp only [map_pow]
      have hC : rowAct K A (C (AddMonoidAlgebra.coeff P d) : MvPolynomial (Fin k × Fin n) K) = C (AddMonoidAlgebra.coeff P d) := by
        simp [rowAct]
      rw [hC]
      have h := (isWeightedHomogeneous_C (colW k n) (AddMonoidAlgebra.coeff P d)).mul
        (IsWeightedHomogeneous.prod d.support _ _ fun v _ => (hXw v).pow (d v))
      simpa [Finsupp.prod, Finsupp.sum] using h
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hP2 ⊢
      intro l j hlj
      have e := hP2 l j hlj
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      let A' : MvPolynomial (Option (Fin k × Fin n)) K →ₐ[K] MvPolynomial (Option (Fin k × Fin n)) K :=
        aeval fun o => o.elim (X none) (fun v => ∑ b : Fin k, C (A v.1 b) * X (some (b, v.2)))
      have h1 : (colAddGen K l j).comp (rowAct K A) = A'.comp (colAddGen K (r := k) l j) := by
        apply MvPolynomial.algHom_ext
        intro v
        by_cases hv : v.2 = j
        · simp [A', colAddGen, rowAct, hv, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
            mul_left_comm]
        · simp [A', colAddGen, rowAct, hv]
      have h2 : (rename (R := K) (some : Fin k × Fin n → Option (Fin k × Fin n))).comp (rowAct K A) =
          A'.comp (rename some) := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [A', rowAct]
      have e1 := congrArg (fun Φ => Φ P) h1
      have e2 := congrArg (fun Φ => Φ P) h2
      simp only [AlgHom.comp_apply] at e1 e2
      rw [e1, e2, ← map_sub, e, map_zero]
  have hid : rowAct K (1 : Matrix (Fin k) (Fin k) K) F = F := by
    have e1 : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single v.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    rw [e1]
    rfl
  have e := congrArg (fun Φ => Φ F) (row_action_mul K k n g⁻¹ g)
  simp only [AlgHom.comp_apply] at e
  rw [Matrix.mul_nonsing_inv g hg, hid] at e
  rw [← e, ← hGF']
  exact hinv _ _ hGK

end Formalism.GradedWeylDivisibility
end
end
