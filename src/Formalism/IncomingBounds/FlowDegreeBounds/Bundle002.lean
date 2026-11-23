module

import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubstSame
public import Formalism.IncomingBounds.Bundle002
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.Bundle001
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndexSigned
public import Formalism.IncomingBounds.DefsThmP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.MvPowerSeries.Order
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

section

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

section
variable {C : Type} [Field C]

theorem tpjet_jetAt0_superset {σ : Type} (P : MvPolynomial σ C) (G : MvPowerSeries σ C)
    (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jetAt0 P G = ∑ m ∈ S, AddMonoidAlgebra.coeff P m * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]

private theorem mem_support_or_of_mem_support_add {σ : Type} (P Q : MvPolynomial σ C)
    (a : σ →₀ ℕ) (ha : a ∈ (P + Q).support) : a ∈ P.support ∨ a ∈ Q.support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at ha
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
  by_cases hP : AddMonoidAlgebra.coeff P a = 0
  · right
    rwa [hP, zero_add] at ha
  · exact Or.inl hP

theorem tpjet_jetAt0_add {σ : Type} (P Q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (P + Q) G = jetAt0 P G + jetAt0 Q G := by
  apply GlobalTheory.MinorShiftJet.jetAt0_add_left <;> assumption

theorem tpjet_jetAt0_zero {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  unfold jetAt0
  simp

theorem tpjet_jetAt0_sum {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, tpjet_jetAt0_zero]
  · intro j t hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]

end
end Formalism.IncomingBounds
end
end

section

noncomputable section

open Module
open scoped Pointwise

namespace Formalism.IncomingBounds.LatticeIndexAlt

open Formalism.LatticeIndexTer

variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]

theorem map_comap_sub (W : Submodule K X) (A : Submodule O X) :
    (A.comap ((W.subtype).restrictScalars O)).map ((W.subtype).restrictScalars O) =
      A ⊓ W.restrictScalars O := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨hx, hW⟩
    exact ⟨⟨x, hW⟩, hx, rfl⟩

theorem qlen_comap (W : Submodule K X) (A B : Submodule O X) :
    qlen O W (A.comap ((W.subtype).restrictScalars O)) (B.comap ((W.subtype).restrictScalars O)) =
      qlen O X (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) := by
  unfold qlen
  have hinj : Function.Injective ((W.subtype).restrictScalars O) := fun a b h => Subtype.ext h
  let e : ↥(A.comap ((W.subtype).restrictScalars O)) ≃ₗ[O] ↥(A ⊓ W.restrictScalars O) :=
    (Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ (map_comap_sub W A))
  refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e ?_)
  ext z
  rw [Submodule.mem_map_equiv]
  have key : (((e.symm z : ↥(A.comap ((W.subtype).restrictScalars O))) : W) : X) = (z : X) :=
    congrArg Subtype.val (e.apply_symm_apply z)
  have hzW : (z : X) ∈ W := (Submodule.mem_inf.mp z.2).2
  constructor
  · intro h
    have h' : (((e.symm z : ↥(A.comap ((W.subtype).restrictScalars O))) : W) : X) ∈ B := h
    rw [key] at h'
    show (z : X) ∈ B ⊓ W.restrictScalars O
    exact Submodule.mem_inf.mpr ⟨h', hzW⟩
  · intro h
    have h2 : (z : X) ∈ B ⊓ W.restrictScalars O := h
    have h' : (z : X) ∈ B := (Submodule.mem_inf.mp h2).1
    rw [← key] at h'
    exact h'

theorem idx_comap (W : Submodule K X) (A B : Submodule O X) :
    idx O W (A.comap ((W.subtype).restrictScalars O)) (B.comap ((W.subtype).restrictScalars O)) =
      idx O X (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) := by
  unfold idx
  rw [qlen_comap W A B, qlen_comap W B A]


omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem isLat_scale {Y : Type} [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y]
    (c : K) (hc : c ≠ 0) (A : Submodule O Y) (hA : IsLat O K Y A) :
    IsLat O K Y (A.map ((c • LinearMap.id : Y →ₗ[K] Y).restrictScalars O)) := by
  unfold IsLat at hA ⊢
  refine ⟨hA.1.map _, ?_⟩
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hA.2, Submodule.map_top,
    LinearMap.range_eq_top]
  intro x
  refine ⟨c⁻¹ • x, ?_⟩
  simp [smul_smul, hc]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem isLat_sup {Y : Type} [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y]
    (A B : Submodule O Y) (hA : A.FG) (hB : IsLat O K Y B) : IsLat O K Y (A ⊔ B) := by
  unfold IsLat at hB ⊢
  refine ⟨hA.sup hB.1, ?_⟩
  rw [eq_top_iff, ← hB.2]
  exact Submodule.span_mono (fun x hx => Submodule.mem_sup_right hx)

end Formalism.IncomingBounds.LatticeIndexAlt

namespace Formalism.IncomingBounds

open Formalism.LatticeIndexTer LatticeIndexAlt

theorem index_last_reduction_holds : IndexLastStep := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ e M Θ hM hΘ W
  rw [← idx_comap W M Θ]
  have hc : (algebraMap O K ϖ) ^ e ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero)
  have hNl := isLat_sup (K := K)
    (M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O)) Θ
    (hM.1.map _) hΘ
  generalize hN : M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O)
    ⊔ Θ = N at hNl ⊢
  have hMN : ∀ x ∈ M, (algebraMap O K ϖ) ^ e • x ∈ N := by
    intro x hx
    rw [← hN]
    exact Submodule.mem_sup_left ⟨x, hx, by simp⟩
  have hΘN : Θ ≤ N := hN ▸ le_sup_right
  let ι : W →ₗ[O] X := (W.subtype).restrictScalars O
  have hι : Function.Injective ι := Subtype.val_injective
  let fW : W →ₗ[O] W := ((((algebraMap O K ϖ) ^ e) • LinearMap.id : W →ₗ[K] W).restrictScalars O)
  have hA₀ : IsLat O K W (M.comap ι) := LatticeIndexValuation.isLat_comap M hM W
  have hB₀ : IsLat O K W (Θ.comap ι) := LatticeIndexValuation.isLat_comap Θ hΘ W
  have hN₀ : IsLat O K W (N.comap ι) := LatticeIndexValuation.isLat_comap N hNl W
  have hS₀ : IsLat O K W ((M.comap ι).map fW) := isLat_scale _ hc _ hA₀
  have hadd1 := lattice_index_add O K W (M.comap ι) ((M.comap ι).map fW) (Θ.comap ι) hA₀ hS₀ hB₀
  have hadd2 := lattice_index_add O K W ((M.comap ι).map fW) (N.comap ι) (Θ.comap ι) hS₀ hN₀ hB₀
  have h1 : idx O W (M.comap ι) ((M.comap ι).map fW) = e * (finrank K W : ℤ) := by
    have hs := lattice_index_scale O K W ϖ hϖ (-e) (M.comap ι) hA₀
    rw [neg_neg] at hs
    exact hs
  have hSN : (M.comap ι).map fW ≤ N.comap ι := by
    rintro _ ⟨y, hy, rfl⟩
    have := hMN _ hy
    simpa [ι, fW] using this
  have h2 : idx O W ((M.comap ι).map fW) (N.comap ι) ≤ 0 := by
    unfold idx
    rw [subgroupData.qlen_eq_zero hSN]
    simp
  have hle : qlen O W (N.comap ι) (Θ.comap ι) ≤ qlen O X N Θ := by
    unfold qlen
    rw [LatticeIndexValuation.length_map_inj ι hι]
    refine subgroupData.length_le_of_le (Submodule.map_comap_le ι N) (Submodule.map_comap_le ι Θ) ?_
    intro x hx
    obtain ⟨⟨w, -, rfl⟩, hxΘ⟩ := Submodule.mem_inf.mp hx
    exact ⟨w, hxΘ, rfl⟩
  have h3 : idx O W (N.comap ι) (Θ.comap ι) ≤ ((qlen O X N Θ).toNat : ℤ) := by
    have h4 : (qlen O W (N.comap ι) (Θ.comap ι)).toNat ≤ (qlen O X N Θ).toNat :=
      ENat.toNat_le_toNat hle (lattice_quotient_finite O K X N Θ hNl hΘ)
    unfold idx
    omega
  linarith

end Formalism.IncomingBounds
end
end

section

noncomputable section
open scoped BigOperators
open MvPowerSeries Finset

namespace Formalism.IncomingBounds

section ThmPExpLemmas

variable {C : Type} [Field C] {σ : Type}

theorem thmPExp_coeff_pow_eq_zero {h : MvPowerSeries σ C} (hh : constantCoeff h = 0)
    {m : σ →₀ ℕ} {k : ℕ} (hk : m.degree < k) : coeff m (h ^ k) = 0 :=
  coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hk)
    (le_order_pow_of_constantCoeff_eq_zero k hh))

theorem thmPExp_coeff_pow_mul_pow_eq_zero {a b : MvPowerSeries σ C} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) {m : σ →₀ ℕ} {j j' : ℕ} (hk : m.degree < j + j') :
    coeff m (a ^ j * b ^ j') = 0 :=
  by
  have h1 := le_order_pow_of_constantCoeff_eq_zero j ha
  have h2 := le_order_pow_of_constantCoeff_eq_zero j' hb
  apply coeff_of_lt_order
  calc ((m.degree : ℕ) : ℕ∞) < ((j + j' : ℕ) : ℕ∞) := by exact_mod_cast hk
    _ = (j : ℕ∞) + (j' : ℕ∞) := by push_cast; rfl
    _ ≤ (a ^ j).order + (b ^ j').order := add_le_add h1 h2
    _ ≤ _ := le_order_mul

theorem thmPExp_coeff_mvExp {h : MvPowerSeries σ C} (hh : constantCoeff h = 0)
    (m : σ →₀ ℕ) {N : ℕ} (hN : m.degree < N) :
    coeff m (mvExp h) = ∑ k ∈ range N, coeff m (h ^ k) / (k.factorial : C) := by
  change ∑ k ∈ range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) = _
  apply Finset.sum_subset (range_subset_range.2 (by omega))
  intro k hk hk'
  simp only [mem_range, not_lt] at hk hk'
  rw [thmPExp_coeff_pow_eq_zero hh (by omega), zero_div]

theorem thmPExp_degree_le_of_mem_antidiagonal [DecidableEq σ] {m : σ →₀ ℕ} {pq : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hpq : pq ∈ antidiagonal m) : pq.1.degree ≤ m.degree ∧ pq.2.degree ≤ m.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  have := congrArg Finsupp.degree hpq
  rw [map_add (f := _)] at this
  omega

end ThmPExpLemmas

theorem thmPExp_choose_div_factorial {K : Type} [Field K] [CharZero K] {k j : ℕ} (hjk : j ≤ k) :
    ((k.choose j : ℕ) : K) / (k.factorial : K) =
      1 / ((j.factorial : K) * ((k - j).factorial : K)) := by
  have h := congrArg (Nat.cast : ℕ → K) (Nat.choose_mul_factorial_mul_factorial hjk)
  push_cast at h
  have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hj : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hkj : ((k - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [div_eq_div_iff hk (mul_ne_zero hj hkj), one_mul, ← h]
  ring

theorem expSeriesAdd : ExpAdd := by
  intro K _ _ σ a b ha hb
  classical
  ext m
  have hN : m.degree < m.degree + 1 := Nat.lt_succ_self _
  set N := m.degree + 1 with hNdef
  have hab : constantCoeff (a + b) = 0 := by simp [ha, hb]
  have hmid : ∀ F : ℕ → ℕ → K,
      ∑ k ∈ range N, ∑ j ∈ range (k + 1), F j (k - j) =
        ∑ j ∈ range N, ∑ j' ∈ range (N - j), F j j' := by
    intro F
    rw [Finset.sum_comm' (t' := range N) (s' := fun j => Ico j N)]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      congr 1
      omega
    · intro k j
      simp only [mem_range, mem_Ico]
      omega
  calc coeff m (mvExp (a + b))
      = ∑ k ∈ range N, coeff m ((a + b) ^ k) / (k.factorial : K) := thmPExp_coeff_mvExp hab m hN
    _ = ∑ k ∈ range N, ∑ j ∈ range (k + 1),
          coeff m (a ^ j * b ^ (k - j)) / ((j.factorial : K) * ((k - j).factorial : K)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)

        rw [add_pow, map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [mem_range] at hj
        rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)), coeff_mul_C, mul_div_assoc,
          thmPExp_choose_div_factorial (by omega), mul_one_div]
    _ = ∑ j ∈ range N, ∑ j' ∈ range (N - j),
          coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)) :=
        hmid (fun j j' => coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)))
    _ = ∑ j ∈ range N, ∑ j' ∈ range N,
          coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        apply Finset.sum_subset (range_subset_range.2 (by omega))
        intro j' _ hj'
        simp only [mem_range, not_lt] at hj'
        rw [thmPExp_coeff_pow_mul_pow_eq_zero ha hb (by omega), zero_div]
    _ = ∑ pq ∈ antidiagonal m, coeff pq.1 (mvExp a) * coeff pq.2 (mvExp b) := by
        symm
        calc ∑ pq ∈ antidiagonal m, coeff pq.1 (mvExp a) * coeff pq.2 (mvExp b)
            = ∑ pq ∈ antidiagonal m, ∑ j ∈ range N, ∑ j' ∈ range N,
                (coeff pq.1 (a ^ j) / (j.factorial : K)) *
                  (coeff pq.2 (b ^ j') / (j'.factorial : K)) := by
              refine Finset.sum_congr rfl (fun pq hpq => ?_)
              rw [thmPExp_coeff_mvExp ha pq.1 (N := N)
                  (by have := (thmPExp_degree_le_of_mem_antidiagonal hpq).1; omega),
                thmPExp_coeff_mvExp hb pq.2 (N := N)
                  (by have := (thmPExp_degree_le_of_mem_antidiagonal hpq).2; omega),
                Finset.sum_mul_sum]
          _ = ∑ j ∈ range N, ∑ pq ∈ antidiagonal m, ∑ j' ∈ range N,
                (coeff pq.1 (a ^ j) / (j.factorial : K)) *
                  (coeff pq.2 (b ^ j') / (j'.factorial : K)) := Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun j' _ => ?_)
              rw [coeff_mul, Finset.sum_div]
              refine Finset.sum_congr rfl (fun pq _ => ?_)
              rw [div_mul_div_comm]
    _ = coeff m (mvExp a * mvExp b) := (coeff_mul _ _ _).symm

end Formalism.IncomingBounds
end
end
