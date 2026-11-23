module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle004
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def thrStar (ε : Fin n → Bool) : ℝ :=
  max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem lfa_mul_of_not_disjoint (s t : Finset (Fin (n * n))) (h : ¬ Disjoint s t) :
    fockBasis n s * fockBasis n t = 0 := by
  exact ExteriorAlgebra.basis_mul_of_not_disjoint _ (Set.powersetCard.ofCard (rfl : s.card = s.card))
    (Set.powersetCard.ofCard (rfl : t.card = t.card)) h

theorem eq_sign_smul_of_intUnit {A : Type*} [AddCommGroup A] [Module ℂ A] (u : ℤˣ) (x y : A) (h : x = u • y) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ x = σ • y := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simpa using h⟩
  · exact ⟨-1, Or.inr rfl, by simpa using h⟩

theorem lfa_mul_of_disjoint (s t : Finset (Fin (n * n))) (h : Disjoint s t) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ fockBasis n s * fockBasis n t = σ • fockBasis n (s ∪ t) := by
  have hm := ExteriorAlgebra.basis_mul_of_disjoint ((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv)
    (Set.powersetCard.ofCard (rfl : s.card = s.card)) (Set.powersetCard.ofCard (rfl : t.card = t.card)) h
  obtain ⟨σ, hσ, h'⟩ := eq_sign_smul_of_intUnit _ _ _ hm
  refine ⟨σ, hσ, h'.trans ?_⟩
  exact congrArg (fun U => σ • fockBasis n U) (Finset.disjUnion_eq_union s t h)

theorem lfa_basis_list (S : Finset (Fin (n * n))) :
    fockBasis n S = ((List.ofFn fun i => finProdFinEquiv.symm (S.orderEmbOfFin rfl i)).map
      fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod := by
  rw [fockBasis, ExteriorAlgebra.basis_apply_ofCard _ (rfl : S.card = S.card), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
  congr 2
  funext i
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply]

theorem lf_basis_singleton (x : Fin n × Fin n) :
    fockBasis n {finProdFinEquiv x} = ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ)) := by
  rw [fockBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton _), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.val_ofCard]

theorem lfa_cp_apply (x : Fin n × Fin n) (v : Fock n) :
    cpFock x.1 x.2 v = fockBasis n {finProdFinEquiv x} * v := by
  rw [lf_basis_singleton]
  rfl

theorem lfa_cm_list (x : Fin n × Fin n) (l : List (Fin n × Fin n)) (hx : x ∉ l) :
    cmFock x.1 x.2 (l.map fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod = 0 := by
  induction l with
  | nil => simp [cmFock]
  | cons y l ih =>
    rw [List.mem_cons, not_or] at hx
    have ih' := ih hx.2
    simp only [cmFock] at ih' ⊢
    rw [List.map_cons, List.prod_cons, CliffordAlgebra.contractLeft_ι_mul, ih']
    simp [hx.1]

theorem lf_cp_basis_of_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∈ S) :
    cpFock x.1 x.2 (fockBasis n S) = 0 := by
  rw [lfa_cp_apply]
  exact lfa_mul_of_not_disjoint _ _ (Finset.not_disjoint_iff.mpr ⟨_, Finset.mem_singleton_self _, hx⟩)

theorem lf_cm_basis_of_not_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∉ S) :
    cmFock x.1 x.2 (fockBasis n S) = 0 := by
  rw [lfa_basis_list]
  apply lfa_cm_list
  intro hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  apply hx
  rw [← hi, Equiv.apply_symm_apply]
  exact Finset.orderEmbOfFin_mem S rfl i

theorem lf_cp_cm_basis {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∉ S) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      cpFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (insert (finProdFinEquiv x) S) ∧
      cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S)) = σ • fockBasis n S := by
  obtain ⟨σ, hσ, h⟩ := lfa_mul_of_disjoint {finProdFinEquiv x} S (Finset.disjoint_singleton_left.mpr hx)
  rw [← Finset.insert_eq] at h
  have hcp : cpFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (insert (finProdFinEquiv x) S) := by
    rw [lfa_cp_apply, h]
  have hcmcp : cmFock x.1 x.2 (cpFock x.1 x.2 (fockBasis n S)) = fockBasis n S := by
    have h0 := lf_cm_basis_of_not_mem hx
    simp only [cpFock, cmFock, LinearMap.mulLeft_apply] at h0 ⊢
    rw [CliffordAlgebra.contractLeft_ι_mul, h0]
    simp
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨σ, hσ, hcp, ?_⟩
  rw [hcp, map_smul] at hcmcp
  calc cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S))
      = (σ * σ) • cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S)) := by rw [hσσ, one_smul]
    _ = σ • fockBasis n S := by rw [← smul_smul, hcmcp]

theorem lf_cm_basis_of_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∈ S) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      cmFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (S.erase (finProdFinEquiv x)) ∧
      cpFock x.1 x.2 (fockBasis n (S.erase (finProdFinEquiv x))) = σ • fockBasis n S := by
  obtain ⟨σ, hσ, h1, h2⟩ := lf_cp_cm_basis (Finset.notMem_erase (finProdFinEquiv x) S)
  rw [Finset.insert_erase hx] at h1 h2
  exact ⟨σ, hσ, h2, h1⟩

theorem lf_num_basis (x : Fin n × Fin n) (S : Finset (Fin (n * n))) :
    cpFock x.1 x.2 (cmFock x.1 x.2 (fockBasis n S)) =
      if finProdFinEquiv x ∈ S then fockBasis n S else 0 := by
  split_ifs with hx
  · obtain ⟨σ, hσ, h1, h2⟩ := lf_cm_basis_of_mem hx
    rw [h1, map_smul, h2, smul_smul]
    rcases hσ with rfl | rfl <;> norm_num
  · rw [lf_cm_basis_of_not_mem hx, map_zero]

theorem lf_repr_cm_eq (x : Fin n × Fin n) (S T : Finset (Fin (n * n))) :
    (fockBasis n).repr (cmFock x.1 x.2 (fockBasis n S)) T =
      (fockBasis n).repr (cpFock x.1 x.2 (fockBasis n T)) S := by
  by_cases hT : finProdFinEquiv x ∈ T
  · rw [lf_cp_basis_of_mem hT, map_zero, Finsupp.zero_apply]
    by_cases hS : finProdFinEquiv x ∈ S
    · obtain ⟨σ, -, h1, -⟩ := lf_cm_basis_of_mem hS
      rw [h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
      intro h
      rw [← h] at hT
      exact Finset.notMem_erase _ _ hT
    · rw [lf_cm_basis_of_not_mem hS, map_zero, Finsupp.zero_apply]
  · obtain ⟨τ, -, h1, h2⟩ := lf_cp_cm_basis hT
    rw [h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hST : insert (finProdFinEquiv x) T = S
    · subst hST
      rw [if_pos rfl, h2, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl]
    · rw [if_neg hST, smul_zero]
      by_cases hS : finProdFinEquiv x ∈ S
      · obtain ⟨σ, -, h3, -⟩ := lf_cm_basis_of_mem hS
        rw [h3, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
        intro h
        apply hST
        rw [← h, Finset.insert_erase hS]
      · rw [lf_cm_basis_of_not_mem hS, map_zero, Finsupp.zero_apply]

theorem lf_repr_cp_star (x : Fin n × Fin n) (S T : Finset (Fin (n * n))) :
    star ((fockBasis n).repr (cpFock x.1 x.2 (fockBasis n S)) T) =
      (fockBasis n).repr (cpFock x.1 x.2 (fockBasis n S)) T := by
  by_cases hS : finProdFinEquiv x ∈ S
  · rw [lf_cp_basis_of_mem hS]
    simp
  · obtain ⟨τ, hτ, h1, -⟩ := lf_cp_cm_basis hS
    rw [h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> rcases hτ with rfl | rfl <;> simp

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def resid (a : Fin n → ℂ) (s : Fin n) : ℂ := ∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')

def ratioV (μ : Fin n → ℝ) (s : Fin n) : ℝ := ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')

def ratioVd (μ : Fin n → ℝ) (s : Fin n) : ℝ := ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s')

theorem prod_one_add_eq_of_resolvent {ι : Type} [DecidableEq ι] (S : Finset ι) :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (a : ι → ℂ) (_ : Set.InjOn a S) (g : ι → R)
      (_ : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (a t - a s) • (g t * g s) = g t - g s),
      ∏ s ∈ S, (1 + g s) =
        1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s := by
  refine Finset.induction_on S ?_ ?_
  · intro R _ _ a _ g _
    simp
  · intro t S ht ih R _ _ a ha g hg
    have hinj : ∀ x ∈ insert t S, ∀ y ∈ insert t S, a x = a y → x = y :=
      fun x hx y hy h => ha (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h
    have haS : Set.InjOn a ↑S := fun x hx y hy h =>
      hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) h
    have hne : ∀ s ∈ S, a t - a s ≠ 0 := fun s hs h =>
      ht ((hinj t (Finset.mem_insert_self t S) s (Finset.mem_insert_of_mem hs) (sub_eq_zero.mp h)) ▸ hs)
    have hgS : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → (a s' - a s) • (g s' * g s) = g s' - g s :=
      fun s hs s' hs' h => hg s (Finset.mem_insert_of_mem hs) s' (Finset.mem_insert_of_mem hs') h
    have hC : ∏ s ∈ S, (1 + 1 / (a t - a s)) = 1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • (1 / (a t - a s)) :=
      ih ℂ a haS (fun s => 1 / (a t - a s)) (fun s hs s' hs' _ => by
        have h1 := hne s hs
        have h2 := hne s' hs'
        simp only [smul_eq_mul]
        field_simp
        ring)
    have hR := ih R a haS g hgS
    have hts : ∀ s ∈ S, g t * g s = (1 / (a t - a s)) • (g t - g s) := by
      intro s hs
      have h' := hg s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_self t S) (fun h => ht (h ▸ hs))
      rw [← h', smul_smul, one_div, inv_mul_cancel₀ (hne s hs), one_smul]
    have hcs : ∀ s ∈ S, (∏ s' ∈ (insert t S).erase s, (a s - a s' + 1) / (a s - a s')) =
        (a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) := by
      intro s hs
      have hst : t ≠ s := fun h => ht (h ▸ hs)
      rw [Finset.erase_insert_of_ne hst, Finset.prod_insert (fun h => ht (Finset.mem_of_mem_erase h))]
    have hct : ∏ s' ∈ S, (a t - a s' + 1) / (a t - a s') =
        1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s)) := by
      calc ∏ s' ∈ S, (a t - a s' + 1) / (a t - a s') = ∏ s ∈ S, (1 + 1 / (a t - a s)) :=
            Finset.prod_congr rfl fun s hs => by
              have := hne s hs
              field_simp
        _ = _ := by rw [hC]; simp only [smul_eq_mul]
    have hper : ∀ s ∈ S, ((a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s'))) • g s =
        (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s - ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g s := by
      intro s hs
      rw [← sub_smul]
      congr 1
      have h1 := hne s hs
      have h2 : a s - a t ≠ 0 := fun h => h1 (by linear_combination -h)
      field_simp
      ring
    have hmul : ∀ s ∈ S, g t * ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s) =
        ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g t - ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g s := by
      intro s hs
      rw [mul_smul_comm, hts s hs, smul_smul, smul_sub]
    have hsum2 : ∑ s ∈ S, (∏ s' ∈ (insert t S).erase s, (a s - a s' + 1) / (a s - a s')) • g s =
        ∑ s ∈ S, ((a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s'))) • g s :=
      Finset.sum_congr rfl fun s hs => by rw [hcs s hs]
    rw [Finset.prod_insert ht, hR, Finset.sum_insert ht, Finset.erase_insert ht, hsum2, hct, Finset.sum_congr rfl hper, add_mul,
      one_mul, mul_add, mul_one, Finset.mul_sum, Finset.sum_congr rfl hmul, add_smul, one_smul,
      Finset.sum_smul]
    simp only [Finset.sum_sub_distrib]
    abel

theorem inv_one_sub_C_mul_X (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X)⁻¹ = PowerSeries.mk (fun k => c ^ k) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, mul_comm (PowerSeries.mk _) (PowerSeries.C c), mul_assoc]
  cases n with
  | zero => simp
  | succ n =>
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), pow_succ]
    ring

theorem resSeries_eq_sum {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) :
    resSeries a = ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) •
      (PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) := by
  have hP : ∀ s, PowerSeries.constantCoeff (1 - PowerSeries.C (a s) * PowerSeries.X) ≠ 0 := by
    intro s; simp
  have h := prod_one_add_eq_of_resolvent (Finset.univ : Finset (Fin n)) (PowerSeries ℂ) a ha.injOn
    (fun s => PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) (fun s _ t _ _ => by
      have key : (1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹ - (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹ =
          (1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹ * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹ *
            ((1 - PowerSeries.C (a s) * PowerSeries.X) - (1 - PowerSeries.C (a t) * PowerSeries.X)) := by
        rw [mul_sub, mul_assoc, PowerSeries.inv_mul_cancel _ (hP s), mul_one,
          mul_comm ((1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹), mul_assoc,
          PowerSeries.inv_mul_cancel _ (hP t), mul_one]
      rw [← mul_sub, key, PowerSeries.smul_eq_C_mul, map_sub]
      ring)
  rw [resSeries, h, add_sub_cancel_left]

theorem resSeries_coeff_succ' {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) =
      ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) * a s ^ k := by

  rw [resSeries_eq_sum ha, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [PowerSeries.coeff_smul, inv_one_sub_C_mul_X, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
    smul_eq_mul]

theorem not_injective_shift_iff {μ ν : Fin n → ℝ} (hμ : Function.Injective μ) (s : Fin n) (c : ℝ)
    (hs : ν s = μ s + c) (ho : ∀ x, x ≠ s → ν x = μ x) :
    ¬ Function.Injective ν ↔ ∃ s' ∈ univ.erase s, μ s + c = μ s' := by
  constructor
  · intro h
    simp only [Function.Injective, not_forall] at h
    obtain ⟨x, y, hxy, hne⟩ := h
    by_cases hx : x = s
    · subst hx
      refine ⟨y, by simp [Ne.symm hne], ?_⟩
      rw [← hs, hxy, ho y (Ne.symm hne)]
    · by_cases hy : y = s
      · subst hy
        refine ⟨x, by simp [hx], ?_⟩
        rw [← hs, ← hxy, ho x hx]
      · exact absurd (hμ (by rw [← ho x hx, ← ho y hy, hxy])) hne
  · rintro ⟨s', hs', h⟩ hinj
    have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
    exact hne (hinj (by rw [ho s' hne, hs, h]))

theorem resSeries_coeff_succ {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) = ∑ s, resid a s * a s ^ k := by
  rw [resSeries_coeff_succ' ha k]
  rfl

theorem resid_poleV (μ : Fin n → ℝ) (s : Fin n) : resid (poleV μ) s = ((ratioV μ s : ℝ) : ℂ) := by
  simp only [resid, ratioV, poleV]
  push_cast
  refine Finset.prod_congr rfl fun s' _ => ?_
  ring

theorem resid_poleVd (μ : Fin n → ℝ) (s : Fin n) : resid (poleVd μ) s = ((ratioVd μ s : ℝ) : ℂ) := by
  simp only [resid, ratioVd, poleVd]
  push_cast
  refine Finset.prod_congr rfl fun s' _ => ?_
  rw [← neg_div_neg_eq]
  ring

theorem poleV_injective {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleV μ) := by
  intro x y h
  apply hμ
  simp only [poleV] at h
  have h' := Complex.ofReal_injective h
  linarith

theorem poleVd_injective {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleVd μ) := by
  intro x y h
  apply hμ
  simp only [poleVd] at h
  have h' := Complex.ofReal_injective h
  linarith

theorem ratioVd_add_single_mul {μ : Fin n → ℝ} (s : Fin n) (hμ : Function.Injective μ)
    (hμs : Function.Injective (μ + Pi.single s 1)) :
    ratioVd (μ + Pi.single s 1) s * ratioV μ s = 1 := by
  rw [ratioVd, ratioV, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro s' hs'
  have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
  have h1 : μ s - μ s' ≠ 0 := sub_ne_zero.mpr (fun h => hne (hμ h).symm)
  have h2 : μ s + 1 - μ s' ≠ 0 := by
    intro h
    apply hne
    apply hμs
    simp [Pi.single_apply, hne]
    linarith
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_apply, hne, if_false, add_zero]
  rw [show μ s + 1 - 1 - μ s' = μ s - μ s' by ring]
  field_simp

end ReciprocityTheory.ChartRestriction.DS
end
end
