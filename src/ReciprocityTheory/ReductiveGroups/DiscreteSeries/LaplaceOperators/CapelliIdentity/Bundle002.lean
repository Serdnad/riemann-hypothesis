module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ColAnti
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

section Ring

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem capelliC_central (hE : GlRelR E) (x : ℂ) (a b : Fin n) : Commute (E a b) (capelliC E x) := by
  have h := cminor_comm E hE a b (id : Fin n → Fin n) id x
  simp only [id, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  by_cases hab : a = b
  · subst hab
    rw [show Function.update (id : Fin n → Fin n) a a = id from Function.update_eq_self a id, sub_self] at h
    exact sub_eq_zero.1 h
  · have h1 : cminor E (Function.update (id : Fin n → Fin n) b a) id x = 0 := by
      apply cminor_rows_not_inj
      intro hinj
      have : Function.update (id : Fin n → Fin n) b a b = Function.update (id : Fin n → Fin n) b a a := by
        simp [Function.update_of_ne hab]
      exact hab (hinj this).symm
    have h2 : cminor E id (Function.update (id : Fin n → Fin n) a b) x = 0 := by
      apply cminor_cols_not_inj E hE
      intro hinj
      have : Function.update (id : Fin n → Fin n) a b a = Function.update (id : Fin n → Fin n) a b b := by
        simp [Function.update_of_ne (Ne.symm hab)]
      exact hab (hinj this)
    rw [h1, h2, sub_self] at h
    exact sub_eq_zero.1 h

end Ring

section Module

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M)

theorem capEntry_apply_end (x : ℂ) (a b : Fin n) (v : M) :
    capEntry E x a b v = E a b v + if a = b then x • v else 0 := by
  unfold capEntry
  split_ifs <;> simp [Module.algebraMap_end_apply]

theorem prod_ofFn_apply_highestWeight (μ : Fin n → ℂ) (v : M) (x : ℂ) (hup : ∀ a b, a < b → E a b v = 0)
    (hd : ∀ a, E a a v = μ a • v) :
    ∀ (p : ℕ) (r c : Fin p → Fin n), Function.Injective r → (∀ j, (r j : ℕ) < p) →
      (∀ j, (c j : ℕ) = j) →
      (List.ofFn fun j : Fin p => capEntry E (x - ((j : ℕ) : ℂ)) (r j) (c j)).prod v =
        if (∀ j, (r j : ℕ) = j) then (∏ j : Fin p, (x + μ (c j) - ((j : ℕ) : ℂ))) • v else 0 := by
  intro p
  induction p with
  | zero =>
    intro r c _ _ _
    simp
  | succ p ih =>
    intro r c hr hrp hc
    rw [List.ofFn_succ', List.prod_concat, Module.End.mul_apply]
    have hcl : (c (Fin.last p) : ℕ) = p := by rw [hc]; simp
    have hrl : (r (Fin.last p) : ℕ) ≤ p := by have := hrp (Fin.last p); omega
    rcases lt_or_eq_of_le hrl with hlt | heq
    · have hlt' : r (Fin.last p) < c (Fin.last p) := by
        rw [Fin.lt_iff_val_lt_val, hcl]; exact hlt
      rw [capEntry_apply_end, hup _ _ hlt', if_neg (ne_of_lt hlt'), add_zero, map_zero]
      rw [if_neg]
      intro hall
      have := hall (Fin.last p)
      simp only [Fin.val_last] at this
      omega
    · have heq' : r (Fin.last p) = c (Fin.last p) := Fin.ext (by rw [heq, hcl])
      rw [capEntry_apply_end, if_pos heq', heq', hd, ← add_smul, map_smul]
      have hr' : Function.Injective (fun j : Fin p => r j.castSucc) :=
        hr.comp (Fin.castSucc_injective p)
      have hrp' : ∀ j : Fin p, (r j.castSucc : ℕ) < p := by
        intro j
        have h1 := hrp j.castSucc
        have h2 : r j.castSucc ≠ r (Fin.last p) := fun h => (Fin.castSucc_lt_last j).ne (hr h)
        have h3 : (r j.castSucc : ℕ) ≠ p := fun h => h2 (Fin.ext (by rw [h, heq]))
        omega
      have hc' : ∀ j : Fin p, (c j.castSucc : ℕ) = j := fun j => by rw [hc]; simp
      have key := ih (fun j => r j.castSucc) (fun j => c j.castSucc) hr' hrp' hc'
      simp only [Fin.coe_castSucc] at key ⊢
      rw [key]
      have hiff : (∀ j : Fin (p + 1), (r j : ℕ) = j) ↔ (∀ j : Fin p, (r j.castSucc : ℕ) = j) := by
        constructor
        · intro h j; simpa using h j.castSucc
        · intro h j
          rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
          · simpa using h i
          · simpa using heq
      by_cases hall : ∀ j : Fin p, (r j.castSucc : ℕ) = j
      · rw [if_pos hall, if_pos (hiff.2 hall), smul_smul, Fin.prod_univ_castSucc]
        congr 1
        simp only [Fin.coe_castSucc, Fin.val_last, hcl]
        ring
      · rw [if_neg hall, if_neg (fun h => hall (hiff.1 h)), smul_zero]

theorem capelliC_hw (μ : Fin n → ℂ) (v : M) (x : ℂ) (hup : ∀ a b, a < b → E a b v = 0)
    (hd : ∀ a, E a a v = μ a • v) :
    capelliC E x v = (∏ a : Fin n, (x + μ a - ((a : ℕ) : ℂ))) • v := by
  unfold capelliC cminor
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [LinearMap.smul_apply]
    have := prod_ofFn_apply_highestWeight E μ v x hup hd n (fun j => (1 : Equiv.Perm (Fin n)) j) id
      (Equiv.injective _) (fun j => by simp) (fun j => rfl)
    simp only [id] at this ⊢
    rw [this, if_pos (fun j => by simp)]
    simp
  · intro σ _ hσ
    rw [LinearMap.smul_apply]
    have := prod_ofFn_apply_highestWeight E μ v x hup hd n (fun j => σ j) id
      (Equiv.injective _) (fun j => (σ j).2) (fun j => rfl)
    simp only [id] at this ⊢
    rw [this, if_neg, smul_zero]
    intro hall
    apply hσ
    ext j
    simpa using hall j
  · intro h; exact absurd (Finset.mem_univ _) h

theorem capelliC_genSub (hE : IsGlRep E) (μ : Fin n → ℝ) (v : M) (hv : IsHWVec E μ v) (x : ℂ) :
    ∀ y ∈ genSub E (Submodule.span ℂ {v}),
      capelliC E x y = (∏ a : Fin n, (x + (μ a : ℂ) - ((a : ℕ) : ℂ))) • y := by
  have hE' : GlRelR E := (isGlRep_iff_glRelR E).1 hE
  set c : ℂ := ∏ a : Fin n, (x + (μ a : ℂ) - ((a : ℕ) : ℂ)) with hc
  have hv' : capelliC E x v = c • v :=
    capelliC_hw E (fun a => (μ a : ℂ)) v x hv.2 hv.1
  let T : Submodule ℂ M := LinearMap.ker (capelliC E x - c • (1 : Module.End ℂ M))
  have hmem : ∀ w, w ∈ T ↔ capelliC E x w = c • w := by
    intro w
    simp only [T, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero]
  have hle : genSub E (Submodule.span ℂ {v}) ≤ T := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact (hmem v).2 hv'
    · intro a b w hw
      rw [hmem] at hw ⊢
      have hcomm := congrArg (fun f : Module.End ℂ M => f w) (capelliC_central E hE' x a b).eq
      simp only [Module.End.mul_apply] at hcomm
      rw [← hcomm, hw, map_smul]
  intro y hy
  exact (hmem y).1 (hle hy)

end Module

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

theorem exists_perm_swap_succAbove {p : ℕ} (i s : Fin (p + 1)) (h : i ≠ s) :
    ∃ π : Equiv.Perm (Fin p), ((Equiv.Perm.sign π : ℤˣ) : ℤ) = (-1) ^ ((i : ℕ) + (s : ℕ) + 1) ∧
      ∀ t, Equiv.swap i s (i.succAbove t) = s.succAbove (π t) := by
  classical
  have hsa : ∀ (j : Fin (p + 1)) (u : Fin p), j.succAbove u = j.cycleRange.symm u.succ := fun j u =>
    ((Equiv.symm_apply_eq _).mpr (Fin.cycleRange_succAbove j u).symm).symm
  let ρ : Equiv.Perm (Fin (p + 1)) := s.cycleRange * Equiv.swap i s * i.cycleRange.symm
  have hρapp : ∀ x, ρ x = s.cycleRange (Equiv.swap i s (i.cycleRange.symm x)) := fun x => rfl
  have hρ0 : ρ 0 = 0 := by
    rw [hρapp, Fin.cycleRange_symm_zero, Equiv.swap_apply_left, Fin.cycleRange_self]
  let π : Equiv.Perm (Fin p) := (Equiv.Perm.decomposeFin ρ).2
  have hdec : Equiv.Perm.decomposeFin.symm ((Equiv.Perm.decomposeFin ρ).1, π) = ρ :=
    Equiv.Perm.decomposeFin.symm_apply_apply ρ
  have h1 : (Equiv.Perm.decomposeFin ρ).1 = 0 := by
    have := congrArg (fun g : Equiv.Perm (Fin (p + 1)) => g 0) hdec
    simp only [Equiv.Perm.decomposeFin_symm_apply_zero] at this
    rw [this, hρ0]
  rw [h1] at hdec
  refine ⟨π, ?_, ?_⟩
  · have hs : Equiv.Perm.sign ρ = Equiv.Perm.sign π := by
      rw [← hdec, Equiv.Perm.decomposeFin.symm_sign]
      simp
    have hs2 : Equiv.Perm.sign ρ = (-1) ^ (s : ℕ) * (-1) * (-1) ^ (i : ℕ) := by
      simp only [ρ, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
        Equiv.Perm.sign_swap h]
    rw [← hs, hs2]
    push_cast
    ring
  · intro t
    have h2 : (π t).succ = ρ t.succ := by
      rw [← hdec, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    rw [hsa s, h2, hρapp, ← hsa i, Equiv.symm_apply_apply]

theorem update_comp_succAbove {α : Type*} {p : ℕ} (f : Fin (p + 1) → α) (i : Fin (p + 1)) (t : Fin p) :
    Function.update (f ∘ i.succAbove) t (f i) = f ∘ Equiv.swap i (i.succAbove t) ∘ i.succAbove := by
  funext u
  by_cases hu : u = t
  · subst hu
    simp
  · simp only [Function.update_apply, if_neg hu, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne i u)
      (fun h => hu (Fin.succAbove_right_injective h))]

theorem sum_sum_succAbove {M : Type*} [AddCommGroup M] {p : ℕ} (f : Fin (p + 1) → M) :
    ∑ i : Fin (p + 1), ∑ t : Fin p, f (i.succAbove t) = p • ∑ s, f s := by
  have h : ∀ i : Fin (p + 1), ∑ t : Fin p, f (i.succAbove t) = ∑ s, f s - f i := by
    intro i
    rw [Fin.sum_univ_succAbove f i]
    abel
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [succ_nsmul]
  abel

theorem neg_one_pow_row (a b c : ℕ) :
    (-1 : ℂ) ^ (a + b) * (-1 : ℂ) ^ (a + c + 1) = (-1 : ℂ) ^ (c + b + 1) := by
  rw [← pow_add, show a + b + (a + c + 1) = (c + b + 1) + 2 * a by ring, pow_add, pow_mul]
  simp

theorem neg_one_pow_col (a b c : ℕ) :
    (-1 : ℂ) ^ (a + b) * (-1 : ℂ) ^ (b + c + 1) = (-1 : ℂ) ^ (a + c + 1) := by
  rw [← pow_add, show a + b + (b + c + 1) = (a + c + 1) + 2 * b by ring, pow_add, pow_mul]
  simp

section Ring

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem cminor_update_row {p : ℕ} (R : Fin (p + 1) → Fin n) (C : Fin p → Fin n) (i : Fin (p + 1))
    (t : Fin p) (y : ℂ) :
    cminor E (Function.update (R ∘ i.succAbove) t (R i)) C y =
      ((-1 : ℂ) ^ ((i : ℕ) + (i.succAbove t : ℕ) + 1)) • cminor E (R ∘ (i.succAbove t).succAbove) C y := by
  obtain ⟨π, hπ, hmap⟩ := exists_perm_swap_succAbove i (i.succAbove t) (Fin.succAbove_ne i t).symm
  have hrows : Function.update (R ∘ i.succAbove) t (R i) = (R ∘ (i.succAbove t).succAbove) ∘ π := by
    rw [update_comp_succAbove]
    funext u
    simp [hmap]
  rw [hrows, cminor_perm_rows, hπ, ← Int.cast_smul_eq_zsmul ℂ]
  simp

theorem cminor_update_col (hE : GlRelR E) {p : ℕ} (R : Fin p → Fin n) (C : Fin (p + 1) → Fin n)
    (j : Fin (p + 1)) (t : Fin p) (y : ℂ) :
    cminor E R (Function.update (C ∘ j.succAbove) t (C j)) y =
      ((-1 : ℂ) ^ ((j : ℕ) + (j.succAbove t : ℕ) + 1)) • cminor E R (C ∘ (j.succAbove t).succAbove) y := by
  obtain ⟨π, hπ, hmap⟩ := exists_perm_swap_succAbove j (j.succAbove t) (Fin.succAbove_ne j t).symm
  have hcols : Function.update (C ∘ j.succAbove) t (C j) = (C ∘ (j.succAbove t).succAbove) ∘ π := by
    rw [update_comp_succAbove]
    funext u
    simp [hmap]
  rw [hcols, cminor_perm_cols E hE, hπ, ← Int.cast_smul_eq_zsmul ℂ]
  simp

theorem capEntry_comm_sub (a b : Fin n) (x : ℂ) (X : 𝒰) :
    capEntry E x a b * X - X * capEntry E x a b = E a b * X - X * E a b := by
  unfold capEntry
  split_ifs
  · rw [add_mul, mul_add, Algebra.commutes]
    abel
  · simp

def capT {p : ℕ} (R C : Fin (p + 1) → Fin n) (y : ℂ) (s j : Fin (p + 1)) : 𝒰 :=
  if R s = C j then ((-1 : ℂ) ^ ((s : ℕ) + (j : ℕ) + 1)) • cminor E (R ∘ s.succAbove) (C ∘ j.succAbove) y
  else 0

theorem comm_term (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (i j : Fin (p + 1)) (y : ℂ) :
    ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
        (E (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) y -
          cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) y * E (R i) (C j)) =
      ∑ t, capT E R C y (i.succAbove t) j - ∑ t, capT E R C y i (j.succAbove t) := by
  rw [cminor_comm (hE := hE) (a := R i) (b := C j) (R := R ∘ i.succAbove)
    (C := C ∘ j.succAbove) (x := y), smul_sub, Finset.smul_sum, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [capT, Function.comp_apply]
    split_ifs with h
    · rw [cminor_update_row, smul_smul, neg_one_pow_row]
    · exact smul_zero _
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [capT, Function.comp_apply]
    by_cases h : C (j.succAbove t) = R i
    · rw [if_pos h, if_pos h.symm, cminor_update_col E hE, smul_smul, neg_one_pow_col]
    · rw [if_neg h, if_neg (Ne.symm h), smul_zero]

end Ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem shiftedEntry_op (x : ℂ) (a b : Fin n) :
    capEntry (fun a b => MulOpposite.op (E b a)) x a b = MulOpposite.op (capEntry E x b a) := by
  unfold capEntry
  by_cases h : a = b
  · subst h
    simp [MulOpposite.algebraMap_apply]
  · have h' : b ≠ a := Ne.symm h
    simp [h, h']

private theorem list_ofFn_reverse_eq_ofFn_rev {α : Type*} {p : ℕ} (f : Fin p → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  congr 1
  ext
  simp only [Fin.val_rev]
  try simp only [List.length_reverse, List.length_ofFn] at h1 h2
  omega

theorem columnMinor_op_rev {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    cminor (fun a b => MulOpposite.op (E b a)) (C ∘ Fin.rev) (R ∘ Fin.rev) x =
      MulOpposite.op (rminor E R C x) := by
  have hop : ∀ g : Equiv.Perm (Fin p) → 𝒰,
      MulOpposite.op (∑ σ, g σ) = ∑ σ, MulOpposite.op (g σ) :=
    fun g => map_sum (MulOpposite.opAddEquiv : 𝒰 ≃+ 𝒰ᵐᵒᵖ) g _
  unfold cminor rminor
  rw [hop]
  refine Fintype.sum_equiv (MulAut.conj (Fin.revPerm (n := p))).toEquiv _ _ (fun σ => ?_)
  have hs : Equiv.Perm.sign (Fin.revPerm * σ * (Fin.revPerm (n := p))⁻¹) = Equiv.Perm.sign σ := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv,
      mul_comm (Equiv.Perm.sign (Fin.revPerm (n := p))), mul_assoc, Int.units_mul_self, mul_one]
  have hτ : ∀ j : Fin p, ((Fin.revPerm * σ * (Fin.revPerm (n := p))⁻¹ : Equiv.Perm (Fin p))) (Fin.rev j) = Fin.rev (σ j) := by
    intro j
    have h1 : (Fin.revPerm (n := p))⁻¹ (Fin.rev j) = j := by
      rw [Equiv.Perm.inv_eq_iff_eq, Fin.revPerm_apply]
    simp only [Equiv.Perm.mul_apply, h1, Fin.revPerm_apply]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hs,
    MulOpposite.op_smul]
  congr 1
  rw [MulOpposite.op_list_prod, List.map_ofFn, list_ofFn_reverse_eq_ofFn_rev]
  refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
  simp only [Function.comp_apply, hτ, shiftedEntry_op]
  congr 2
  rw [Fin.val_rev, Nat.cast_sub (by have := j.isLt; omega)]
  push_cast
  ring

theorem rowMinor_eq_unop {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    rminor E R C x = MulOpposite.unop
      (cminor (fun a b => MulOpposite.op (E b a)) (C ∘ Fin.rev) (R ∘ Fin.rev) x) := by
  rw [columnMinor_op_rev, MulOpposite.unop_op]

theorem neg_one_pow_add_rev {p : ℕ} (i j : Fin (p + 1)) :
    (-1 : ℂ) ^ ((j : ℕ) + ((Fin.rev i : Fin (p + 1)) : ℕ)) =
      (-1 : ℂ) ^ ((i : ℕ) + ((Fin.rev j : Fin (p + 1)) : ℕ)) := by
  rw [neg_one_pow_eq_pow_mod_two ((j : ℕ) + ((Fin.rev i : Fin (p + 1)) : ℕ)),
    neg_one_pow_eq_pow_mod_two ((i : ℕ) + ((Fin.rev j : Fin (p + 1)) : ℕ))]
  congr 1
  rw [Fin.val_rev, Fin.val_rev]
  have := i.isLt
  have := j.isLt
  omega

theorem rminor_row_at (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (i : Fin (p + 1)) (x : ℂ) :
    rminor E R C x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
      (rminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) * capEntry E x (R i) (C j)) := by
  have hunop : ∀ g : Fin (p + 1) → 𝒰ᵐᵒᵖ,
      MulOpposite.unop (∑ i, g i) = ∑ i, MulOpposite.unop (g i) :=
    fun g => map_sum (MulOpposite.opAddEquiv : 𝒰 ≃+ 𝒰ᵐᵒᵖ).symm g _
  rw [rowMinor_eq_unop, cminor_col_at (hE := glRelR_op (hE := hE)) _ _ _ (Fin.rev i), hunop]
  refine Fintype.sum_equiv (Fin.revPerm (n := p + 1)) _ _ (fun i' => ?_)
  have e1 : (C ∘ Fin.rev) ∘ i'.succAbove = (C ∘ (Fin.rev i').succAbove) ∘ Fin.rev := by
    funext k
    simp [Fin.rev_succAbove]
  have e2 : (R ∘ Fin.rev) ∘ (Fin.rev i).succAbove = (R ∘ i.succAbove) ∘ Fin.rev := by
    funext k
    simp [Fin.rev_succAbove]
  rw [MulOpposite.unop_smul, MulOpposite.unop_mul, e1, e2, columnMinor_op_rev, MulOpposite.unop_op]
  simp only [Function.comp_apply, shiftedEntry_op, MulOpposite.unop_op, Fin.rev_rev, Fin.revPerm_apply]
  rw [neg_one_pow_add_rev]

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end
