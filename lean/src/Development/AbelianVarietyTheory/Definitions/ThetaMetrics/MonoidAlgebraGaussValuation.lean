import Mathlib

namespace GlobalTheory

noncomputable section

open scoped NNReal TensorProduct

section CoeffSup

variable {ι M Γ₀ : Type*} [Zero M] [LinearOrderedCommMonoidWithZero Γ₀]

def coeffSup (N : M → Γ₀) (c : ι →₀ M) : Γ₀ := c.support.sup fun i => N (c i)

variable {N : M → Γ₀}

@[simp] theorem coeffSup_zero : coeffSup N (0 : ι →₀ M) = 0 := by
  simp [coeffSup, bot_eq_zero]

theorem coeffSup_le_iff (h0 : N 0 = 0) {c : ι →₀ M} {γ : Γ₀} :
    coeffSup N c ≤ γ ↔ ∀ i, N (c i) ≤ γ := by
  rw [coeffSup, Finset.sup_le_iff]
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : i ∈ c.support
  · exact h i hi
  · rw [Finsupp.notMem_support_iff.mp hi, h0]; exact zero_le

theorem coeffSup_lt_iff (h0 : N 0 = 0) {c : ι →₀ M} {γ : Γ₀} (hγ : γ ≠ 0) :
    coeffSup N c < γ ↔ ∀ i, N (c i) < γ := by
  have hγ' : (⊥ : Γ₀) < γ := by rw [bot_eq_zero]; exact zero_lt_iff.mpr hγ
  rw [coeffSup, Finset.sup_lt_iff hγ']
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : i ∈ c.support
  · exact h i hi
  · rw [Finsupp.notMem_support_iff.mp hi, h0]; exact zero_lt_iff.mpr hγ

theorem le_coeffSup (h0 : N 0 = 0) (c : ι →₀ M) (i : ι) : N (c i) ≤ coeffSup N c :=
  (coeffSup_le_iff h0).mp le_rfl i

theorem exists_mem_support_coeffSup_eq {c : ι →₀ M} (hc : c ≠ 0) :
    ∃ i ∈ c.support, coeffSup N c = N (c i) :=
  Finset.exists_mem_eq_sup _ (Finsupp.support_nonempty_iff.mpr hc) _

theorem exists_coeffSup_eq [Nonempty ι] (h0 : N 0 = 0) (c : ι →₀ M) :
    ∃ i, coeffSup N c = N (c i) := by
  by_cases hc : c = 0
  · exact ⟨Classical.arbitrary ι, by simp [hc, h0]⟩
  · obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := N) hc
    exact ⟨i, hi⟩

theorem coeffSup_eq_zero_iff (h0 : N 0 = 0) {c : ι →₀ M} :
    coeffSup N c = 0 ↔ ∀ i, N (c i) = 0 := by
  simp only [← le_zero_iff, coeffSup_le_iff h0]

theorem coeffSup_single (h0 : N 0 = 0) (i : ι) (a : M) :
    coeffSup N (Finsupp.single i a) = N a := by
  classical
  refine le_antisymm ((coeffSup_le_iff h0).mpr fun j => ?_) ?_
  · rw [Finsupp.single_apply]; split_ifs
    · exact le_rfl
    · rw [h0]; exact zero_le
  · simpa using le_coeffSup h0 (Finsupp.single i a) i

theorem coeffSup_eq_sup_univ [Fintype ι] (h0 : N 0 = 0) (c : ι →₀ M) :
    coeffSup N c = Finset.univ.sup fun i => N (c i) :=
  eq_of_forall_ge_iff fun γ => by simp [coeffSup_le_iff h0]

theorem coeffSup_eq_mul_of_forall (h0 : N 0 = 0) {M' : Type*} [Zero M'] {N' : M' → Γ₀}
    (h0' : N' 0 = 0) {c : ι →₀ M} {c' : ι →₀ M'} {γ : Γ₀} (h : ∀ i, N' (c' i) = γ * N (c i)) :
    coeffSup N' c' = γ * coeffSup N c := by
  refine le_antisymm ((coeffSup_le_iff h0').mpr fun i => ?_) ?_
  · rw [h i]; exact mul_le_mul_right (le_coeffSup h0 c i) γ
  · by_cases hc : c = 0
    · simp [hc]
    · obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := N) hc
      rw [hi, ← h i]; exact le_coeffSup h0' c' i

end CoeffSup

section MonoidAlgebra

variable {R G Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

theorem coeffSup_coeff_mul_le [Add G] (f g : AddMonoidAlgebra R G) :
    coeffSup v (f * g).coeff ≤ coeffSup v f.coeff * coeffSup v g.coeff := by
  classical
  refine (coeffSup_le_iff v.map_zero).mpr fun m => ?_
  rw [AddMonoidAlgebra.coeff_mul]
  refine v.map_sum_le fun a _ => v.map_sum_le fun b _ => ?_
  dsimp only
  split_ifs
  · rw [v.map_mul]
    exact mul_le_mul' (le_coeffSup v.map_zero _ _) (le_coeffSup v.map_zero _ _)
  · rw [v.map_zero]; exact zero_le

theorem coeffSup_coeff_mul [Add G] [UniqueSums G] (f g : AddMonoidAlgebra R G) :
    coeffSup v (f * g).coeff = coeffSup v f.coeff * coeffSup v g.coeff := by
  classical
  refine le_antisymm (coeffSup_coeff_mul_le v f g) ?_
  by_cases hf : coeffSup v f.coeff = 0
  · simp [hf]
  by_cases hg : coeffSup v g.coeff = 0
  · simp [hg]
  have hf' : f.coeff ≠ 0 := fun h => hf (by simp [h])
  have hg' : g.coeff ≠ 0 := fun h => hg (by simp [h])
  obtain ⟨a, ha, ha'⟩ := exists_mem_support_coeffSup_eq (N := v) hf'
  obtain ⟨b, hb, hb'⟩ := exists_mem_support_coeffSup_eq (N := v) hg'
  obtain ⟨a₀, ha₀, b₀, hb₀, hu⟩ := UniqueSums.uniqueAdd_of_nonempty
    (A := f.coeff.support.filter fun x => v (f.coeff x) = coeffSup v f.coeff)
    (B := g.coeff.support.filter fun x => v (g.coeff x) = coeffSup v g.coeff)
    ⟨a, Finset.mem_filter.mpr ⟨ha, ha'.symm⟩⟩ ⟨b, Finset.mem_filter.mpr ⟨hb, hb'.symm⟩⟩
  obtain ⟨ha₁, ha₂⟩ := Finset.mem_filter.mp ha₀
  obtain ⟨hb₁, hb₂⟩ := Finset.mem_filter.mp hb₀
  refine le_trans (le_of_eq ?_) (le_coeffSup v.map_zero _ (a₀ + b₀))
  have hpos : 0 < coeffSup v f.coeff * coeffSup v g.coeff := zero_lt_iff.mpr (mul_ne_zero hf hg)
  rw [AddMonoidAlgebra.coeff_mul]
  simp_rw [Finsupp.sum]
  rw [← Finset.sum_product', v.map_sum_eq_of_lt (j := (a₀, b₀))
    (Finset.mem_product.mpr ⟨ha₁, hb₁⟩)]
  · simp [ha₂, hb₂]
  · intro p hp
    obtain ⟨hp, hne⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_singleton] at hne
    simp only [if_true, map_mul, ha₂, hb₂]
    split_ifs with he
    · rw [map_mul]
      have h₁ := le_coeffSup v.map_zero f.coeff p.1
      have h₂ := le_coeffSup v.map_zero g.coeff p.2
      rcases h₁.eq_or_lt with h₁ | h₁
      · rcases h₂.eq_or_lt with h₂ | h₂
        · have := hu (Finset.mem_filter.mpr ⟨hp₁, h₁⟩) (Finset.mem_filter.mpr ⟨hp₂, h₂⟩) he
          exact absurd (Prod.ext this.1 this.2) hne
        · rw [h₁]; exact mul_lt_mul_of_pos_left h₂ (zero_lt_iff.mpr hf)
      · exact lt_of_le_of_lt (mul_le_mul_right h₂ _)
          (mul_lt_mul_of_pos_right h₁ (zero_lt_iff.mpr hg))
    · rw [map_zero]; exact hpos

variable [AddMonoid G] [UniqueSums G]

def gaussValAlg : Valuation (AddMonoidAlgebra R G) Γ₀ where
  toFun f := coeffSup v f.coeff
  map_zero' := by simp
  map_one' := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, coeffSup_single v.map_zero,
      v.map_one]
  map_mul' := coeffSup_coeff_mul v
  map_add_le_max' f g := (coeffSup_le_iff v.map_zero).mpr fun m => by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (v.map_add _ _).trans
      (max_le_max (le_coeffSup v.map_zero _ _) (le_coeffSup v.map_zero _ _))

theorem gaussValAlg_apply (f : AddMonoidAlgebra R G) :
    gaussValAlg v f = f.coeff.support.sup fun m => v (f.coeff m) := rfl

theorem gaussValAlg_le_iff {f : AddMonoidAlgebra R G} {γ : Γ₀} :
    gaussValAlg v f ≤ γ ↔ ∀ m, v (f.coeff m) ≤ γ := coeffSup_le_iff v.map_zero

@[simp] theorem gaussValAlg_single (m : G) (a : R) :
    gaussValAlg v (AddMonoidAlgebra.single m a) = v a :=
  coeffSup_single v.map_zero m a

theorem exists_gaussValAlg_eq (f : AddMonoidAlgebra R G) :
    ∃ m, gaussValAlg v f = v (f.coeff m) :=
  haveI : Nonempty G := ⟨0⟩
  exists_coeffSup_eq v.map_zero f.coeff

theorem gaussValAlg_eq_zero_iff {f : AddMonoidAlgebra R G} :
    gaussValAlg v f = 0 ↔ ∀ m, v (f.coeff m) = 0 := coeffSup_eq_zero_iff v.map_zero

end MonoidAlgebra

end

end GlobalTheory
