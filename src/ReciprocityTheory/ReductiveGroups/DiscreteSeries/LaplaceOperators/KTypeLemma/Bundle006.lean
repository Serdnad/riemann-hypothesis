module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  ext d
  simp only [tensV, prj, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.add_apply]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp_all

theorem vc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  ext d
  simp only [tensVd, prj, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.sub_apply]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp_all

theorem vc_tensV_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem vc_tensVd_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem vc_eeV_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeV E (Pi.single t m) e = E t e m := by
  simp [eeV, prj, Pi.single_apply, apply_ite]

theorem vc_eeVd_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeVd E (Pi.single t m) e = -E e t m := by
  simp [eeVd, prj, Pi.single_apply, apply_ite]

theorem vc_commV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeV E) (tensV E a b) := by
  obtain ⟨hT, -, hcas, -⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeV E g =
      casimir (tensV E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensV E a b g c)) = tensV E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensV_apply, vc_tensV_apply, map_add (f := _)]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeV E * tensV E a b = tensV E a b * eeV E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeV E (tensV E a b g) = (2 : ℂ) • tensV E a b (eeV E g) := by
    rw [← map_smul (tensV E a b) (2 : ℂ) (eeV E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensV E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_commVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeVd E) (tensVd E a b) := by
  obtain ⟨-, hT, -, hcas⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeVd E g =
      casimir (tensVd E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensVd E a b g c)) = tensVd E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensVd_apply, vc_tensVd_apply, map_sub]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeVd E * tensVd E a b = tensVd E a b * eeVd E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeVd E (tensVd E a b g) = (2 : ℂ) • tensVd E a b (eeVd E g) := by
    rw [← map_smul (tensVd E a b) (2 : ℂ) (eeVd E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensVd E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_gen_top (E : Fin n → Fin n → Module.End ℂ M) (φ : M)
    (hgen : genSub E (Submodule.span ℂ {φ}) = ⊤) (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (G : Submodule ℂ (Fin n → M)) (hG : ∀ a b, ∀ x ∈ G, T a b x ∈ G)
    (hφ : ∀ c, (Pi.single c φ : Fin n → M) ∈ G) : G = ⊤ := by
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G}
      add_mem' := by
        intro x y hx hy c
        rw [Pi.single_add]
        exact G.add_mem (hx c) (hy c)
      zero_mem' := by
        intro c
        rw [Pi.single_zero]
        exact G.zero_mem
      smul_mem' := by
        intro r x hx c
        rw [Pi.single_smul']
        exact G.smul_mem r (hx c) }
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm c
    have h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)
    have h2 := G.add_mem (h1 (hT a b c m)) (hG a b _ (hm c))
    simpa using h2
  have hle := vc_genSub_le E _ S (by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hφ) hSS
  rw [hgen] at hle
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle Submodule.mem_top c

end Inst

section Inst2

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_genV (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      ∑ d ∈ univ.filter (fun d => t < d), tensV E t d (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeV_single, Finset.sum_apply]
  simp only [vc_tensV_single, Pi.add_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, hlow t e h, not_lt.mpr h.le]
  · have hc : (univ.filter fun d : Fin n => e < d).card = n - 1 - e := by
      rw [filter_lt_eq_Ioi, Fin.card_Ioi]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_add, hc, hd]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
    congr 1
    have he : 1 + (e : ℕ) ≤ n := by have := e.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub he]
    simp only [rho, thV]
    push_cast
    ring
  · simp [h.ne', h]

theorem vc_genVd (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      -∑ d ∈ univ.filter (fun d => d < t), tensVd E d t (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeVd_single, Pi.neg_apply, Finset.sum_apply]
  simp only [vc_tensVd_single, Pi.sub_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, h]
  · have hc : (univ.filter fun d : Fin n => d < e).card = e := by
      rw [filter_gt_eq_Iio, Fin.card_Iio]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_sub, hc, hd,
      neg_neg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]
    congr 1
    simp only [rho, thVd]
    push_cast
    ring
  · simp [h.ne', hlow e t h, not_lt.mpr h.le]

end Inst2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section VKMain

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem vk_natCast_Ioi (c : Fin n) : (((n - 1 - (c : ℕ) : ℕ) : ℝ) : ℂ) = ((n : ℂ) - 1 - (c : ℕ)) := by
  have := c.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

theorem vk_stepV (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hdiag : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ)
    (t : Fin n) :
    (eeV E - ((thV lam t : ℝ) : ℂ) • 1) (Pi.single t φ) =
      ∑ d ∈ Ioi t, tensV E t d (Pi.single d φ) := by
  funext c
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, vk_eeV_apply, Finset.sum_apply, vk_tensV_apply, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
  rw [Pi.single_eq_same]
  rcases lt_trichotomy c t with h | h | h
  · rw [hlow t c h, Pi.single_eq_of_ne (ne_of_lt h)]
    have h1 : ∀ d ∈ Ioi t, E t d ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_lt (h.trans (mem_Ioi.1 hd))), map_zero]
    rw [Finset.sum_eq_zero h1]
    simp [ne_of_lt h]
  · subst h
    have h1 : ∀ d ∈ Ioi c, E c d ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_lt (mem_Ioi.1 hd)), map_zero]
    rw [Finset.sum_eq_zero h1, hdiag]
    simp only [Pi.single_eq_same, if_true, Finset.sum_const, Fin.card_Ioi, zero_add]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
    congr 1
    have := vk_natCast_Ioi c
    push_cast at this ⊢
    rw [this]
    simp only [rho, thV]
    push_cast
    ring
  · rw [Finset.sum_eq_single c (fun b hb hbc => by rw [Pi.single_eq_of_ne (Ne.symm hbc), map_zero])
      (fun hc => absurd (mem_Ioi.2 h) hc)]
    simp [ne_of_gt h]

theorem vk_stepVd (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hdiag : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ)
    (s : Fin n) :
    (eeVd E - ((thVd lam s : ℝ) : ℂ) • 1) (Pi.single s φ) =
      -∑ d ∈ Iio s, tensVd E d s (Pi.single d φ) := by
  funext c
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, vk_eeVd_apply, Finset.sum_apply, vk_tensVd_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
  rw [Pi.single_eq_same]
  rcases lt_trichotomy c s with h | h | h
  · rw [Finset.sum_eq_single c (fun b hb hbc => by rw [Pi.single_eq_of_ne (Ne.symm hbc), map_zero])
      (fun hc => absurd (mem_Iio.2 h) hc)]
    simp [ne_of_lt h]
  · subst h
    have h1 : ∀ d ∈ Iio c, E d c ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_gt (mem_Iio.1 hd)), map_zero]
    rw [Finset.sum_eq_zero h1, hdiag]
    simp only [Pi.single_eq_same, if_true, Finset.sum_const, Fin.card_Iio, zero_sub, neg_neg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]
    congr 1
    simp only [rho, thVd]
    push_cast
    ring
  · rw [hlow c s h, Pi.single_eq_of_ne (ne_of_gt h)]
    have h1 : ∀ d ∈ Iio s, E d s ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_gt ((mem_Iio.1 hd).trans h)), map_zero]
    rw [Finset.sum_eq_zero h1]
    simp [ne_of_gt h]

theorem vk_single_smul (c : Fin n) (r : ℂ) (x : M) :
    (Pi.single c (r • x) : Fin n → M) = r • Pi.single c x := by
  ext d
  by_cases h : d = c
  · subst h; simp
  · simp [h]

theorem vk_gen_top (E : Fin n → Fin n → Module.End ℂ M) (φ : M)
    (hgen : genSub E (Submodule.span ℂ {φ}) = ⊤) (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (f : Fin n → M) :
    f ∈ genSub T (Submodule.span ℂ (Set.range fun t : Fin n => (Pi.single t φ : Fin n → M))) := by
  set G := genSub T (Submodule.span ℂ (Set.range fun t : Fin n => (Pi.single t φ : Fin n → M)))
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G}
      add_mem' := by
        intro x y hx hy c
        rw [Pi.single_add]
        exact G.add_mem (hx c) (hy c)
      zero_mem' := by
        intro c
        rw [Pi.single_zero]
        exact G.zero_mem
      smul_mem' := by
        intro r x hx c
        rw [vk_single_smul]
        exact G.smul_mem r (hx c) }
  have hφ : Submodule.span ℂ {φ} ≤ S := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    intro c
    exact vk_le_genSub T _ (Submodule.subset_span ⟨c, rfl⟩)
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm c
    have h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)
    have h2 := G.add_mem (h1 (hT a b c m)) (vk_genSub_stable T _ a b _ (hm c))
    simpa using h2
  have hle : genSub E (Submodule.span ℂ {φ}) ≤ S := sInf_le ⟨hφ, hSS⟩
  rw [hgen] at hle
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle Submodule.mem_top c

theorem vk_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  ext d
  rw [vk_tensV_apply]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;> simp_all

theorem vk_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  ext d
  rw [vk_tensVd_apply]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;> simp_all

theorem vk_hT_V (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    Pi.single c (E a b m) - tensV E a b (Pi.single c m) ∈
      Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) := by
  rw [vk_tensV_single]
  split_ifs
  · have hx : (Pi.single a m : Fin n → M) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
      Submodule.subset_span ⟨a, rfl⟩
    simpa using Submodule.neg_mem _ hx
  · simp

theorem vk_hT_Vd (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    Pi.single c (E a b m) - tensVd E a b (Pi.single c m) ∈
      Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) := by
  rw [vk_tensVd_single]
  split_ifs
  · have hx : (Pi.single b m : Fin n → M) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
      Submodule.subset_span ⟨b, rfl⟩
    simpa using hx
  · simp

end VKMain

theorem verma_product_identity (n : ℕ) : VermaProductIdentity n := by
  intro M _ _ E lam φ hE hlow hdiag hgen
  constructor
  · refine LinearMap.ext fun f => ?_
    rw [vk_prodShift_eq, LinearMap.zero_apply]
    refine vk_kill (tensV E) (eeV E) (fun a b => vk_eeV_comm E hE a b) (fun t => ((thV lam t : ℝ) : ℂ))
      (fun t => (Pi.single t φ : Fin n → M)) (fun t => ?_) f (vk_gen_top E φ hgen _ (vk_hT_V E) f)
    rw [vk_stepV E lam φ hlow hdiag t]
    exact Submodule.sum_mem _ fun d hd => vk_genSub_stable _ _ _ _ _
      (vk_le_genSub _ _ (Submodule.subset_span ⟨d, mem_Ioi.1 hd, rfl⟩))
  · refine LinearMap.ext fun f => ?_
    rw [vk_prodShift_eq, LinearMap.zero_apply]
    have hprod : ∏ t : Fin n, (X - C (((thVd lam t : ℝ) : ℂ))) =
        ∏ t : Fin n, (X - C (((thVd lam (Fin.rev t) : ℝ) : ℂ))) :=
      (Fintype.prod_equiv Fin.revPerm _ _ (fun t => by simp)).symm
    have hrange : Set.range (fun t : Fin n => (Pi.single (Fin.rev t) φ : Fin n → M)) =
        Set.range (fun t : Fin n => (Pi.single t φ : Fin n → M)) :=
      Fin.rev_surjective.range_comp (fun t : Fin n => (Pi.single t φ : Fin n → M))
    rw [hprod]
    refine vk_kill (tensVd E) (eeVd E) (fun a b => vk_eeVd_comm E hE a b)
      (fun t => ((thVd lam (Fin.rev t) : ℝ) : ℂ))
      (fun t => (Pi.single (Fin.rev t) φ : Fin n → M)) (fun t => ?_) f
      (by rw [hrange]; exact vk_gen_top E φ hgen _ (vk_hT_Vd E) f)
    rw [vk_stepVd E lam φ hlow hdiag (Fin.rev t)]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => vk_genSub_stable _ _ _ _ _
      (vk_le_genSub _ _ (Submodule.subset_span ⟨Fin.rev d, ?_, by simp⟩)))
    simp only [Set.mem_ofPred_eq]
    exact Fin.lt_rev_iff.2 (mem_Iio.1 hd)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
