module

public import Formalism.PieriBlockIdeals.Bundle003
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
public import Formalism.PieriBlockIdeals.IntegralQuotient
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.WorkedExample

open Formalism.CohomologicalDescent

theorem weight_reflection_holds : MwFlip := by
  intro l b h t κ U
  unfold mwCount
  apply Finset.card_bij' (fun u _ => h - u) (fun u _ => h - u)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc] at hu ⊢
    obtain ⟨⟨⟨w, hw, rfl⟩, hB⟩, x, hx, hxu⟩ := hu
    refine ⟨⟨by simpa using hw, fun hc => hB ⟨by omega, by omega⟩⟩, h - x, ⟨by omega, by omega⟩, ?_⟩
    exact (Int.ModEq.refl h).sub hxu
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc] at hu ⊢
    obtain ⟨⟨hw, hB⟩, x, hx, hxu⟩ := hu
    refine ⟨⟨⟨u, hw, rfl⟩, fun hc => hB ⟨by omega, by omega⟩⟩, h - x, ⟨by omega, by omega⟩, ?_⟩
    exact (Int.ModEq.refl h).sub hxu
  · intro u _; ring
  · intro u _; ring

theorem prod_comp_eq_prod_comp {K : Type} [CommRing K] {N : ℕ} (f : Fin N → Polynomial K) (g : Polynomial K) :
    (∏ a, f a).comp g = ∏ a, (f a).comp g :=
  map_prod (Polynomial.compRingHom g) f Finset.univ

theorem linkage_reflection_holds : LinkageFlip := by
  intro K _ N U U' c c' h H
  have H2 := congrArg (fun p => p.comp (-Polynomial.X + Polynomial.C (((-h - c' - c : ℤ)) : K))) H
  simp only [prod_comp_eq_prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp] at H2
  have e : ∀ W : Fin N → ℤ, ∀ a : Fin N, -Polynomial.X + Polynomial.C (((-h - c' - c : ℤ)) : K) +
      Polynomial.C (((W a + c : ℤ)) : K) = -(Polynomial.X + Polynomial.C (((h - W a + c' : ℤ)) : K)) := by
    intro W a
    rw [neg_add, add_assoc, ← Polynomial.C_add, ← Polynomial.C_neg]
    congr 2
    push_cast
    ring
  simp only [e, Finset.prod_neg] at H2
  exact ((isUnit_neg_one).pow _).mul_left_cancel H2

theorem prod_X_add_C_shift_eq {K : Type} [CommRing K] {N : ℕ} (U U' : Fin N → ℤ) (c c' : ℤ)
    (H : (∏ a, (Polynomial.X + Polynomial.C (((U a + c : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c : ℤ)) : K))) :
    (∏ a, (Polynomial.X + Polynomial.C (((U a + c' : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c' : ℤ)) : K)) := by
  have H2 := congrArg (fun p => p.comp (Polynomial.X + Polynomial.C (((c' - c : ℤ)) : K))) H
  simp only [prod_comp_eq_prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp] at H2
  have e : ∀ W : Fin N → ℤ, ∀ a : Fin N, Polynomial.X + Polynomial.C (((c' - c : ℤ)) : K) +
      Polynomial.C (((W a + c : ℤ)) : K) = Polynomial.X + Polynomial.C (((W a + c' : ℤ)) : K) := by
    intro W a
    rw [add_assoc, ← Polynomial.C_add]
    congr 2
    push_cast
    ring
  simpa only [e] using H2

theorem weight_letters_holds : MwLetters := by
  intro ι N D σ h t hR l κ i
  obtain ⟨_, _, _, hU, _, hbot⟩ := hR
  unfold Labels.mw
  have himg : Finset.univ.image (D.U (D.cc i)) =
      (Finset.univ.image (D.U i)).image (fun u => (h : ℤ) - u) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨D.U i (Fin.rev a), ⟨_, rfl⟩, (hU i a).symm⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨Fin.rev a, by rw [hU, Fin.rev_rev]⟩
  rw [himg, hbot]
  exact weight_reflection_holds l (D.bot i) h t κ _

theorem linked_all_holds : LinkedAll := by
  intro ι N D σ h t F _ cst hR hL
  obtain ⟨hinv, _, hΦ, hU, hU', hbot⟩ := hR
  have hc : ∀ i ∈ D.Φ, StrictAnti (D.U (D.cc i)) ∧ StrictAnti (D.U' (D.cc i)) ∧
      (∀ s : Fin t, ∃ a, D.U (D.cc i) a = D.bot (D.cc i) + ((s : ℕ) : ℤ)) ∧
      (∏ a, (Polynomial.X + Polynomial.C (((D.U (D.cc i) a + 0 : ℤ)) : F))) =
        ∏ a, (Polynomial.X + Polynomial.C (((D.U' (D.cc i) a + 0 : ℤ)) : F)) := by
    intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := hL i hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      rw [hU, hU]
      have := h1 (Fin.rev_lt_rev.mpr hab)
      omega
    · intro a b hab
      rw [hU', hU']
      have := h2 (Fin.rev_lt_rev.mpr hab)
      omega
    · intro s
      obtain ⟨a, ha⟩ := h3 (Fin.rev s)
      refine ⟨Fin.rev a, ?_⟩
      rw [hU, Fin.rev_rev, ha, hbot]
      have e1 : ((Fin.rev s : Fin t) : ℕ) = t - (s + 1) := Fin.val_rev s
      have e2 := s.isLt
      omega
    · have e := linkage_reflection_holds F N (D.U i) (D.U' i) (cst i) 0 h h4
      have r1 := Equiv.prod_comp Fin.revPerm
        (fun a => (Polynomial.X + Polynomial.C ((((h : ℤ) - D.U i a + 0 : ℤ)) : F)))
      have r2 := Equiv.prod_comp Fin.revPerm
        (fun a => (Polynomial.X + Polynomial.C ((((h : ℤ) - D.U' i a + 0 : ℤ)) : F)))
      simp only [Fin.revPerm_apply] at r1 r2
      simp only [hU, hU']
      rw [r1, r2, e]
  intro i
  rcases hΦ i with hi | hi
  · obtain ⟨h1, h2, h3, h4⟩ := hL i hi
    exact ⟨h1, h2, h3, prod_X_add_C_shift_eq _ _ _ _ h4⟩
  · have := hc (D.cc i) hi
    rwa [hinv i] at this

theorem reflection_carried_facts {ι : Type} {N : ℕ} (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) (ep : ι → ι)
    (J : ι → Fin N → ℤ) (botJ : ι → ℤ) (hR : D.Refl σ h t) (hC : D.Carried ep J botJ) :
    (∀ i, ep (ep i) = i) ∧ (∀ i, σ (ep i) = ep (σ i)) ∧ (∀ i, J i = D.U' (ep i)) ∧
      (∀ i, botJ i = D.bot (ep i)) := by
  obtain ⟨hinv, hcom, _⟩ := hR
  obtain ⟨hep, hJ, hb⟩ := hC
  have h1 : ∀ i, ep (ep i) = i := by
    rcases hep with rfl | rfl
    · intro i; rfl
    · exact hinv
  have h2 : ∀ i, σ (ep i) = ep (σ i) := by
    rcases hep with rfl | rfl
    · intro i; rfl
    · exact hcom
  refine ⟨h1, h2, fun i => ?_, fun i => ?_⟩
  · rw [← hJ (ep i), h1]
  · rw [← hb (ep i), h1]

theorem orientation_lattice_holds : WEOrientLattice := by
  intro ι _ σ k j t q l h _ O F L _ _ _ _ _ _ I _ W u c D cst ep J botJ kap τ ζ em jj hl hsmall hR hL
    hC hW hS
  obtain ⟨hinv, hcom, hJ, hb⟩ := reflection_carried_facts D σ h t ep J botJ hR hC
  have all := linked_all_holds ι _ D σ h t F cst hR hL
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have e1 : D.U (ep (ep τ)) = D.U τ := by rw [hinv]
  have e2 : J (ep τ) = D.U' τ := hC.2.1 τ
  have e3 : botJ (ep τ) = D.bot τ := hC.2.2 τ
  have e4 : σ (ep τ) = ep (σ τ) := hcom τ
  have e5 : botJ (ep (σ τ)) = D.bot (σ τ) := hC.2.2 _
  have e6 : D.U (ep (ep (σ τ))) = D.U (σ τ) := by rw [hinv]
  have key := FrobeniusPeriodChange.weight_exponents_from_lattice ι σ k j t q l h O F L I W u c (fun i => D.U (ep i)) J botJ
    (fun _ => 0) kap (ep τ) ζ em jj
    hl hsmall hW (fun i => (all (ep i)).1) (fun i => by rw [hJ]; exact (all (ep i)).2.1)
    (fun i s => by rw [hb]; exact (all (ep i)).2.2.1 s)
    (fun i => by rw [hJ]; exact (all (ep i)).2.2.2)
    (by intro a; show 0 ≤ D.U (ep (ep τ)) a; rw [e1]; exact hS1 a)
    (by show ∑ a, D.U (ep (ep τ)) a = _; rw [e1, e2]; exact hS2)
    (by intro a h1 h2; show D.U (ep (ep τ)) a = _; rw [e1, e3]; exact hS3 a h1 h2)
  simp only [e4, e1, e2, e3, e5, e6] at key
  exact key

end Formalism.CohomologicalDescent.WorkedExample
end
end

section

namespace Formalism.CohomologicalDescent.LR

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.Symmetrization

theorem lrd_core {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℚ V]
    (φ : ι → Module.End ℚ V) (hφ : ∀ a b, Commute (φ a) (φ b)) (L : AddSubgroup V)
    (hL : ∀ (v : ι) (k : ℕ), ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • ((φ v) ^ k) x ∈ L) :
    ∀ (M : Multiset ι), ∀ x ∈ L,
      (((∏ v, (Multiset.count v M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x ∈ L := by
  suffices key : ∀ n : ℕ, ∀ M : Multiset ι, Multiset.card M = n → ∀ x ∈ L,
      (((∏ v, (Multiset.count v M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x ∈ L by
    intro M
    exact key _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hn x hx
    by_cases hM : M = 0
    · subst hM
      simp [hx]
    obtain ⟨v, hv⟩ := Multiset.exists_mem_of_ne_zero hM

    set c := Multiset.count v M with hc
    set M' := M.filter (fun w => ¬ w = v) with hM'
    have hsplit : M = Multiset.replicate c v + M' := by
      rw [hM', hc, ← Multiset.filter_eq' M v, Multiset.filter_add_not]
    have hc0 : 0 < c := Multiset.count_pos.mpr hv
    have hcard : Multiset.card M' < n := by
      have e := congrArg Multiset.card hsplit
      rw [Multiset.card_add, Multiset.card_replicate] at e
      omega
    have hperm : M.toList.Perm (List.replicate c v ++ M'.toList) := by
      have e : (M.toList : Multiset ι) = ((List.replicate c v ++ M'.toList : List ι) : Multiset ι) := by
        rw [Multiset.coe_toList, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_replicate]
        exact hsplit
      exact Multiset.coe_eq_coe.mp e
    have hpw : (M.toList.map φ).Pairwise Commute :=
      List.pairwise_map.mpr (List.pairwise_of_forall fun a b => hφ a b)
    have hprod : (M.toList.map φ).prod = φ v ^ c * (M'.toList.map φ).prod := by
      rw [(hperm.map φ).prod_eq' hpw]
      simp [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]

    have hcnt : ∀ w ∈ Finset.univ.erase v, Multiset.count w M' = Multiset.count w M := by
      intro w hw
      exact Multiset.count_filter_of_pos (Finset.ne_of_mem_erase hw)
    have hcv : Multiset.count v M' = 0 := Multiset.count_filter_of_neg (fun h => h rfl)
    have hfact : (∏ w, (Multiset.count w M).factorial : ℕ) =
        c.factorial * ∏ w, (Multiset.count w M').factorial := by
      rw [← Finset.mul_prod_erase Finset.univ (fun w => (Multiset.count w M).factorial) (Finset.mem_univ v),
        ← Finset.mul_prod_erase Finset.univ (fun w => (Multiset.count w M').factorial) (Finset.mem_univ v),
        hcv, Nat.factorial_zero, one_mul]
      congr 1
      exact Finset.prod_congr rfl fun w hw => by rw [hcnt w hw]
    have hrest := ih _ (hn ▸ hcard) M' rfl x hx
    have e : (((∏ w, (Multiset.count w M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x =
        ((c.factorial : ℚ)⁻¹) • (φ v ^ c)
          ((((∏ w, (Multiset.count w M').factorial : ℕ) : ℚ)⁻¹) • (M'.toList.map φ).prod x) := by
      rw [hprod, hfact, Module.End.mul_apply, map_smul, smul_smul, Nat.cast_mul, mul_inv]
    rw [e]
    exact hL v c _ hrest

theorem Fs_div_mem {V P R : Type} [AddCommGroup V] [Module ℚ V] [DecidableEq P] [DecidableEq R] [Fintype P]
    [Fintype R] (S : Symmetrization.HidaSetting ℚ V P R) (L : AddSubgroup V)
    (hL : ∀ (v : R × P) (k : ℕ), ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • ((S.f v) ^ k) x ∈ L) {n : ℕ}
    (m : Sym (R × P) n) : ∀ x ∈ L, ((Symmetrization.mfact m : ℚ)⁻¹) • S.Fs m x ∈ L := by
  have hcomm : ∀ a b : R × P, Commute (S.f a) (S.f b) := by
    intro a b
    have h := S.comm (Sum.inr a.1) (Sum.inl a.2) (Sum.inr b.1) (Sum.inl b.2)
    simp only [reduceCtorEq, if_false, sub_zero] at h
    exact sub_eq_zero.mp h
  intro x hx
  exact lrd_core S.f hcomm L hL m.1 x hx

end Formalism.CohomologicalDescent.LR
end
