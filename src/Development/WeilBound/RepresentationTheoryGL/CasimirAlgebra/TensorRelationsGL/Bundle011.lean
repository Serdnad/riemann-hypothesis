module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepFormulaA
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlgA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle006
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace PStepFormula

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem one (hT : TensorGl) (hJ : JMComm) (hQ : PiQdet) (hC : Curry) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : GlRel E) (u : ℂ) :
    (PiJ 1 E u * qdet (tE (Finset.univ : Finset (Fin 1)) E) u : Module.End ℂ (TV n M (Fin 1))) =
      lift (qdet E u) * PiJ 1 E (u + 1) := by
  obtain ⟨hbij, -, h3, h4, -, -, h7⟩ := hC n M E 1 n
  set e := LinearEquiv.ofBijective (curF n M 1 n) hbij
  have hG : GlRel (tE (Finset.univ : Finset (Fin 1)) E) := (hT n M (Fin 1) E hE Finset.univ).1
  have hE' : GlRel (fun a b => (lift (E a b) : Module.End ℂ (TV n M (Fin 1)))) :=
    glRel_map (liftA n M (Fin 1)) hE
  have hsw : ∀ a b : Fin n, e.conjAlgEquiv ℂ (pm (Equiv.swap (Fin.natAdd 1 a) (Fin.natAdd 1 b))) =
      pm (Equiv.swap a b) := fun a b => conj_eq e fun x => LinearMap.congr_fun (h7 a b) x
  have hOr : ∀ j : Fin n, e.conjAlgEquiv ℂ (Om E (Fin.natAdd 1 j)) = Om (fun a b => lift (E a b)) j :=
    fun j => conj_eq e fun x => curF_Om_r E j x
  have hOl : e.conjAlgEquiv ℂ (Om E (Fin.castAdd n (0 : Fin 1))) = lift (Om E 0) :=
    conj_eq e fun x => curF_Om_l E 0 x
  have s1 : e.conjAlgEquiv ℂ (PiJ (1 + n) E u) = lift (PiJ 1 E u) * PiJ n (tE Finset.univ E) u := by
    rw [lift_PiJ]
    unfold PiJ
    rw [List.ofFn_add, List.prod_append, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    simp only [Function.comp_def, map_add (f := _), AlgEquiv.commutes]
    congr 2
    · congr 1; funext i; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h3 i) x
    · congr 1; funext j; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h4 j) x
  set Q : Module.End ℂ (TV n M (Fin (1 + n))) :=
    ∑ j : Fin n, pm (Equiv.swap (Fin.natAdd 1 j) (Fin.castAdd n 0)) with hQdef
  have s2 : e.conjAlgEquiv ℂ (PiJ (1 + n) E u) =
      PiJ n (fun a b => lift (E a b)) u * (algebraMap ℂ _ u + lift (Om E 0) + e.conjAlgEquiv ℂ Q) := by
    have hR : pm (rot n) * PiJ (1 + n) E u * pm (rot n)⁻¹ = PiJ (1 + n) E u := by
      rw [← ((hJ n M E hE (1 + n)).2.2 u (rot n)).eq, mul_assoc, ← pm_mul, mul_inv_cancel, pm_one, mul_one]
    let eρ : TV n M (Fin (1 + n)) ≃ₗ[ℂ] TV n M (Fin (1 + n)) :=
      LinearEquiv.ofLinear (pm (rot n)) (pm (rot n)⁻¹)
        (by rw [← Module.End.mul_eq_comp, ← pm_mul, mul_inv_cancel, pm_one]; rfl)
        (by rw [← Module.End.mul_eq_comp, ← pm_mul, inv_mul_cancel, pm_one]; rfl)
    have hΨ : ∀ T, eρ.conjAlgEquiv ℂ T = pm (rot n) * T * pm (rot n)⁻¹ := fun T => rfl
    rw [← hR, ← hΨ]
    unfold PiJ
    rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, List.ofFn_congr (Nat.add_comm 1 n),
      List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    simp only [Function.comp_apply, map_add (f := _), AlgEquiv.commutes]
    congr 1
    · congr 1; congr 1; funext j; congr 1
      have hk : (Fin.cast (Nat.add_comm 1 n).symm j.castSucc : Fin (1 + n)) = ⟨j, by omega⟩ := Fin.ext (by simp)

      rw [hΨ, conj_xJ hT E hE, hk, rot_nat, map_add (f := _), hOr, xJ, sum_lt_cast _ (by simp), map_sum]
      congr 1
      refine Finset.sum_congr (Finset.filter_congr fun i _ => Iff.rfl) fun i _ => ?_
      rw [rot_nat, hsw]
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hΨ, conj_xJ hT E hE, rot_last _ (by simp), map_add (f := _), hOl, sum_lt_cast _ (by simp), hQdef, map_sum, map_sum,
          add_assoc]
      congr 2
      refine Finset.sum_congr (Finset.filter_true_of_mem fun i _ => by simp) fun i _ => ?_
      rw [rot_nat]
  have hQalt : e.conjAlgEquiv ℂ Q * alt Finset.univ = alt Finset.univ := by
    apply LinearMap.ext; intro g
    rw [Module.End.mul_apply]
    funext J I
    have hsymm : ∀ (y : TV n (TV n M (Fin 1)) (Fin n)) (I' : Fin 1 → Fin n) (J' : Fin n → Fin n),
        e.symm y (Fin.append I' J') = y J' I' := fun y I' J' =>
      congrFun (congrFun (e.apply_symm_apply y) J') I'
    show (Q (e.symm (alt Finset.univ g))) (Fin.append I J) = _
    rw [hQdef, LinearMap.sum_apply, Finset.sum_apply]
    simp only [pm_apply, app_swap, hsymm]
    exact sum_swap (fun J I => alt Finset.univ g J I) (fun J a b hab => alt_swap g J a b hab) J I
  have hq1 := hQ n _ _ hG u
  have hq2 := hQ n _ _ hE' u
  have hqE : qdet (fun a b => (lift (E a b) : Module.End ℂ (TV n M (Fin 1)))) u = lift (qdet E u) :=
    (qdet_map (liftA n M (Fin 1)) E u).symm
  have hcomm : ∀ B : Module.End ℂ (TV n M (Fin 1)),
      (alt Finset.univ : Module.End ℂ (TV n (TV n M (Fin 1)) (Fin n))) * lift B = lift B * alt Finset.univ := by
    intro B
    simp only [alt, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, (lift_comm_pm B _).eq]
  have hl : (lift (algebraMap ℂ _ (u + 1) + Om E 0) : Module.End ℂ (TV n (TV n M (Fin 1)) (Fin n))) =
      algebraMap ℂ _ u + lift (Om E 0) + 1 := by
    rw [← liftA_apply, map_add (f := _), AlgHom.commutes, liftA_apply, map_add (f := _), map_one]; abel
  rw [PiJ_one E (u + 1)]
  apply ext_of_alt (n := n)
  calc lift (PiJ 1 E u * qdet (tE Finset.univ E) u) * alt Finset.univ
      = lift (PiJ 1 E u) * (PiJ n (tE Finset.univ E) u * alt Finset.univ) := by rw [hq1, lift_mul, mul_assoc]
    _ = e.conjAlgEquiv ℂ (PiJ (1 + n) E u) * alt Finset.univ := by rw [s1, mul_assoc]
    _ = PiJ n (fun a b => lift (E a b)) u * (lift (algebraMap ℂ _ (u + 1) + Om E 0) * alt Finset.univ) := by
        rw [s2, mul_assoc, hl, add_mul, hQalt, add_mul _ 1, one_mul]
    _ = PiJ n (fun a b => lift (E a b)) u * alt Finset.univ * lift (algebraMap ℂ _ (u + 1) + Om E 0) := by
        rw [← hcomm, mul_assoc]
    _ = lift (lift (qdet E u) * (algebraMap ℂ _ (u + 1) + Om E 0)) * alt Finset.univ := by
        rw [hq2, hqE, mul_assoc, hcomm, ← mul_assoc, ← lift_mul]

end PStepFormula

open PStepFormula in
theorem stepFormula_of : TensorGl → JMComm → PiQdet → Curry → StepFormula := by
  intro hT hJ hQ hC n M _ _ E hE m
  induction m generalizing M with
  | zero =>
    intro u
    have h0 : (tE (Finset.univ : Finset (Fin 0)) E : Fin n → Fin n → Module.End ℂ (TV n M (Fin 0))) =
        fun a b => liftA n M (Fin 0) (E a b) := by
      funext a b; simp [tE, liftA_apply]
    rw [h0, ← qdet_map, liftA_apply]
    simp [PiJ]
  | succ m ih =>
    intro u
    obtain ⟨hbij, h2, h3, h4, h5, -, -⟩ := hC n M E m 1
    set e := LinearEquiv.ofBijective (curF n M m 1) hbij
    have hG : GlRel (tE (Finset.univ : Finset (Fin m)) E) := (hT n M (Fin m) E hE Finset.univ).1
    have hsplit : ∀ v : ℂ, e.conjAlgEquiv ℂ (PiJ (m + 1) E v) =
        lift (PiJ m E v) * PiJ 1 (tE Finset.univ E) v := by
      intro v
      rw [lift_PiJ]
      unfold PiJ
      rw [List.ofFn_add, List.prod_append, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      simp only [Function.comp_def, map_add (f := _), AlgEquiv.commutes]
      congr 2
      · congr 1; funext i; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h3 i) x
      · congr 1; funext j; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h4 j) x
    have hq : e.conjAlgEquiv ℂ (qdet (tE (Finset.univ : Finset (Fin (m + 1))) E) u) =
        qdet (tE (Finset.univ : Finset (Fin 1)) (tE (Finset.univ : Finset (Fin m)) E)) u := by
      rw [← AlgEquiv.coe_toAlgHom, qdet_map]
      congr 1; funext a b
      exact conj_eq e fun x => LinearMap.congr_fun (h2 a b) x
    have hl : e.conjAlgEquiv ℂ (lift (qdet E u)) = lift (lift (qdet E u)) :=
      conj_eq e fun x => LinearMap.congr_fun (h5 _) x
    apply (e.conjAlgEquiv ℂ).injective
    rw [map_mul, map_mul, hsplit, hsplit, hq, hl, mul_assoc, one hT hJ hQ hC _ hG, ← mul_assoc, ← lift_mul, ih M E hE,
      lift_mul, mul_assoc]

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

open WallAlgP in
theorem wallAlg_of (hA : TensorGl) (_hJ : JMComm) (hQ : QdetFacts) (hS : Spectrum) : WallAlg := by
  unfold WallAlg
  intro n M _ _ E₁ E₂ h₁ h₂ hcomm s₁ s₂ c hc₁ hc₂ m X hX hperm hOm htot
  obtain ⟨ξ0, hξ0X, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  have eqA : (n:ℂ) * (s₁ + s₂) + n * (n - 1) + m = n * c := by
    have tr₁ := (hQ n M E₁ h₁).2.2.1 _ hc₁
    have tr₂ := (hQ n M E₂ h₂).2.2.1 _ hc₂
    have key1 := trace_rel E₁ E₂ c _ _ ξ0 tr₁ tr₂ (fun a b => htot a b ξ0 hξ0X)
    have e := smul_left_injective ℂ hξ0 key1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e
    linear_combination e
  refine ⟨eqA, fun hm => ?_⟩
  have hOmC : ∀ (σ : Equiv.Perm (Fin m)) (p : Fin m), pm σ * Om E₁ p = Om E₁ (σ p) * pm σ :=
    (hA n M (Fin m) E₁ h₁ Finset.univ).2.2.2
  have key : ∀ k, k < n → k ≤ m → (∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0) →
      k < m ∧ ∃ ξ ∈ X, alt (firstG m (k + 1)) ξ ≠ 0 := by
    intro k hkn hkm hPk
    by_contra hneg
    have hout : ∀ ξ ∈ X, ∀ i : Fin m, k ≤ (i:ℕ) →
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j i) (alt (firstG m k) ξ) = alt (firstG m k) ξ := by
      intro ξ hξ i hi
      have hk : k < m := lt_of_le_of_lt hi i.isLt
      have hz : ∀ η ∈ X, alt (firstG m (k + 1)) η = 0 := by
        intro η hη
        by_contra hne
        exact hneg ⟨hk, η, hη, hne⟩
      exact outer hk X hperm hz ξ hξ i hi
    have hsw : ∀ ξ : TV n M (Fin m), ∀ i j : Fin m, i ≠ j → (i:ℕ) < k → (j:ℕ) < k →
        pm (Equiv.swap i j) (alt (firstG m k) ξ) = -alt (firstG m k) ξ := by
      intro ξ i j hij hi hj
      have hmem : Equiv.swap i j ∈ firstG m k := by
        rw [mem_firstG]
        intro l hl
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          rw [h] at hl
          omega
        · intro h
          rw [h] at hl
          omega
      rw [pm_alt_first _ hmem, Equiv.Perm.sign_swap hij]
      simp
    have hinv : ∀ y ∈ X.map (alt (firstG m k)),
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₁ j) y ∈ X.map (alt (firstG m k)) := by
      intro y hy
      obtain ⟨ξ, hξ, rfl⟩ := Submodule.mem_map.mp hy
      simp only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
      refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j hj => Submodule.sum_mem _ fun i hi => ?_)
      · rw [← om_alt E₁ hOmC k ξ]
        exact Submodule.mem_map_of_mem (Submodule.sum_mem _ fun j _ => hOm j ξ hξ)
      · have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        rw [hsw ξ i j (ne_of_lt hi') (lt_trans (show (i:ℕ) < (j:ℕ) from hi') hj') hj']
        exact Submodule.neg_mem _ (Submodule.mem_map_of_mem hξ)
    obtain ⟨ξ1, hξ1X, hξ1⟩ := hPk
    obtain ⟨L₁, hL₁⟩ := (hS n M E₁ h₁ (fun _ => s₁) s₁ hc₁ (fun _ => ⟨0, by simp⟩) m).1 k hkm
    obtain ⟨L₂, hL₂⟩ := (hS n M E₂ h₂ (fun _ => s₂) s₂ hc₂ (fun _ => ⟨0, by simp⟩) m).1 k hkm
    obtain ⟨w, hwY, hw0, r₁, hw1⟩ := eigen (X.map (alt (firstG m k))) _ hinv
      (fun r : ℕ => (k:ℂ) * s₁ + r) L₁ hL₁ (alt (firstG m k) ξ1) (Submodule.mem_map_of_mem hξ1X) hξ1
    obtain ⟨ζ, hζ, rfl⟩ := Submodule.mem_map.mp hwY
    have hwX : alt (firstG m k) ζ ∈ X := alt_mem X hperm ζ hζ
    have hw := fun a b => htot a b _ hwX
    set w := alt (firstG m k) ζ with hwdef
    have hT : ∀ E : Fin n → Fin n → Module.End ℂ M, (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E j) w =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), Om E j w +
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w := by
      intro E
      simp only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
    have hsplit : ∀ j : Fin m, (j:ℕ) < k →
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
          ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w +
            ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), pm (Equiv.swap j p) w := by
      intro j hj
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h1 : p = j
      · subst h1
        simp [not_le.mpr hj]
      · by_cases h2 : (p:ℕ) < k
        · simp [h1, h2, not_le.mpr h2]
        · simp [h1, h2, not_lt.mp h2]
    have e1 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), (∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w +
            ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), pm (Equiv.swap j p) w) :=
      Finset.sum_congr rfl fun j hj => hsplit j (Finset.mem_filter.mp hj).2
    have e2 : ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j p) w =
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), w :=
      Finset.sum_congr rfl fun p hp => hout ζ hζ p (Finset.mem_filter.mp hp).2
    have e3 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w =
        2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w :=
      symm_sum (fun i j => pm (Equiv.swap i j) w) (fun i j => by simp only [Equiv.swap_comm i j])
    have hmid : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
        2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w +
          ((m:ℂ) - k) • w := by
      rw [e1, Finset.sum_add_distrib, e3, Finset.sum_comm, e2, Finset.sum_const, card_highS hkm,
        ← Nat.cast_smul_eq_nsmul ℂ (m - k), Nat.cast_sub hkm]
    have hsum : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k),
        (Om E₁ j w + Om E₂ j w + ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w + (n:ℂ) • w) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), c • w :=
      Finset.sum_congr rfl fun j _ => contr E₁ E₂ c w hw j
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_lowS hkm] at hsum
    rw [hmid] at hsum
    have h1 := hw1
    rw [hT E₁] at h1
    have hT2 : (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₂ j) w =
        ((k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁)) • w := by
      rw [hT E₂]
      linear_combination (norm := module) hsum - h1
    obtain ⟨r₂, hr₂⟩ := eigen_val _ (fun r : ℕ => (k:ℂ) * s₂ + r) L₂ hL₂ w hw0 _ hT2
    have hr : (k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁) = k * s₂ + r₂ := hr₂
    have hfin : (m:ℂ) * k = m * n + n * (r₁ + r₂) := by
      linear_combination (n:ℂ) * hr + (k:ℂ) * eqA
    have hnat : m * k = m * n + n * (r₁ + r₂) := by exact_mod_cast hfin
    have h3 : m * (k + 1) ≤ m * n := Nat.mul_le_mul_left m hkn
    nlinarith [Nat.zero_le (n * (r₁ + r₂))]
  have hall : ∀ k, k ≤ n → k ≤ m ∧ ∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨Nat.zero_le _, ξ0, hξ0X, by rwa [alt_zero]⟩
    | succ k ih =>
      intro hk
      obtain ⟨hkm, hP⟩ := ih (Nat.le_of_succ_le hk)
      exact key k (Nat.lt_of_succ_le hk) hkm hP
  exact hall n le_rfl

end PositivityTheory.Rg.Cz

end
end
