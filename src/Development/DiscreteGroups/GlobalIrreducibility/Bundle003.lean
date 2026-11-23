module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle001
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem exists_scale (X : Finset k) :
    ∃ t : kˣ, valuation k (t : k) ≤ 1 ∧ ∀ x ∈ X, valuation k ((t : k) * x) ≤ 1 := by
  classical
  have hne : ∀ x : k, ¬ valuation k x ≤ 1 → x ≠ 0 := fun x h h0 => h (by simp [h0])
  let f : k → kˣ := fun x => if h : valuation k x ≤ 1 then 1 else (Units.mk0 x (hne x h))⁻¹
  have hf1 : ∀ x, valuation k ((f x : kˣ) : k) ≤ 1 := by
    intro x
    by_cases h : valuation k x ≤ 1
    · simp [f, h]
    · simp only [f, dif_neg h, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
      push Not at h
      exact inv_le_one_of_one_le₀ h.le
  have hf2 : ∀ x, valuation k ((f x : kˣ) * x) ≤ 1 := by
    intro x
    by_cases h : valuation k x ≤ 1
    · simpa [f, h] using h
    · simp only [f, dif_neg h, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [inv_mul_cancel₀ (hne x h), map_one]
  refine ⟨∏ x ∈ X, f x, ?_, fun y hy => ?_⟩
  · rw [Units.coe_prod, map_prod]
    exact Finset.prod_le_one' fun x _ => hf1 x
  · rw [Units.coe_prod, ← Finset.mul_prod_erase X (fun x => ((f x : kˣ) : k)) hy, mul_assoc, mul_comm, mul_assoc,
      map_mul]
    have h1 : valuation k (∏ x ∈ X.erase y, ((f x : kˣ) : k)) ≤ 1 := by
      rw [map_prod]; exact Finset.prod_le_one' fun x _ => hf1 x
    calc valuation k (∏ x ∈ X.erase y, ((f x : kˣ) : k)) * valuation k (y * (f y : k))
        ≤ 1 * 1 := by gcongr; rw [mul_comm]; exact hf2 y
      _ = 1 := one_mul 1

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j : Fin m, Continuous fun g : GL (Fin m) k => (g : Matrix (Fin m) (Fin m) k) i j :=
    fun i j => (Units.continuous_val (M := Matrix (Fin m) (Fin m) k)).matrix_elem i j
  have e : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i : Fin m, ⋂ j : Fin m, {g : GL (Fin m) k | j < i → (g : Matrix (Fin m) (Fin m) k) i j = 0}) ∩
        ⋂ i : Fin m, {g : GL (Fin m) k | (g : Matrix (Fin m) (Fin m) k) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => ?_).inter (isClosed_iInter fun i => isClosed_eq (hc i i) continuous_const)
  by_cases hji : j < i
  · simpa [hji] using isClosed_eq (hc i j) continuous_const
  · simp [hji]

theorem diag_conj_apply (t : Fin m → kˣ) (g : GL (Fin m) k) (i j : Fin m) :
    ((diagT k (Fin m) t * g * (diagT k (Fin m) t)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j =
      (t i : k) * (g : Matrix (Fin m) (Fin m) k) i j * ((t j)⁻¹ : kˣ) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

theorem diag_conj_mem_unipB (t : Fin m → kˣ) {g : GL (Fin m) k} (hg : g ∈ unipB k (Fin m)) :
    diagT k (Fin m) t * g * (diagT k (Fin m) t)⁻¹ ∈ unipB k (Fin m) := by
  refine (mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [diag_conj_apply, ((mem_unipB _).1 hg).1 i j hij]; simp
  · rw [diag_conj_apply, ((mem_unipB _).1 hg).2 i]; simp

theorem exists_compact_unip (F : Finset (GL (Fin m) k)) (hF : ∀ u ∈ F, u ∈ unipB k (Fin m)) :
    ∃ C : Subgroup (GL (Fin m) k), IsCompact (C : Set (GL (Fin m) k)) ∧ C ≤ unipB k (Fin m) ∧ ∀ u ∈ F, u ∈ C := by
  classical
  obtain ⟨t, ht1, ht⟩ := exists_scale ((F ×ˢ (Finset.univ ×ˢ Finset.univ)).image
    fun x : GL (Fin m) k × Fin m × Fin m => (x.1 : Matrix (Fin m) (Fin m) k) x.2.1 x.2.2)
  let d : GL (Fin m) k := diagT k (Fin m) fun i => t ^ (i : ℕ)
  let C : Subgroup (GL (Fin m) k) := (unipB k (Fin m) ⊓ KO k (Fin m)).map (MulAut.conj d).toMonoidHom
  refine ⟨C, ?_, ?_, fun u hu => ?_⟩
  · rw [Subgroup.coe_map, Subgroup.coe_inf]
    refine (GlobalTheory.SplitFlip.isCompact_KO.inter_left isClosed_unipB).image ?_
    exact (continuous_const.mul continuous_id).mul continuous_const
  · rintro _ ⟨g, hg, rfl⟩
    exact diag_conj_mem_unipB _ hg.1
  · have e : diagT k (Fin m) (fun i => (t ^ (i : ℕ))⁻¹) = d⁻¹ := by rw [← map_inv]; rfl
    have hU : d⁻¹ * u * d ∈ unipB k (Fin m) := by
      have := diag_conj_mem_unipB (fun i => (t ^ (i : ℕ))⁻¹) (hF u hu)
      rwa [e, inv_inv] at this
    have hent : ∀ i j, ((d⁻¹ * u * d : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j =
        ((t : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin m) (Fin m) k) i j * (t : k) ^ (j : ℕ) := by
      intro i j
      have e2 : d⁻¹ * u * d = diagT k (Fin m) (fun i => (t ^ (i : ℕ))⁻¹) * u *
          (diagT k (Fin m) (fun i => (t ^ (i : ℕ))⁻¹))⁻¹ := by rw [e, inv_inv]
      rw [e2, diag_conj_apply]
      simp
    refine ⟨d⁻¹ * u * d, ⟨hU, mem_KO_of_unip hU fun i j => ?_⟩, ?_⟩
    · rw [hent]
      rcases lt_trichotomy i j with hij | rfl | hij
      · obtain ⟨c, hc⟩ : ∃ c : ℕ, (j : ℕ) = i + (c + 1) := ⟨j - i - 1, by rw [Fin.lt_def] at hij; omega⟩
        have ht0 : (t : k) ^ (i : ℕ) ≠ 0 := pow_ne_zero _ t.ne_zero
        have e3 : ((t : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin m) (Fin m) k) i j * (t : k) ^ (j : ℕ) =
            (t : k) ^ c * ((t : k) * (u : Matrix (Fin m) (Fin m) k) i j) := by
          rw [hc, pow_add, pow_succ]
          calc ((t : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin m) (Fin m) k) i j * ((t : k) ^ (i : ℕ) * ((t : k) ^ c * t))
              = (((t : k) ^ (i : ℕ))⁻¹ * (t : k) ^ (i : ℕ)) * ((t : k) ^ c * ((t : k) * (u : Matrix (Fin m) (Fin m) k) i j)) := by ring
            _ = _ := by rw [inv_mul_cancel₀ ht0, one_mul]
        rw [e3, map_mul, map_pow]
        exact mul_le_one' (pow_le_one' ht1 c) (ht _ (Finset.mem_image.2 ⟨(u, i, j), by simp [hu], rfl⟩))
      · rw [((mem_unipB _).1 (hF u hu)).2 i, mul_one, inv_mul_cancel₀ (pow_ne_zero _ t.ne_zero), map_one]
      · rw [((mem_unipB _).1 (hF u hu)).1 i j hij]; simp
    · simp [MulAut.conj_apply, d, mul_assoc]

end DiscreteGroups.sglob.DzType
end
end

section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) {c : kˣ} (hc : HasConductor ψ c)


include hc in
theorem dual_sum_eq_zero {s t : kˣ} {b : k} (hbt : b ∈ ball t) (hbs : b ∉ ball s) :
    ∑ f : Q (c * t⁻¹) (c * s⁻¹), ((ψ (-(((Quotient.out f : ↥(ball (c * s⁻¹))) : k) * b)) : Circle) : ℂ) = 0 := by
  obtain ⟨ξ0, hξ0, hne⟩ := hc.exists_ne_one (c * s⁻¹) (x := b)
    (by rw [show c * (c * s⁻¹)⁻¹ = s by rw [mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]]; exact hbs)
  let φ : k → ℂ := fun ξ => ((ψ (-(ξ * b)) : Circle) : ℂ)
  have hφ : ∀ ξ, ∀ h ∈ ball (c * t⁻¹), φ (ξ + h) = φ ξ := by
    intro ξ h hh
    show ((ψ (-((ξ + h) * b)) : Circle) : ℂ) = ψ (-(ξ * b))
    rw [add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh hbt, Circle.coe_one, mul_one]
  let ξ0' : ↥(ball (c * s⁻¹)) := ⟨ξ0, hξ0⟩
  have shift : ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) =
      φ ξ0 * ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) := by
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ξ0' : Q (c * t⁻¹) (c * s⁻¹)))]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Equiv.coe_addRight, apply_out φ hφ (Quotient.out f + ξ0') _
      (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq'])]
    simp only [φ, AddSubgroup.coe_add, ξ0']
    rw [add_mul, neg_add, ch_add ψ, mul_comm]
  have hne' : φ ξ0 ≠ 1 := by
    intro h1
    apply hne
    have := ch_neg_mul ψ (ξ0 * b)
    simp only [φ] at h1
    rw [h1, one_mul] at this
    exact Circle.coe_eq_one.1 this
  have h2 : (1 - φ ξ0) * ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) = 0 := by
    rw [sub_mul, one_mul, ← shift, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne'.symm)


include hc in
theorem sum_avg {s t : kˣ} {x : V} (hx : ∀ h ∈ ball s, σ h x = x) :
    ∑ f : Q (c * t⁻¹) (c * s⁻¹), avg ψ σ s t ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) x =
      ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x := by
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (0 : Q s t)]
  · rw [hx _ out_zero_mem]
    congr 1
    have h1 : ∀ f : Q (c * t⁻¹) (c * s⁻¹), ((ψ (-(((Quotient.out f : ↥(ball (c * s⁻¹))) : k) *
        ((Quotient.out (0 : Q s t) : ↥(ball t)) : k))) : Circle) : ℂ) = 1 := fun f => by
      rw [psi_neg_triv hc (out_mem f) out_zero_mem, Circle.coe_one]
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · intro q _ hq
    rw [dual_sum_eq_zero ψ hc (out_mem q) (fun h => hq ((out_mem_iff q).1 h)), zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end DiscreteGroups.sglob.LConvGenF
end
end
