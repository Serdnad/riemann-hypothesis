module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle573
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Data.Fintype.Order
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.Int.LeastGreatest

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem multiset_eq_of_powerSums_zpow_eq : ∀ (k : Type) [Field k] [CharZero k] (z : k), z ≠ 0 →
    (∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1) → ∀ J J' : Multiset ℤ,
    (∀ n : ℕ, (J.map fun h => (z ^ h) ^ n).sum = (J'.map fun h => (z ^ h) ^ n).sum) → J = J' := by
  intro k _ _ z hz hroot J J' hsum

  have hlt : ∀ a b : ℤ, a < b → z ^ a ≠ z ^ b := by
    intro a b hab heq
    have h1 : z ^ (b - a) = 1 := by
      rw [zpow_sub₀ hz, heq, div_self (zpow_ne_zero _ hz)]
    have h2 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    rw [← h2, zpow_natCast] at h1
    exact hroot _ (by omega) h1
  have hinj : Function.Injective (fun h : ℤ => z ^ h) := by
    intro a b hab
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt a b h hab
    · exact hlt b a h hab.symm

  let χ : ℤ → (Multiplicative ℕ →* k) := fun h => powersHom k (z ^ h)
  have hχ : Function.Injective χ := (powersHom k).injective.comp hinj
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) k).comp χ hχ
  rw [linearIndependent_iff'] at hli

  have key : ∀ (M : Multiset ℤ) (s : Finset ℤ), M.toFinset ⊆ s → ∀ f : ℤ → k,
      (M.map f).sum = ∑ h ∈ s, (M.count h : k) * f h := by
    intro M s hs f
    rw [Finset.sum_multiset_map_count]
    simp_rw [nsmul_eq_mul]
    apply Finset.sum_subset hs
    intro x _ hx
    rw [Multiset.mem_toFinset] at hx
    simp [Multiset.count_eq_zero.mpr hx]
  set s : Finset ℤ := (J + J').toFinset with hs
  have hJ : J.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inl hx)
  have hJ' : J'.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inr hx)
  have hzero := hli s (fun h => (J.count h : k) - (J'.count h : k)) (by
    funext m
    have e := hsum (Multiplicative.toAdd m)
    rw [key J s hJ, key J' s hJ'] at e
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    simp only [χ, powersHom_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact e)
  refine Multiset.ext.mpr (fun a => ?_)
  by_cases ha : a ∈ s
  · have := hzero a ha
    rw [sub_eq_zero] at this
    exact_mod_cast this
  · rw [hs, Multiset.mem_toFinset, Multiset.mem_add, not_or] at ha
    rw [Multiset.count_eq_zero.mpr ha.1, Multiset.count_eq_zero.mpr ha.2]

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.SmallRootCl

variable {l : ℕ} [Fact l.Prime]

theorem norm_one_add_pow_sub_one_le (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (m : ℕ) :
    ‖(1 + x) ^ m - 1‖ ≤ ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ‖1 + x‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hx)
    have e : (1 + x) ^ (m + 1) - 1 = ((1 + x) ^ m - 1) * (1 + x) + x := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖(1 + x) ^ m - 1‖ * ‖1 + x‖ ≤ ‖x‖ * 1 :=
          mul_le_mul ih h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _

theorem inv_le_norm_prime (q : ℕ) (hq : q.Prime) : (l : ℝ)⁻¹ ≤ ‖(q : ℂ_[l])‖ := by
  have hl : l.Prime := Fact.out
  have h := PadicComplex.norm_extends' l (q : ℚ_[l])
  rw [map_natCast, PadicComplex.coe_natCast] at h
  rw [h]
  by_cases hql : q = l
  · subst hql; rw [Padic.norm_p]
  · have hc : Nat.Coprime l q := (Nat.coprime_primes hl hq).2 (Ne.symm hql)
    rw [(Padic.norm_natCast_eq_one_iff).2 hc]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le)

theorem not_root (x : ℂ_[l]) (hx0 : x ≠ 0) (hx : ‖x‖ < (l : ℝ)⁻¹) (i : ℕ) (hi : 1 ≤ i) :
    (1 + x) ^ i ≠ 1 := by
  intro hpow
  have hl : l.Prime := Fact.out
  have hx1 : ‖x‖ ≤ 1 := hx.le.trans (inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le))
  set ζ := 1 + x with hζ
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨i, by omega, hpow⟩
  set d := orderOf ζ with hd
  have hdpos : 0 < d := hfin.orderOf_pos
  have hd1 : d ≠ 1 := by
    intro h
    rw [hd, orderOf_eq_one_iff, hζ] at h
    exact hx0 (by linear_combination h)
  set q := d.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime hd1
  have hqd : q ∣ d := Nat.minFac_dvd d
  set η := ζ ^ (d / q) with hη
  have hηq : η ^ q = 1 := by
    rw [hη, ← pow_mul, Nat.div_mul_cancel hqd, hd]; exact pow_orderOf_eq_one ζ
  have hη1 : η ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · exact (Nat.div_pos (Nat.le_of_dvd hdpos hqd) hq.pos).ne'
    · exact Nat.div_lt_self hdpos hq.one_lt
  have hsum : ∑ j ∈ Finset.range q, η ^ j = 0 := by
    have h := geom_sum_mul η q
    rw [hηq, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hη1)
  have hsmall : ∀ j, ‖η ^ j - 1‖ ≤ ‖x‖ := fun j => by
    rw [hη, ← pow_mul]; exact norm_one_add_pow_sub_one_le x hx1 _
  have hqeq : (q : ℂ_[l]) = -∑ j ∈ Finset.range q, (η ^ j - 1) := by
    rw [Finset.sum_sub_distrib, hsum]; simp
  have hle : ‖(q : ℂ_[l])‖ ≤ ‖x‖ := by
    rw [hqeq, norm_neg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => hsmall j
  have := inv_le_norm_prime (l := l) q hq
  linarith

theorem exists_one_add_pow_mul_not_root : ∀ (l : ℕ) [Fact l.Prime] (a : ℂ_[l]), a ≠ 0 → ∃ k : ℕ, 1 + (l : ℂ_[l]) ^ k * a ≠ 0 ∧ ∀ i : ℕ, 1 ≤ i → (1 + (l : ℂ_[l]) ^ k * a) ^ i ≠ 1 := by
  intro l _ a ha
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hnl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p, map_natCast, PadicComplex.coe_natCast] at h
    exact h
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (inv_pos.2 hl0) ha0)
    (inv_lt_one_of_one_lt₀ hl1)
  set x := (l : ℂ_[l]) ^ k * a with hxdef
  have hxn : ‖x‖ < (l : ℝ)⁻¹ := by
    rw [hxdef, norm_mul, norm_pow, hnl]
    exact (lt_div_iff₀ ha0).1 hk
  have hl0' : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hx0 : x ≠ 0 := mul_ne_zero (pow_ne_zero _ hl0') ha
  refine ⟨k, ?_, fun i hi => not_root x hx0 hxn i hi⟩
  intro h
  have : x = -1 := by linear_combination h
  have h1 : ‖x‖ = 1 := by rw [this, norm_neg, norm_one]
  have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  linarith

end GlobalTheory.SmallRootCl
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AdaptedBasis

variable {k M : Type} [Field k] [AddCommGroup M] [Module k M]

theorem exists_adapted_family (F : ℤ → Submodule k M) (hF : Antitone F) :
    ∀ (n : ℕ) (D : Submodule k M) [FiniteDimensional k D], Module.finrank k D = n →
    (∀ x ∈ D, ∃ a, x ∈ F a) → (∀ x ∈ D, (∀ a, x ∈ F a) → x = 0) →
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → M) (h : ι → ℤ), LinearIndependent k v ∧
      Submodule.span k (Set.range v) = D ∧ (∀ j, v j ∈ F (h j) ∧ v j ∉ F (h j + 1)) ∧
      ∀ a, D ⊓ F a ≤ Submodule.span k (v '' {j | a ≤ h j}) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ hn hex hsep
  by_cases hD : D = ⊥
  · subst hD
    refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, linearIndependent_empty_type, ?_,
      fun j => j.elim, fun a => by simp⟩
    simp
  have hne : ∃ a, D ≤ F a := by
    let b := Module.finBasis k D
    have hb : ∀ i, ∃ a, (b i : M) ∈ F a := fun i => hex _ (b i).2
    choose c hc using hb
    obtain ⟨m, hm⟩ := Finite.exists_le (fun i => OrderDual.toDual (c i))
    refine ⟨OrderDual.ofDual m, ?_⟩
    intro x hx
    have hx' : (⟨x, hx⟩ : D) ∈ Submodule.span k (Set.range b) := by
      rw [b.span_eq]; trivial
    have : (Submodule.span k (Set.range b)).map D.subtype ≤ F (OrderDual.ofDual m) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hF (hm i) (hc i)
    exact this ⟨_, hx', rfl⟩
  have hbdd : ∃ b, ∀ z, D ≤ F z → z ≤ b := by
    obtain ⟨x, hxD, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    have : ¬ ∀ a, x ∈ F a := fun h => hx0 (hsep x hxD h)
    push_neg at this
    obtain ⟨a, ha⟩ := this
    refine ⟨a, fun z hz => ?_⟩
    by_contra hlt
    exact ha (hF (le_of_not_ge hlt) (hz hxD))
  obtain ⟨a₀, ha₀, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  set D' := D ⊓ F (a₀ + 1) with hD'
  have hD'D : D' ≤ D := inf_le_left
  have hlt : D' < D := by
    refine lt_of_le_of_ne hD'D fun heq => ?_
    have : D ≤ F (a₀ + 1) := heq ▸ inf_le_right
    have := hmax _ this
    omega
  haveI : FiniteDimensional k D' := Submodule.finiteDimensional_of_le hD'D
  obtain ⟨ι, _, v, h, hli, hspan, hdeg, hfil⟩ :=
    ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) D' rfl
      (fun x hx => hex x (hD'D hx)) (fun x hx => hsep x (hD'D hx))
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl D'
  set C := C' ⊓ D with hC
  have hCD : C ≤ D := inf_le_right
  have hdisj : Disjoint D' C := hC'.disjoint.mono_right inf_le_left
  have hsup : D' ⊔ C = D := by
    rw [hC, ← sup_inf_assoc_of_le _ hD'D, hC'.sup_eq_top, top_inf_eq]
  haveI : FiniteDimensional k C := Submodule.finiteDimensional_of_le hCD
  let bC := Module.finBasis k C
  let c : Fin (Module.finrank k C) → M := fun i => (bC i : M)
  have hcli : LinearIndependent k c := bC.linearIndependent.map' C.subtype C.ker_subtype
  have hcspan : Submodule.span k (Set.range c) = C := by
    have : Set.range c = C.subtype '' Set.range bC := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, bC.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hdeg' : ∀ j, a₀ + 1 ≤ h j := by
    intro j
    by_contra hj
    push_neg at hj
    have hvj : v j ∈ D' := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    exact (hdeg j).2 (hF (show h j + 1 ≤ a₀ + 1 by omega) (Submodule.mem_inf.mp hvj).2)
  refine ⟨ι ⊕ Fin (Module.finrank k C), inferInstance, Sum.elim v c,
    Sum.elim h (fun _ => a₀), ?_, ?_, ?_, ?_⟩
  · exact hli.sum_type hcli (by rw [hspan, hcspan]; exact hdisj)
  · rw [Set.Sum.elim_range, Submodule.span_union, hspan, hcspan, hsup]
  · rintro (j | i)
    · exact hdeg j
    · refine ⟨ha₀ (hCD (bC i).2), fun hmem => ?_⟩
      have h1 : c i ∈ D' := ⟨hCD (bC i).2, hmem⟩
      have h2 : c i = 0 := (Submodule.disjoint_def.mp hdisj) _ h1 (bC i).2
      exact hcli.ne_zero i h2
  · intro a x hx
    by_cases ha : a ≤ a₀
    · have hall : {j : ι ⊕ Fin (Module.finrank k C) | a ≤ Sum.elim h (fun _ => a₀) j} = Set.univ := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rcases j with j | i
        · have := hdeg' j; simp only [Sum.elim_inl]; omega
        · simpa using ha
      rw [hall, Set.image_univ, Set.Sum.elim_range, Submodule.span_union, hspan, hcspan, hsup]
      exact hx.1
    · push_neg at ha
      have hx' : x ∈ D' ⊓ F a := ⟨⟨hx.1, hF (by omega) hx.2⟩, hx.2⟩
      refine Submodule.span_mono ?_ (hfil a hx')
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨Sum.inl j, hj, rfl⟩

end GlobalTheory.AdaptedBasis

namespace GlobalTheory.AdaptedBasis

theorem exists_adapted_basis {k M : Type} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hex : ∀ x ∈ D, ∃ a, x ∈ F a) (hsep : ∀ x ∈ D, (∀ a, x ∈ F a) → x = 0) :
    ∃ (b : Module.Basis (Fin (Module.finrank k D)) k D) (h : Fin (Module.finrank k D) → ℤ),
      (∀ j, (b j : M) ∈ F (h j) ∧ (b j : M) ∉ F (h j + 1)) ∧
      ∀ (a : ℤ) (x : D), (x : M) ∈ F a → ∀ j, b.repr x j ≠ 0 → a ≤ h j := by
  classical
  obtain ⟨ι, _, v, h, hli, hspan, hdeg, hfil⟩ :=
    exists_adapted_family F hF _ D rfl hex hsep
  let b0 : Module.Basis ι k D := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hb0 : ∀ i, (b0 i : M) = v i := fun i => by
    simp [b0, Module.Basis.span_apply]
  let e : ι ≃ Fin (Module.finrank k D) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b0).symm
  refine ⟨b0.reindex e, fun j => h (e.symm j), fun j => ?_, fun a x hx j hj => ?_⟩
  · rw [Module.Basis.reindex_apply, hb0]
    exact hdeg _
  · rw [Module.Basis.repr_reindex_apply] at hj
    have hxs : (x : M) ∈ Submodule.span k (v '' {i | a ≤ h i}) := hfil a ⟨x.2, hx⟩
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination k).mp hxs
    have hrepr : b0.repr x = l := by
      have : x = Finsupp.linearCombination k b0 l := by
        apply Subtype.ext
        have h1 := Finsupp.apply_linearCombination k D.subtype b0 l
        simp only [Submodule.subtype_apply] at h1
        have hv : (⇑D.subtype ∘ ⇑b0) = v := funext hb0
        rw [h1, hv, hlx]
      rw [this, b0.repr_linearCombination]
    rw [hrepr] at hj
    exact hl (Finsupp.mem_support_iff.mpr hj)

end GlobalTheory.AdaptedBasis
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.descent_free_module_cocycle : ∀ (A B D T : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing T] [Algebra A B] (p q : B →+* D) (q₁₂ q₂₃ q₁₃ : D →+* T) (q₃ : B →+* T), (algebraMap A B).FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (p.comp (algebraMap A B))) (CommRingCat.ofHom q₃) (CommRingCat.ofHom q₁₂) → q₂₃.comp p = q₁₂.comp q → q₂₃.comp q = q₃ → q₁₃.comp p = q₁₂.comp p → q₁₃.comp q = q₃ → ∀ (d : ℕ) (ε : Matrix (Fin d) (Fin d) D), IsUnit ε → ε.map q₁₂ * ε.map q₂₃ = ε.map q₁₃ → ∀ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => p (z i)) = ε.mulVec fun i => q (z i)) → Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  first | exact @GlobalTheory.descent_free_cocycle | exact GlobalTheory.descent_free_cocycle | (intros; apply GlobalTheory.descent_free_cocycle <;> assumption)
end
