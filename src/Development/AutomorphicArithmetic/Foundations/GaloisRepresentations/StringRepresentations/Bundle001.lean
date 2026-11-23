module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.GaloisStatementWeakOfFull
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace UpperTheory.GalN

open GlobalTheory

theorem OpenB.exp_eq {q : ℕ} {α : ℂ} (h : OpenB q α) (hq : 1 < q) {x y : ℝ} (e : ‖α‖ * (q : ℝ) ^ x = (q : ℝ) ^ y)
    (m : ℤ) (hm : y - x = (m : ℝ) / 2) : x = y := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have e2 : ‖α‖ = (q : ℝ) ^ (y - x) := by
    rw [Real.rpow_sub hq0, ← e, mul_div_assoc, div_self (Real.rpow_pos_of_pos hq0 x).ne', mul_one]
  obtain ⟨h1, h2⟩ := h
  rw [e2, Real.rpow_lt_rpow_left_iff hq1, hm] at h1 h2
  have a1 : (-1 : ℤ) < m := by
    have : ((-1 : ℤ) : ℝ) < m := by push_cast; linarith
    exact_mod_cast this
  have a2 : m < 1 := by
    have : (m : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have : m = 0 := by omega
  rw [this] at hm
  simp at hm
  linarith

theorem OpenB.inv {q : ℕ} {α : ℂ} (h : OpenB q α) (hq : 1 < q) : OpenB q α⁻¹ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hp : (0 : ℝ) < (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hq0 _
  obtain ⟨h1, h2⟩ := h
  rw [Real.rpow_neg hq0.le] at h1
  have h0 : 0 < ‖α‖ := (inv_pos.2 hp).trans h1
  rw [OpenB, norm_inv, Real.rpow_neg hq0.le]
  exact ⟨(inv_lt_inv₀ hp h0).2 h2, (inv_lt_comm₀ h0 hp).2 h1⟩

theorem OpenB.le_rpow {q : ℕ} {α : ℂ} (h : OpenB q α) (hq : 1 < q) {x : ℝ} (hx : 1 / 2 ≤ x) : ‖α‖ ≤ (q : ℝ) ^ x :=
  h.2.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.le) hx)

theorem string_count :
    ∀ (q t : ℕ) (L : List (ℕ × Multiset ℂ)) (Rw : Multiset ℂ) (c : ℂ), 1 < q → 1 ≤ t → ‖c‖ = 1 → (∀ x ∈ Rw, ‖x‖ < (q : ℝ) ^ (((t : ℝ) - 1) / 2)) → (∀ e ∈ L, 1 ≤ e.1 ∧ e.2 ≠ 0 ∧ (∀ α ∈ e.2, OpenB q α) ∧ (t ≤ e.1 → ∀ α ∈ e.2, ‖α‖ = 1)) → (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum = Rw + ((List.range t).map fun k => ({c * (q : ℂ) ^ (((((t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum → (∃ e ∈ L, t ≤ e.1) ∧ ∀ e ∈ L, t ≤ e.1 → e.1 = t ∧ e.2 = {c} := by
  intro q t L Rw c hq ht hc hRw hL hsum
  have hq0 : 0 < q := by omega
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  have nm : ∀ s : ℝ, ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s := norm_natCast_cpow_ofReal hq0
  have Pne : ∀ s : ℝ, (q : ℂ) ^ ((s : ℝ) : ℂ) ≠ 0 := by
    intro s h0
    have h := nm s
    rw [h0, norm_zero] at h
    exact (Real.rpow_pos_of_pos (by positivity) s).ne' h.symm
  simp only [bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def] at hsum
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hright : ((List.range (n+1)).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - (k : ℝ) : ℝ) : ℂ)} : Multiset ℂ)).sum
      = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum := by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    congr 2
    · simp
    · apply List.map_congr_left
      intro k _
      simp
  rw [hright] at hsum
  have hsmall : ∀ x ∈ Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum,
      ‖x‖ < (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2) := by
    intro x hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact hRw x hx
    · obtain ⟨m, hm, hxm⟩ := (multiset_mem_list_sum' _ _).1 hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hm
      rw [Multiset.mem_singleton] at hxm
      subst hxm
      rw [norm_mul, hc, nm, one_mul]
      exact Real.rpow_lt_rpow_of_exponent_lt hq1 (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hsum' : (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum
      = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum) := by
    rw [hsum, add_left_comm]
  clear hsum hright
  constructor
  · have hmem := hsum' ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self _))
    obtain ⟨m, hm, hxm⟩ := (multiset_mem_list_sum' _ _).1 hmem
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    obtain ⟨m', hm', hxm'⟩ := (multiset_mem_list_sum' _ _).1 hxm
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hm'
    obtain ⟨α, hα, hαeq⟩ := Multiset.mem_map.1 hxm'
    have hn := congrArg norm hαeq
    rw [norm_mul, norm_mul, hc, nm, nm, one_mul] at hn
    have hx : ((e.1 : ℝ) - 1) / 2 - (k : ℝ) = (((n + 1 : ℕ) : ℝ) - 1) / 2 :=
      ((hL e he).2.2.1 α hα).exp_eq hq hn ((n : ℤ) + 1 - e.1 + 2 * k) (by push_cast; ring)
    refine ⟨e, he, ?_⟩
    have : ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ) := by
      have hk : (0:ℝ) ≤ k := by positivity
      push_cast at hx ⊢
      linarith
    exact_mod_cast this
  · intro e he hte
    obtain ⟨hd1, hE0, -, hEn⟩ := hL e he
    replace hEn := hEn hte
    have hle : e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ))
        ≤ {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum) := by
      rw [← hsum']
      refine (multiset_le_list_sum' ((List.range e.1).map fun (k : ℕ) => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))) _ ?_).trans (multiset_le_list_sum' _ _ ?_)
      · exact List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩
      · exact List.mem_map.2 ⟨e, he, rfl⟩
    have h1 := Multiset.filter_le_filter (fun x : ℂ => (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2) ≤ ‖x‖) hle
    rw [Multiset.filter_eq_self.2, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => not_le.2 (hsmall x hx)), add_zero] at h1
    swap
    · intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      rw [norm_mul, hEn α hα, nm, one_mul]
      apply Real.rpow_le_rpow_of_exponent_le hq1.le
      have : ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ) := by exact_mod_cast hte
      push_cast at this ⊢
      linarith
    have h2 := h1.trans (Multiset.filter_le _ _)
    have hcard : Multiset.card ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} : Multiset ℂ) ≤ Multiset.card (e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ))) := by
      rw [Multiset.card_singleton, Multiset.card_map]
      exact Multiset.card_pos.2 hE0
    have h3 := Multiset.eq_of_le_of_card_le h2 hcard
    obtain ⟨α, hEα, hαeq⟩ := Multiset.map_eq_singleton.1 h3
    have hα : α ∈ e.2 := by rw [hEα]; exact Multiset.mem_singleton_self _
    have hn := congrArg norm hαeq
    rw [norm_mul, norm_mul, hEn α hα, hc, nm, nm, one_mul, one_mul] at hn
    have hx := rpow_exponent_inj_of_one_lt hq1 hn
    have hd : e.1 = n + 1 := by
      have : (e.1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by push_cast at hx ⊢; linarith
      exact_mod_cast this
    refine ⟨hd, ?_⟩
    rw [hEα]
    congr 1
    simp only [hd, Nat.cast_zero, sub_zero] at hαeq
    exact mul_right_cancel₀ (Pne _) hαeq

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem one_lt_q (w : PlE H) : 1 < normV w := by
  haveI : Finite (𝓞 H.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 H.E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  show 1 < Nat.card (𝓞 H.E ⧸ w.asIdeal)
  exact Finite.one_lt_card

theorem half_le_r (R : Ranks) : (1 / 2 : ℝ) ≤ ((R.r : ℝ) - 1) / 2 := by
  have : 2 ≤ R.r := by
    have h1 := R.two_le_m
    have h2 := R.m_add_three_le_k
    show 2 ≤ R.k + R.m - 1
    omega
  have h' : (2 : ℝ) ≤ R.r := by exact_mod_cast this
  linarith

theorem TempAt.part {a : ℕ} {π : A.CG a} {w : PlE H} (h : TempAt N A π w) (hu : A.unr (A.locG π w)) :
    ∀ α ∈ A.frobEig (A.locG π w), OpenB (normV w) α ∧ (a = 1 → ‖α‖ = 1) :=
  fun α hα => ⟨h.2 hu α hα, fun e => (A.tempered_unr _ hu).1 (h.1 e) α hα⟩

theorem TempAt.part_tw (hAut : TieAut N A) {a : ℕ} {π : A.CG a} {w : PlE H} (h : TempAt N A (A.tw π A.etaT) w)
    (hu : A.unr (A.locG π w)) : ∀ α ∈ A.frobEig (A.locG π w), OpenB (normV w) α ∧ (a = 1 → ‖α‖ = 1) := by
  intro α hα
  have hd := A.locG_dim A.etaT w
  have heu := A.etaT_unr w
  obtain ⟨e, he⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ heu).trans hd)
  have hen : ‖e‖ = 1 := (A.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; simp)
  have k := h.part (by rw [A.locG_tw]; exact A.unr_char _ _ hd hu heu) (α * e) (by
    rw [A.locG_tw, A.frobEig_char _ _ e hu heu hd he]
    exact Multiset.mem_map_of_mem _ hα)
  exact ⟨k.1.of_mul hen, fun e1 => by simpa [hen] using k.2 e1⟩

theorem rank_one_of_long {Pa : List (Part A.CG)} (hr : rankIso N A Pa = R.nV) {p : Part A.CG} (hp : p ∈ Pa)
    (ha : 1 ≤ p.a) (ht : R.t ≤ p.d) : p.a = 1 := by
  have h1 : p.a * p.d ≤ rankIso N A Pa :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (f := fun p : Part A.CG => p.a * p.d) hp)
  have h2 : R.r + 5 ≤ R.t := R.rank_add_five_le
  rw [hr, Ranks.nV] at h1
  by_contra hne
  have h3 : 2 * R.t ≤ p.a * p.d := Nat.mul_le_mul (by omega) ht
  omega

end UpperTheory.GalN
end
end

section

noncomputable section

namespace UpperTheory.GalN

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At UpperTheory.Lit.Car

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def Spl {w : PlE H} (c : G H.E N.Om → ℂ) (t : ℕ) (y : A.LP w) : Prop :=
  ∃ a b : A.LP w, y = A.lpSum a b ∧ A.lpDim b = t ∧ A.mono0 b ∧
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (c σ)) ^ t

structure RelW {w : PlE H} (x y : A.LP w) : Prop where
  dim : A.lpDim x = A.lpDim y
  ine : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol x σ = A.inePol y σ
  n0 : A.mono0 y → x = y
  spl : ∀ (u : A.LP w) (c : G H.E N.Om → ℂ) (t : ℕ), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
    (A.inePol (A.lpSum y u) γ).rootMultiplicity (c γ) ≤ t → Spl N A c t (A.lpSum y u) → Spl N A c t (A.lpSum x u)

structure RelA {w : PlE H} (x y : A.LP w) : Prop where
  dim : A.lpDim x = A.lpDim y
  mono : A.mono0 y → A.mono0 x
  ine : A.mono0 y ∧ IneAb N A y → ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol x σ = A.inePol y σ

structure CuspA {w : PlE H} (x y : A.LP w) : Prop where
  rel : RelA N A x y
  one : A.lpDim y = 1 → x = y

variable {N A}

theorem RelA.refl {w : PlE H} (x : A.LP w) : RelA N A x x := ⟨rfl, id, fun _ _ _ => rfl⟩

private theorem commutator_le_self' {G : Type*} [Group G] (K : Subgroup G) : ⁅K, K⁆ ≤ K :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

theorem RelA.unr {w : PlE H} {x y : A.LP w} (h : RelA N A x y) (hy : A.unr y) : A.unr x := by
  obtain ⟨hm, hi⟩ := (A.unr_iff_ine y).mp hy
  refine (A.unr_iff_ine x).mpr ⟨h.mono hm, fun σ hσ => ?_⟩
  rw [h.ine ⟨hm, fun τ hτ => hi τ (commutator_le_self' _ hτ)⟩ σ hσ, hi σ hσ, h.dim]

private theorem eq_X_sub_one_pow_of_monic_mul_eq {p q : ℂ[X]} {n m : ℕ} (hp : p.Monic) (hpn : p.natDegree = n)
    (h : p * q = (X - 1) ^ (n + m)) : p = (X - 1) ^ n := by
  have hd : p ∣ (X - C 1) ^ (n + m) := ⟨q, by simpa using h.symm⟩
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) _).mp hd
  have he : p = (X - C 1) ^ i :=
    Polynomial.eq_of_monic_of_associated hp ((Polynomial.monic_X_sub_C 1).pow i) hi
  have hin : i = n := by
    rw [← hpn, he, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  subst hin
  simpa using he

theorem RelA.sum (hLP : TieLP N A) {w : PlE H} {x y x' y' : A.LP w} (h : RelA N A x y) (h' : RelA N A x' y') :
    RelA N A (A.lpSum x x') (A.lpSum y y') := by
  have hu1 : A.lpDim (A.lpUnr w {1}) = 1 := by
    rw [(A.lpUnr_spec w {1} (by simp)).2.2]
    simp
  have hmon : ∀ (a : A.LP w) σ, σ ∈ Ine (F := H.E) (N.plOm.1 w) →
      (A.inePol a σ).Monic ∧ (A.inePol a σ).natDegree = A.lpDim a := fun a σ hσ =>
    ((hLP w a a (A.lpUnr w {1}) (A.lpUnr w {1}) 0 hu1 hu1).2.2.2.2.2 σ hσ).1
  refine ⟨by rw [A.lpDim_sum, A.lpDim_sum, h.dim, h'.dim], fun hm => ?_, fun ⟨hm, hab⟩ σ hσ => ?_⟩
  · rw [A.monomial_sum_iff] at hm ⊢
    exact ⟨h.mono hm.1, h'.mono hm.2⟩
  · rw [A.monomial_sum_iff] at hm
    have key : ∀ τ ∈ ⁅Ine (F := H.E) (N.plOm.1 w), Ine (F := H.E) (N.plOm.1 w)⁆,
        A.inePol y τ = (X - 1) ^ A.lpDim y ∧ A.inePol y' τ = (X - 1) ^ A.lpDim y' := by
      intro τ hτ
      have hτI : τ ∈ Ine (F := H.E) (N.plOm.1 w) := commutator_le_self' _ hτ
      have e := hab τ hτ
      rw [A.inePol_sum, A.lpDim_sum] at e
      refine ⟨eq_X_sub_one_pow_of_monic_mul_eq (hmon y τ hτI).1 (hmon y τ hτI).2 e, ?_⟩
      rw [mul_comm, add_comm] at e
      exact eq_X_sub_one_pow_of_monic_mul_eq (hmon y' τ hτI).1 (hmon y' τ hτI).2 e
    rw [A.inePol_sum, A.inePol_sum, h.ine ⟨hm.1, fun τ hτ => (key τ hτ).1⟩ σ hσ,
      h'.ine ⟨hm.2, fun τ hτ => (key τ hτ).2⟩ σ hσ]

theorem RelA.char (hLP : TieLP N A) {w : PlE H} {x y : A.LP w} (h : RelA N A x y) (c : A.LP w) (hc : A.lpDim c = 1)
    (hu : A.unr c) : RelA N A (A.lpChar x c) (A.lpChar y c) := by
  have hpc : ∀ τ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol c τ = X - C 1 := by
    intro τ hτ
    rw [((A.unr_iff_ine c).mp hu).2 τ hτ, hc]
    simp
  have hch : ∀ (a : A.LP w) τ, τ ∈ Ine (F := H.E) (N.plOm.1 w) →
      A.inePol (A.lpChar a c) τ = A.inePol a τ := by
    intro a τ hτ
    rw [((hLP w a a c c 0 hc hc).2.2.2.2.2 τ hτ).2 1 (hpc τ hτ), Polynomial.scaleRoots_one]
  refine ⟨by rw [A.lpDim_char _ _ hc, A.lpDim_char _ _ hc, h.dim], fun hm => ?_,
    fun ⟨hm, hab⟩ σ hσ => ?_⟩
  · rw [A.monomial_char_iff _ _ hc] at hm ⊢
    exact h.mono hm
  · rw [A.monomial_char_iff _ _ hc] at hm
    have hab' : IneAb N A y := by
      intro τ hτ
      have hτI : τ ∈ Ine (F := H.E) (N.plOm.1 w) := commutator_le_self' _ hτ
      have e := hab τ hτ
      rw [hch y τ hτI, A.lpDim_char _ _ hc] at e
      exact e
    rw [hch x σ hσ, hch y σ hσ, h.ine ⟨hm, hab'⟩ σ hσ]

theorem RelW.refl {w : PlE H} (x : A.LP w) : RelW N A x x := ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ _ _ k => k⟩

theorem RelW.of_eq {w : PlE H} {x y : A.LP w} (e : x = y) : RelW N A x y := e ▸ RelW.refl x

theorem CuspA.of_eq {w : PlE H} {x y : A.LP w} (e : x = y) : CuspA N A x y := by
  subst e
  exact ⟨RelA.refl x, fun _ => rfl⟩

theorem RelW.mono {w : PlE H} {x y : A.LP w} (h : RelW N A x y) (hy : A.mono0 y) : A.mono0 x := (h.n0 hy) ▸ hy

theorem RelW.sum {w : PlE H} {x y x' y' : A.LP w} (h : RelW N A x y) (h' : RelW N A x' y') :
    RelW N A (A.lpSum x x') (A.lpSum y y') := by
  refine ⟨by rw [A.lpDim_sum, A.lpDim_sum, h.dim, h'.dim],
    fun σ hσ => by rw [A.inePol_sum, A.inePol_sum, h.ine σ hσ, h'.ine σ hσ],
    fun k => by rw [h.n0 ((A.monomial_sum_iff _ _).1 k).1, h'.n0 ((A.monomial_sum_iff _ _).1 k).2], fun u c t γ hγ hm hs => ?_⟩
  rw [A.lpSum_assoc] at hm hs
  have s1 := h.spl _ c t γ hγ hm hs
  have e : A.lpSum x (A.lpSum y' u) = A.lpSum y' (A.lpSum x u) := by
    rw [← A.lpSum_assoc, A.lpSum_comm x y', A.lpSum_assoc]
  have hm' : (A.inePol (A.lpSum y' (A.lpSum x u)) γ).rootMultiplicity (c γ) ≤ t := by
    rw [← e, A.inePol_sum, h.ine γ hγ, ← A.inePol_sum]; exact hm
  have s2 := h'.spl _ c t γ hγ hm' (e ▸ s1)
  rwa [← A.lpSum_assoc, A.lpSum_comm x' x] at s2

theorem Spl.char (hLP : TieLP N A) {w : PlE H} {c : G H.E N.Om → ℂ} {t : ℕ} {y : A.LP w} (h : Spl N A c t y)
    (k : A.LP w) (hk : A.lpDim k = 1) (hu : A.unr k) : Spl N A c t (A.lpChar y k) := by
  obtain ⟨a, b, e, d, m, p⟩ := h
  exact ⟨A.lpChar a k, A.lpChar b k, by rw [e, (hLP w a b k k 0 hk hk).1], by rw [A.lpDim_char _ _ hk, d],
    (A.monomial_char_iff _ _ hk).2 m, fun σ hσ => by rw [inePol_char_unr hLP _ _ hk hu σ hσ, p σ hσ]⟩

theorem exists_inv_unr {w : PlE H} (k : A.LP w) (hk : A.lpDim k = 1) (hu : A.unr k) :
    ∃ k' : A.LP w, A.lpDim k' = 1 ∧ A.unr k' ∧ A.lpChar k k' = A.lpUnr w {1} ∧ A.lpChar k' k = A.lpUnr w {1} := by
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((A.frobEig_card k hu).trans hk)
  have hc0 : c ≠ 0 := fun h => A.frobEig_ne_zero k hu (by rw [hc, h]; exact Multiset.mem_singleton_self 0)
  obtain ⟨hu', hf', hd'⟩ := A.lpUnr_spec w {c⁻¹} (by simp [hc0, eq_comm])
  have hd1 : A.lpDim (A.lpUnr w {c⁻¹}) = 1 := by rw [hd']; simp
  refine ⟨A.lpUnr w {c⁻¹}, hd1, hu', ?_, ?_⟩
  · rw [A.unr_eq_lpUnr _ (A.unr_char _ _ hd1 hu hu'), A.frobEig_char _ _ c⁻¹ hu hu' hd1 hf', hc]
    simp [hc0]
  · rw [A.unr_eq_lpUnr _ (A.unr_char _ _ hk hu' hu), A.frobEig_char _ _ c hu' hu hk hc, hf']
    simp [hc0]

theorem RelW.char (hLP : TieLP N A) {w : PlE H} {x y : A.LP w} (h : RelW N A x y) (k : A.LP w) (hk : A.lpDim k = 1)
    (hu : A.unr k) : RelW N A (A.lpChar x k) (A.lpChar y k) := by
  refine ⟨by rw [A.lpDim_char _ _ hk, A.lpDim_char _ _ hk, h.dim],
    fun σ hσ => by rw [inePol_char_unr hLP _ _ hk hu σ hσ, inePol_char_unr hLP _ _ hk hu σ hσ, h.ine σ hσ],
    fun m => by rw [h.n0 ((A.monomial_char_iff _ _ hk).1 m)], fun u c t γ hγ hm hs => ?_⟩
  obtain ⟨k', hk', hu', e1, e2⟩ := exists_inv_unr k hk hu
  have e : ∀ z : A.LP w, A.lpSum (A.lpChar z k) u = A.lpChar (A.lpSum z (A.lpChar u k')) k := fun z => by
    rw [(hLP w z _ k k 0 hk hk).1, (hLP w u u k' k 0 hk' hk).2.2.2.1, e2, (hLP w u u k' k 0 hk' hk).2.2.2.2.1]
  rw [e] at hm hs ⊢
  rw [inePol_char_unr hLP _ _ hk hu γ hγ] at hm
  have hs' := hs.char hLP k' hk' hu'
  rw [(hLP w _ u k k' 0 hk hk').2.2.2.1, e1, (hLP w _ u k k' 0 hk hk').2.2.2.2.1] at hs'
  exact (h.spl _ c t γ hγ hm hs').char hLP k hk hu

variable (N A)

def AutomorphicGaloisAdmissible : Prop :=
  ∀ i, (∀ a, 1 ≤ a → ∀ π : A.CG a, A.csd π → A.ralg π →
      ∃ ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)),
        Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) ∧
        IsSSRep ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) →
          RelW N A (A.wdOf i ρ w) (A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2))) ∧
        (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧
          (∀ τ, InducesW N i τ w → A.jumpsW i ρ τ = A.jumpsInf i π τ) ∧
          CuspA N A (A.wdOf i ρ w) (A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2)))) ∧
    (∀ a (π : A.CG a), A.ralg π → ∃ w₀ : ℂ, ∀ τ : H.E →+* ℂ,
      A.infG π (τ.comp (H.conj : H.E ≃ₐ[ℚ] H.E).toRingEquiv.toRingHom) = (A.infG π τ).map (w₀ - ·)) ∧
    (∀ (χ : A.CG 1) (s : ℝ), (∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) →
      ∃ ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)), ContQ N i ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i ρ w = A.lpTw (A.locG χ w) s) ∧
        ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧ A.wdOf i ρ w = A.lpTw (A.locG χ w) s ∧
          ∀ τ, InducesW N i τ w → (A.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
            (A.infG χ ((A.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ))))

variable {N A}

theorem weakA' (h : AutomorphicGaloisAdmissible N A) : AutomorphicGaloisAdmissible N A := h
theorem weak' {D : D7} (h : AutomorphicGaloisAdmissible D.nd D.naut) : AutomorphicGaloisAdmissible D.nd D.naut := h

end UpperTheory.GalN
end
end
