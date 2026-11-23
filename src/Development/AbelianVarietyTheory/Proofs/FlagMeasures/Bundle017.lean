module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
import Lemmata.GeneralBFactThirdTerForm.Imports
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Pi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle001
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

section

open NumberField

namespace GlobalTheory.IntMulIntegral

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (z : K) :
    ∃ M : ℤ, M ≠ 0 ∧ IsIntegral ℤ ((M : K) * z) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint

theorem main : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V]
    [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V}, Submodule.span K (↑A : Set V) = ⊤ →
    ∀ (x : V), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • x ∈ A := by
  apply GlobalTheory.IntegerMultipleIntegral.exists_int_smul_mem <;> assumption

end GlobalTheory.IntMulIntegral
end

section

namespace GlobalTheory.SmulMemSpan

theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V) (hL : Submodule.IsFullLattice K L) (x : V) :
    ∃ (r : NumberField.RingOfIntegers K), r ≠ (0 : NumberField.RingOfIntegers K) ∧ r • x ∈ L := by
  apply Bl.general_b_fact_third_ter_form.goal1 <;> assumption

end GlobalTheory.SmulMemSpan
end

section

open GlobalTheory.SgAlg Matrix

namespace GlobalTheory.SgAlg

theorem isField_or_exists_idempotent_of_isQA {E : Type} [CommRing E] (σ : E →+* E) (h : IsQA σ) :
    IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  obtain ⟨hinv, ⟨x₀, hx₀⟩, hred, -, hunit⟩ := h
  by_cases hN : ∀ y : E, y ≠ 0 → y * σ y ≠ 0
  · left
    refine ⟨⟨σ x₀, x₀, hx₀⟩, mul_comm, ?_⟩
    intro y hy
    have hfix : σ (y * σ y) = y * σ y := by
      rw [map_mul, hinv, mul_comm]
    obtain ⟨u, hu⟩ := hunit _ hfix (hN y hy)
    refine ⟨σ y * (↑u⁻¹ : E), ?_⟩
    rw [← mul_assoc, ← hu]
    exact u.mul_inv
  · right
    push Not at hN
    obtain ⟨y, hy, hyy⟩ := hN
    have hsfix : σ (y + σ y) = y + σ y := by
      rw [map_add (f := _), hinv, add_comm]
    have hs : y + σ y ≠ 0 := by
      intro h0
      have h1 : σ y = -y := eq_neg_of_add_eq_zero_right h0
      rw [h1] at hyy
      have h2 : y ^ 2 = 0 := by
        have : y * y = 0 := by simpa using hyy
        rw [pow_two, this]
      exact hy (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
    obtain ⟨s, hs'⟩ := hunit _ hsfix hs
    have hsum : (↑s⁻¹ : E) * (y + σ y) = 1 := by rw [← hs', Units.inv_mul]
    have hσs : σ (↑s⁻¹ : E) * (y + σ y) = 1 := by
      have : σ ((↑s⁻¹ : E) * (y + σ y)) = 1 := by
        rw [hsum, map_one]
      rwa [map_mul, hsfix] at this
    have hσs' : σ (↑s⁻¹ : E) = ↑s⁻¹ := by
      calc σ (↑s⁻¹ : E) = σ (↑s⁻¹ : E) * ((y + σ y) * ↑s⁻¹) := by
            rw [mul_comm (y + σ y), hsum, mul_one]
        _ = ↑s⁻¹ := by rw [← mul_assoc, hσs, one_mul]
    set e : E := y * ↑s⁻¹ with he
    have hσe : σ e = σ y * ↑s⁻¹ := by rw [he, map_mul, hσs']
    have hadd : e + σ e = 1 := by
      rw [hσe, he, ← add_mul, mul_comm]; exact hsum
    have horth : e * σ e = 0 := by
      rw [hσe, he]
      calc y * ↑s⁻¹ * (σ y * ↑s⁻¹) = (y * σ y) * (↑s⁻¹ * ↑s⁻¹) := by ring
        _ = 0 := by rw [hyy, zero_mul]
    have hidem : e * e = e := by
      have : e * (e + σ e) = e := by rw [hadd, mul_one]
      rwa [mul_add, horth, add_zero] at this
    refine ⟨e, hidem, hadd, ?_⟩
    intro x hx
    have hufix : σ (e * x + σ (e * x)) = e * x + σ (e * x) := by
      rw [map_add (f := _), hinv, add_comm]
    have heu : e * (e * x + σ (e * x)) = e * x := by
      rw [map_mul, mul_add, ← mul_assoc, hidem, ← mul_assoc, horth, zero_mul, add_zero]
    have hu0 : e * x + σ (e * x) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at heu
      exact hx heu.symm
    obtain ⟨u, hu⟩ := hunit _ hufix hu0
    refine ⟨↑u⁻¹, ?_⟩
    rw [← heu, ← hu, mul_assoc, u.mul_inv, mul_one]

end GlobalTheory.SgAlg
end

section

noncomputable section
open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt.Transport

variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma apply_out_mk_eq_of_invariant {B : AddSubgroup W} {φ : W → ℂ}
    (hφ : ∀ w b, b ∈ B → φ (w + b) = φ w) (y : W) :
    φ (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) = φ y := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) : W ⧸ B) =
      QuotientAddGroup.mk y := Quotient.out_eq _
  rw [QuotientAddGroup.eq] at h
  have := hφ (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) _ h
  rw [add_neg_cancel_left] at this
  exact this.symm

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma Fine_map_addEquiv_and_finsum_eq (e : W ≃+ W') {A B : AddSubgroup W}
    {φ : W' → ℂ} (hB : _root_.GlobalTheory.IdxInt.Fine A (fun w => φ (e w)) B) :
    _root_.GlobalTheory.IdxInt.Fine (A.map e.toAddMonoidHom) φ (B.map e.toAddMonoidHom) ∧
      (∑ᶠ c : W' ⧸ B.map e.toAddMonoidHom, φ (Quotient.out c)) =
        ∑ᶠ c : W ⧸ B, φ (e (Quotient.out c)) := by
  obtain ⟨hBA, hBi, hφ, hsupp⟩ := hB
  have hφ' : ∀ w b, b ∈ B.map e.toAddMonoidHom → φ (w + b) = φ w := by
    rintro w _ ⟨b, hb, rfl⟩
    have := hφ (e.symm w) b hb
    simpa using this
  let q : W ⧸ B ≃+ W' ⧸ B.map e.toAddMonoidHom := QuotientAddGroup.congr _ _ e rfl
  have hq : ∀ y : W, q (QuotientAddGroup.mk y) = QuotientAddGroup.mk (e y) := fun _ => rfl
  refine ⟨⟨AddSubgroup.map_mono hBA, ?_, hφ', ?_⟩, ?_⟩
  · rw [AddSubgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hBi
  · refine (hsupp.image q).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨QuotientAddGroup.mk (e.symm y), ⟨e.symm y, by simpa using hy, rfl⟩, ?_⟩
    rw [hq, AddEquiv.apply_symm_apply]
  · rw [← finsum_comp_equiv q.toEquiv]
    refine finsum_congr fun c => ?_
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    change φ (Quotient.out (q (QuotientAddGroup.mk y))) = _
    rw [hq, apply_out_mk_eq_of_invariant hφ', apply_out_mk_eq_of_invariant (φ := fun w => φ (e w)) hφ]

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma map_symm_map_addEquiv (e : W ≃+ W') (A : AddSubgroup W) :
    (A.map e.toAddMonoidHom).map e.symm.toAddMonoidHom = A := by
  ext x
  simp

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma Fine_of_le_and_finsum_eq_relIndex_mul {A B C : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex B ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ C ∧
      (∑ᶠ c : W ⧸ C, φ (Quotient.out c)) =
        (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ (Quotient.out c) := by
  obtain ⟨hBA, hBi, hφ, hsupp⟩ := hB
  haveI : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hC
  let e := AddSubgroup.quotientEquivProdOfLE hCB
  have he : ∀ y : W, (e (QuotientAddGroup.mk y)).1 = QuotientAddGroup.mk y := fun _ => rfl
  have hφC : ∀ w b, b ∈ C → φ (w + b) = φ w := fun w b hb => hφ w b (hCB hb)
  have hcomp : ∀ x : W ⧸ C, φ (Quotient.out x) = φ (Quotient.out (e x).1) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [he, apply_out_mk_eq_of_invariant hφC, apply_out_mk_eq_of_invariant hφ]
  set T : Set (W ⧸ B) := (fun w : W => (w : W ⧸ B)) '' Function.support φ with hT
  have hgT : Function.support (fun c : W ⧸ B => φ (Quotient.out c)) ⊆ T := by
    intro c hc
    refine ⟨Quotient.out c, hc, ?_⟩
    exact Quotient.out_eq c
  refine ⟨⟨hCB.trans hBA, ?_, hφC, ?_⟩, ?_⟩
  · rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA]
    exact mul_ne_zero hC hBi
  · refine ((hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
      e.injective.injOn).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, Set.mem_univ _⟩
    rw [he]
    exact ⟨y, hy, rfl⟩
  · rw [finsum_congr hcomp,
      finsum_comp_equiv e (f := fun p : (W ⧸ B) × (B ⧸ C.addSubgroupOf B) => φ (Quotient.out p.1))]
    rw [finsum_curry _ ?_]
    · haveI := Fintype.ofFinite (B ⧸ C.addSubgroupOf B)
      simp only [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_finsum]
      congr 1
      funext a
      rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
    · exact (hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).subset
        fun p hp => ⟨hgT hp, Set.mem_univ _⟩

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma finsum_out_div_relIndex_eq_inf_of_fine {A B₁ B₂ : AddSubgroup W} {φ : W → ℂ}
    (h₁ : _root_.GlobalTheory.IdxInt.Fine A φ B₁) (h₂ : _root_.GlobalTheory.IdxInt.Fine A φ B₂) :
    (∑ᶠ c : W ⧸ B₁, φ (Quotient.out c)) / (B₁.relIndex A : ℂ) =
      (∑ᶠ c : W ⧸ (B₁ ⊓ B₂), φ (Quotient.out c)) / ((B₁ ⊓ B₂).relIndex A : ℂ) := by
  have hle : B₁ ⊓ B₂ ≤ B₁ := inf_le_left
  have hprod := AddSubgroup.relIndex_mul_relIndex (B₁ ⊓ B₂) B₁ A hle h₁.1
  have hA : (B₁ ⊓ B₂).relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h₁.2.1 h₂.2.1
  have hi : (B₁ ⊓ B₂).relIndex B₁ ≠ 0 := by
    rw [← hprod] at hA
    exact left_ne_zero_of_mul hA
  rw [(Fine_of_le_and_finsum_eq_relIndex_mul h₁ hle hi).2, ← hprod, Nat.cast_mul,
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hi)]

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma cint_eq_finsum_div_relIndex_of_fine {A B : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) :
    _root_.GlobalTheory.IdxInt.cint A φ = (∑ᶠ c : W ⧸ B, φ (Quotient.out c)) / (B.relIndex A : ℂ) := by
  have hnice : _root_.GlobalTheory.IdxInt.Nice A φ := ⟨B, hB⟩
  unfold _root_.GlobalTheory.IdxInt.cint
  rw [dite_eq_left hnice, finsum_out_div_relIndex_eq_inf_of_fine hnice.choose_spec hB,
    finsum_out_div_relIndex_eq_inf_of_fine hB hnice.choose_spec, inf_comm]

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma Fine_inf_of_relIndex_ne_zero {A A' B : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (h₂ : A'.relIndex A ≠ 0) (h₁ : A.relIndex A' ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ (B ⊓ A') ∧ _root_.GlobalTheory.IdxInt.Fine A' φ (B ⊓ A') := by
  have hBA : B ≤ A := hB.1
  have hCA : (B ⊓ A').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 h₂
  have hi : (B ⊓ A').relIndex B ≠ 0 := by
    have h := hCA
    rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') B A inf_le_left hBA] at h
    exact left_ne_zero_of_mul h
  have hfine := (Fine_of_le_and_finsum_eq_relIndex_mul hB inf_le_left hi).1
  refine ⟨hfine, inf_le_right, ?_, hfine.2.2⟩
  have hCD : B ⊓ A' ≤ A ⊓ A' := inf_le_inf_right A' hBA
  have hD : (B ⊓ A').relIndex (A ⊓ A') ≠ 0 := by
    have h := hCA
    rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left] at h
    exact left_ne_zero_of_mul h
  rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A' hCD inf_le_right,
    AddSubgroup.inf_relIndex_right]
  exact mul_ne_zero hD h₁


open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
theorem _root_.GlobalTheory.IdxInt.Transport.cint_map_and_change : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (_root_.GlobalTheory.IdxInt.Nice (A.map e.toAddMonoidHom) φ ↔ _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w))) ∧ _root_.GlobalTheory.IdxInt.cint (A.map e.toAddMonoidHom) φ = _root_.GlobalTheory.IdxInt.cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (_root_.GlobalTheory.IdxInt.Nice A φ ↔ _root_.GlobalTheory.IdxInt.Nice A' φ) ∧ _root_.GlobalTheory.IdxInt.cint A' φ * (A.relIndex A' : ℂ) = _root_.GlobalTheory.IdxInt.cint A φ * (A'.relIndex A : ℂ) := by
  intro W _ W' _
  refine ⟨fun e A φ => ?_, fun A A' φ h₁ h₂ => ?_⟩
  · have hiff : _root_.GlobalTheory.IdxInt.Nice (A.map e.toAddMonoidHom) φ ↔
        _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w)) := by
      constructor
      · rintro ⟨B', hB'⟩
        have hB'' : _root_.GlobalTheory.IdxInt.Fine (A.map e.toAddMonoidHom)
            (fun w => (fun w => φ (e w)) (e.symm w)) B' := by simpa using hB'
        have h := (Fine_map_addEquiv_and_finsum_eq e.symm (φ := fun w => φ (e w)) hB'').1
        rw [map_symm_map_addEquiv] at h
        exact ⟨_, h⟩
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_map_addEquiv_and_finsum_eq e hB).1⟩
    refine ⟨hiff, ?_⟩
    by_cases hN : _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w))
    · obtain ⟨B, hB⟩ := hN
      rw [cint_eq_finsum_div_relIndex_of_fine hB, cint_eq_finsum_div_relIndex_of_fine (Fine_map_addEquiv_and_finsum_eq e hB).1,
        (Fine_map_addEquiv_and_finsum_eq e hB).2, AddSubgroup.relIndex_map_map_of_injective _ _ e.injective]
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dite_eq_right hN, dite_eq_right (hiff.not.mpr hN)]
  · have hiff : _root_.GlobalTheory.IdxInt.Nice A φ ↔ _root_.GlobalTheory.IdxInt.Nice A' φ := by
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_inf_of_relIndex_ne_zero hB h₂ h₁).2⟩
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_inf_of_relIndex_ne_zero hB h₁ h₂).2⟩
    refine ⟨hiff, ?_⟩
    by_cases hN : _root_.GlobalTheory.IdxInt.Nice A φ
    · obtain ⟨B, hB⟩ := hN
      have hC := Fine_inf_of_relIndex_ne_zero hB h₂ h₁
      have hCD : B ⊓ A' ≤ A ⊓ A' := inf_le_inf_right A' hB.1
      have hD : (B ⊓ A').relIndex (A ⊓ A') ≠ 0 := by
        have h := hC.1.2.1
        rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left] at h
        exact left_ne_zero_of_mul h
      rw [cint_eq_finsum_div_relIndex_of_fine hC.1, cint_eq_finsum_div_relIndex_of_fine hC.2,
        ← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A' hCD inf_le_right,
        ← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left,
        AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_left]
      have hD' : ((B ⊓ A').relIndex (A ⊓ A') : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
      have h₁' : (A.relIndex A' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h₁
      have h₂' : (A'.relIndex A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h₂
      push_cast
      field_simp
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dite_eq_right hN, dite_eq_right (hiff.not.mp hN)]
      simp

end GlobalTheory.IdxInt.Transport
end
end

section

namespace GlobalTheory.SumRefinement

theorem finsum_fst {X F : Type} [Finite F] (g : X → ℂ) (hg : (Function.support g).Finite) :
    ∑ᶠ p : X × F, g p.1 = (Nat.card F : ℂ) * ∑ᶠ x, g x := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  rw [finsum_eq_sum_of_support_subset (s := hg.toFinset ×ˢ Finset.univ) _ ?_,
    finsum_eq_sum_of_support_subset (s := hg.toFinset) _ (by simp),
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · intro p hp
    simp only [Function.mem_support] at hp
    simp [hp]

theorem sum_refine {W : Type} [AddCommGroup W] {A B C : AddSubgroup W} {φ : W → ℂ}
    (h : GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hi : AddSubgroup.relIndex C B ≠ 0) :
    ∑ᶠ (c : W ⧸ C), φ (Quotient.out c) =
      (AddSubgroup.relIndex C B : ℂ) * ∑ᶠ (c : W ⧸ B), φ (Quotient.out c) := by
  classical
  obtain ⟨-, -, hinv, hfin⟩ := h
  set e := AddSubgroup.quotientEquivProdOfLE hCB with he
  have hfst : ∀ x : W ⧸ C, (e x).1 = (QuotientAddGroup.mk (Quotient.out x) : W ⧸ B) := by
    intro x
    conv_lhs => rw [← Quotient.out_eq' x]
    rfl
  have hcong : ∀ u v : W, (QuotientAddGroup.mk u : W ⧸ B) = QuotientAddGroup.mk v → φ u = φ v := by
    intro u v huv
    have hb : -u + v ∈ B := QuotientAddGroup.eq.1 huv
    have h1 := hinv u (-u + v) hb
    rw [add_neg_cancel_left] at h1
    exact h1.symm
  have hval : ∀ x : W ⧸ C, φ (Quotient.out x) = φ (Quotient.out (e x).1) := by
    intro x
    rw [hfst]
    exact hcong _ _ (QuotientAddGroup.out_eq' _).symm
  have : Finite (↥B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hi
  have hg : (Function.support fun b : W ⧸ B => φ (Quotient.out b)).Finite := by
    refine hfin.subset ?_
    intro b hb
    exact ⟨Quotient.out b, hb, QuotientAddGroup.out_eq' b⟩
  rw [← finsum_comp_equiv e.symm]
  simp_rw [hval, Equiv.apply_symm_apply]
  rw [finsum_fst (fun b : W ⧸ B => φ (Quotient.out b)) hg]
  rfl

end GlobalTheory.SumRefinement
end

section

open scoped Classical

namespace GlobalTheory.GramCount

private lemma ncard_preimage_surjective_eq {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (hs : Function.Surjective φ) (m n : ℕ)
    (T : Set (Fin m → Fin n → B)) :
    Set.ncard {x : Fin m → Fin n → A | (fun a i => φ (x a i)) ∈ T} =
      Nat.card {u : A // φ u = 0} ^ (n * m) * Set.ncard T := by
  have hσ : ∀ b, φ (Function.surjInv hs b) = b := Function.surjInv_eq hs

  let E : (Fin m → Fin n → A) ≃ (Fin m → Fin n → B) × (Fin m → Fin n → {u : A // φ u = 0}) :=
    { toFun := fun x => (fun a i => φ (x a i),
        fun a i => ⟨x a i - Function.surjInv hs (φ (x a i)), by rw [map_sub, hσ, sub_self]⟩)
      invFun := fun q a i => Function.surjInv hs (q.1 a i) + (q.2 a i).1
      left_inv := fun x => by funext a i; simp
      right_inv := fun q => by
        obtain ⟨q1, q2⟩ := q
        refine Prod.ext ?_ ?_
        · funext a i; simp [hσ, (q2 a i).2]
        · funext a i; apply Subtype.ext; simp [hσ, (q2 a i).2] }
  have e2 : {x : Fin m → Fin n → A | (fun a i => φ (x a i)) ∈ T} ≃
      T × (Fin m → Fin n → {u : A // φ u = 0}) :=
    (E.subtypeEquiv (p := fun x : Fin m → Fin n → A => (fun a i => φ (x a i)) ∈ T)
      (q := fun q : (Fin m → Fin n → B) × (Fin m → Fin n → {u : A // φ u = 0}) => q.1 ∈ T)
      (fun x => Iff.rfl)).trans Equiv.prodSubtypeFstEquivSubtypeProd
  simp only [← Nat.card_coe_set_eq]
  rw [Nat.card_congr e2, Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin]
  ring

theorem ncard_gram_mod_eq_card_ker_pow_mul {A B : Type} [CommRing A] [Finite A] [CommRing B]
    (c : A →+* A) (c' : B →+* B) (hc : ∀ u, c (c u) = u) (p : A) (hp : IsNilpotent p)
    (φ : A →+* B) (hs : Function.Surjective φ) (hφ : ∀ u, φ (c u) = c' (φ u))
    (hk : ∀ u, φ u = 0 ↔ p ∣ u) (m n : ℕ) (G : Matrix (Fin m) (Fin m) A) :
    Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} =
      Nat.card {u : A // p ∣ u} ^ (n * m) * Set.ncard (sols c' n (G.map φ)) := by
  have hk' : ∀ u, φ u = 0 → IsUnit (1 + u) := fun u hu => by
    obtain ⟨v, rfl⟩ := (hk u).1 hu
    exact (Commute.all p v).isNilpotent_mul_right hp |>.isUnit_one_add

  have hset : {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} =
      {x | (fun a i => φ (x a i)) ∈ sols c' n (G.map φ)} := by
    ext x
    simp only [Set.mem_setOf_eq, sols]
    constructor
    · rintro ⟨hx, hG⟩
      refine ⟨Prim.map c c' φ hφ hx, fun a b => ?_⟩
      have h := (hk _).2 (hG a b)
      rw [map_sub, map_ip c c' φ hφ] at h
      simpa [Matrix.map_apply, sub_eq_zero] using h
    · rintro ⟨hx, hG⟩
      refine ⟨prim_of_map c hc c' φ hφ hs hk' hx, fun a b => (hk _).1 ?_⟩
      have h := hG a b
      simp only [Matrix.map_apply] at h
      rw [map_sub, map_ip c c' φ hφ, h, sub_self]
  rw [hset, ncard_preimage_surjective_eq φ hs m n, Nat.card_congr (Equiv.subtypeEquivRight hk)]

end GlobalTheory.GramCount
end

section


theorem _root_.GlobalTheory.T.sum_prod_fixed_place_average_alt : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] {V : Type} [AddCommGroup V] [Module ℂ V] (a : ∀ i, G i → ℂ) (f : (∀ i, G i) → V), (∀ i (γ : ∀ i, G i), γ i = 1 → ∑ β : G i, a i β • f (Function.update γ i β) = f γ) → ∑ γ : (∀ i, G i), (∏ i, a i (γ i)) • f γ = f 1 := by
  first | exact @GlobalTheory.sum_prod_fixed_place_average | exact GlobalTheory.sum_prod_fixed_place_average | (intros; apply GlobalTheory.sum_prod_fixed_place_average <;> assumption)
end
