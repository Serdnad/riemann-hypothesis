module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HfAlgSmulRight
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle029
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
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
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
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
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

@[expose] public section

section

noncomputable section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT.EEBasic

section General
variable {B : Type} [CommRing B] (b : B)

theorem pow_dvd_iff_eval (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣ x ↔
      AdicCompletion.eval (Ideal.span {b}) B k x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval
    (Submodule.fg_span_singleton b), Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton,
    map_pow]

theorem eval_algebraMap (k : ℕ) (c : B) :
    AdicCompletion.eval (Ideal.span {b}) B k (algebraMap B (AdicCompletion (Ideal.span {b}) B) c)
      = Submodule.Quotient.mk c := by
  rw [AdicCompletion.algebraMap_apply]
  rfl

theorem pow_dvd_of_pow_dvd (k : ℕ) (c : B)
    (h : (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      algebraMap B (AdicCompletion (Ideal.span {b}) B) c) : b ^ k ∣ c := by
  rw [pow_dvd_iff_eval, eval_algebraMap, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
    Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  exact h

theorem exists_pow_dvd_sub (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    ∃ c : B, (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      x - algebraMap B (AdicCompletion (Ideal.span {b}) B) c := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (Ideal.span {b}) B k x)
  exact ⟨c, by rw [pow_dvd_iff_eval, map_sub, eval_algebraMap, hc, sub_self]⟩

theorem complete : IsAdicComplete
    (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b})
    (AdicCompletion (Ideal.span {b}) B) := by
  have h : Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b} =
      (Ideal.span {b}).map (algebraMap B (AdicCompletion (Ideal.span {b}) B)) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton b)

end General

variable {O : Type} [CommRing O]

theorem C_dvd_iff (c : O) (a : O⟦X⟧) : C c ∣ a ↔ ∀ n, c ∣ coeff n a := by
  constructor
  · rintro ⟨q, rfl⟩ n
    rw [coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose q hq using h
    exact ⟨PowerSeries.mk q, PowerSeries.ext fun n => by rw [coeff_C_mul, coeff_mk, hq]⟩

theorem C_dvd_of_dvd_X_pow_mul (c : O) (m : ℕ) (a : O⟦X⟧) (h : C c ∣ X ^ m * a) : C c ∣ a := by
  rw [C_dvd_iff] at h ⊢
  intro n
  have := h (n + m)
  rwa [coeff_X_pow_mul] at this

theorem C_dvd_of_dvd_away (c : O) (a : O⟦X⟧)
    (h : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c) ∣
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) : C c ∣ a := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) z
  have h1 : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (X ^ m * a) =
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c * q) := by
    rw [map_mul, map_mul, map_pow, hz, ← hq]; ring
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (X : O⟦X⟧) h1
  refine C_dvd_of_dvd_X_pow_mul c (n + m) a ⟨X ^ n * q, ?_⟩
  rw [pow_add, mul_assoc, hn]; ring

theorem algebraMap_EE (l : ℕ) (a : O⟦X⟧) : algebraMap O⟦X⟧ (EE O l) a =
    algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)
      (algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]; rfl

theorem saturated (l : ℕ) (a : O⟦X⟧) (k : ℕ)
    (h : (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a) : (l : O⟦X⟧) ^ k ∣ a := by
  rw [algebraMap_EE, ← map_natCast (algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)) l] at h
  have h2 := pow_dvd_of_pow_dvd _ k _ h
  have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
  rw [e]
  apply C_dvd_of_dvd_away
  rwa [← e, map_pow, map_natCast]

end GlobalTheory.NB.LT.EEBasic

namespace GlobalTheory.NB.LT

open EEBasic

theorem EE_basic : ∀ {l : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O], l.Prime → ¬ IsUnit (l : O) → Function.Injective (algebraMap O⟦X⟧ (EE O l)) ∧ IsUnit (algebraMap O⟦X⟧ (EE O l) X) ∧ IsAdicComplete (Ideal.span {(l : EE O l)}) (EE O l) ∧ (∀ (x : EE O l) (k : ℕ), ∃ (a : O⟦X⟧) (m : ℕ), (l : EE O l) ^ k ∣ x * algebraMap O⟦X⟧ (EE O l) (X ^ m) - algebraMap O⟦X⟧ (EE O l) a) ∧ (∀ (a : O⟦X⟧) (k : ℕ), (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a → (l : O⟦X⟧) ^ k ∣ a) := by
  intro l O _ _ _ _ _ _ hl
  refine ⟨?_, ?_, ?_, ?_, saturated l⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) inferInstance _ fun k => ?_
    have h1 := saturated l a k (by rw [ha]; exact dvd_zero _)
    have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
    rw [e, C_dvd_iff] at h1
    obtain ⟨q, hq⟩ := h1 n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hq]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).2 hl) k)
  · rw [algebraMap_EE]
    exact (IsLocalization.Away.algebraMap_isUnit (X : O⟦X⟧)).map _
  · have := complete (l : Localization.Away (X : O⟦X⟧))
    rwa [map_natCast] at this
  · intro x k
    obtain ⟨c, hc⟩ := exists_pow_dvd_sub (l : Localization.Away (X : O⟦X⟧)) k x
    rw [map_natCast] at hc
    obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) c
    refine ⟨q, m, ?_⟩
    rw [algebraMap_EE l q, ← hq, map_mul, algebraMap_EE, map_pow (algebraMap O⟦X⟧ _), ← sub_mul]
    exact hc.mul_right _

end GlobalTheory.NB.LT
end
end

section

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem isUnit_of_not_dvd {ϖ b : O} (hϖ : Irreducible ϖ) (h : ¬ ϖ ∣ b) : IsUnit b := by
  by_contra hb
  have hm : b ∈ IsLocalRing.maximalIdeal O := hb
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.mem_span_singleton] at hm
  exact h hm

theorem alg_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : algebraMap O K ϖ ≠ 0 := by
  intro h
  exact hϖ.ne_zero (IsFractionRing.injective O K (by simpa using h))

theorem exists_unit_conj (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : Oˣ, cK (algebraMap O K ϖ) = algebraMap O K u * algebraMap O K ϖ := by
  have h1 : Irreducible (c ϖ) := (MulEquiv.irreducible_iff c.toMulEquiv).2 hϖ
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible O h1 hϖ
  refine ⟨u⁻¹, ?_⟩
  have e : c ϖ = ((u⁻¹ : Oˣ) : O) * ϖ := by
    calc c ϖ = c ϖ * u * ((u⁻¹ : Oˣ) : O) := by simp [mul_assoc]
      _ = ϖ * ((u⁻¹ : Oˣ) : O) := by rw [hu]
      _ = _ := mul_comm _ _
  rw [hcK, e, map_mul]

theorem exists_ratio {ϖ : O} (hϖ : Irreducible ϖ) {β γ : K}
    (hβ : β ∉ (algebraMap O K).range) (hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range)
    (hγ : algebraMap O K ϖ * γ ∈ (algebraMap O K).range) :
    ∃ a : O, γ = algebraMap O K a * β := by
  obtain ⟨b, hb⟩ := hβ'
  obtain ⟨g, hg⟩ := hγ
  have h0 : algebraMap O K ϖ ≠ 0 := alg_ne_zero hϖ
  have hbu : IsUnit b := by
    apply isUnit_of_not_dvd hϖ
    rintro ⟨e, rfl⟩
    apply hβ
    refine ⟨e, ?_⟩
    rw [map_mul] at hb
    exact (mul_left_cancel₀ h0 hb)
  obtain ⟨u, rfl⟩ := hbu
  refine ⟨g * ((u⁻¹ : Oˣ) : O), ?_⟩
  apply mul_left_cancel₀ h0
  have e1 : algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul]; simp
  rw [← hg, map_mul]
  calc algebraMap O K g = algebraMap O K g * (algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O)) := by
        rw [e1, mul_one]
    _ = algebraMap O K g * ((algebraMap O K ϖ * β) * algebraMap O K ((u⁻¹ : Oˣ) : O)) := by rw [hb]
    _ = _ := by ring

theorem ratio_mem_iff {ϖ : O} (hϖ : Irreducible ϖ) {β : K}
    (hβ : β ∉ (algebraMap O K).range) (hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range)
    (a : O) : algebraMap O K a * β ∈ (algebraMap O K).range ↔ ϖ ∣ a := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨u, rfl⟩ := isUnit_of_not_dvd hϖ hd
    apply hβ
    have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul]; simp
    have : β = algebraMap O K ((u⁻¹ : Oˣ) : O) * (algebraMap O K (u : O) * β) := by
      rw [← mul_assoc, e1, one_mul]
    rw [this]
    exact mul_mem ⟨_, rfl⟩ h
  · rintro ⟨e, rfl⟩
    rw [map_mul, mul_comm (algebraMap O K ϖ), mul_assoc]
    exact mul_mem ⟨_, rfl⟩ hβ'

theorem mul_pair_mem (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K} (hw : ϖ • v ∈ L)
    {l : Fin r → K} (hl : l ∈ L) :
    algebraMap O K ϖ * hf cK J v l ∈ (algebraMap O K).range := by
  obtain ⟨u, hu⟩ := exists_unit_conj c cK hcK (K := K) hϖ
  have h1 := (hSD _).1 hw l hl
  rw [hf_algSmul_left, hu] at h1
  have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
    rw [← map_mul]; simp
  have : algebraMap O K ϖ * hf cK J v l = algebraMap O K ((u⁻¹ : Oˣ) : O) *
      (algebraMap O K (u : O) * algebraMap O K ϖ * hf cK J v l) := by
    rw [mul_assoc, ← mul_assoc (algebraMap O K ((u⁻¹ : Oˣ) : O)), e1, one_mul]
  rw [this]
  exact mul_mem ⟨_, rfl⟩ h1

theorem perp_relIndex (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K} (hv : v ∉ L)
    (hw : ϖ • v ∈ L) :
    (perp cK J L v).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (IsLocalRing.ResidueField O) := by
  classical
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  set β := hf cK J v l0 with hβdef
  have hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hβ0 : β ≠ 0 := by
    intro h0
    exact hβ (h0 ▸ zero_mem _)
  have hex : ∀ l : L.toAddSubgroup, ∃ a : O, hf cK J v (l : Fin r → K) = algebraMap O K a * β :=
    fun l => exists_ratio hϖ hβ hβ' (mul_pair_mem c cK hcK hϖ hSD hw l.2)
  choose a ha using hex
  have hadd : ∀ x y : L.toAddSubgroup, a (x + y) = a x + a y := by
    intro x y
    apply IsFractionRing.injective O K
    apply mul_right_cancel₀ hβ0
    rw [← ha, map_add (f := _), add_mul, ← ha, ← ha]
    simpa using hf_add_right cK J v (x : Fin r → K) y
  let ψ : L.toAddSubgroup →+ IsLocalRing.ResidueField O :=
    AddMonoidHom.mk' (fun l => IsLocalRing.residue O (a l)) (by
      intro x y; rw [hadd, map_add (f := _)])
  have hker : (perp cK J L v).toAddSubgroup.addSubgroupOf L.toAddSubgroup = ψ.ker := by
    ext l
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change (l : Fin r → K) ∈ perp cK J L v ↔ IsLocalRing.residue O (a l) = 0
    rw [mem_perp, IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton,
      ← ratio_mem_iff hϖ hβ hβ', ← ha]
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
    have hm : b • l0 ∈ L.toAddSubgroup := L.smul_mem b hl0
    refine ⟨⟨b • l0, hm⟩, ?_⟩
    have : a ⟨b • l0, hm⟩ = b := by
      apply IsFractionRing.injective O K
      apply mul_right_cancel₀ hβ0
      rw [← ha]
      exact hf_algSmul_right cK J b v l0
    change IsLocalRing.residue O (a ⟨b • l0, hm⟩) = _
    rw [this]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj]
  exact Nat.card_congr AddSubgroup.topEquiv.toEquiv

theorem smul_injective {ϖ : O} (hϖ : Irreducible ϖ) :
    Function.Injective (fun x : Fin r → K => ϖ • x) := by
  intro x y h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  exact mul_left_cancel₀ (alg_ne_zero hϖ) this

theorem idx_eq_of_le {ϖ : O} (hϖ : Irreducible ϖ) {M L : Submodule O (Fin r → K)} (h : M ≤ L)
    (hi : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) : idx ϖ M = idx ϖ L := by
  set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'
  have hinj : Function.Injective f.toAddMonoidHom := smul_injective hϖ
  have e : ∀ P : Submodule O (Fin r → K),
      (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom := fun P => by
    ext x; simp [Submodule.mem_map]
  have hsub : ∀ P : Submodule O (Fin r → K), (P.map f).toAddSubgroup ≤ P.toAddSubgroup := by
    intro P x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact P.smul_mem ϖ hy
  have hBA : (M.map f).toAddSubgroup ≤ (L.map f).toAddSubgroup :=
    fun x hx => Submodule.map_mono h hx
  have hML : M.toAddSubgroup ≤ L.toAddSubgroup := h
  have e1 : (M.map f).toAddSubgroup.relIndex (L.map f).toAddSubgroup =
      M.toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  have h1 := AddSubgroup.relIndex_mul_relIndex _ _ _ hBA (hsub L)
  have h2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (hsub M) hML
  rw [e1] at h1
  have h3 : M.toAddSubgroup.relIndex L.toAddSubgroup * idx ϖ L =
      idx ϖ M * M.toAddSubgroup.relIndex L.toAddSubgroup := by
    simp only [idx]; rw [h1, h2]
  rw [mul_comm] at h3
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h3).symm

end GlobalTheory.HermNbr
end

section

noncomputable section

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr.Red

def lvlPoly (l : ℕ) (R : Type) [CommRing R] (k : ℕ) : Polynomial R :=
  ∑ i ∈ Finset.range l, ((1 + Polynomial.X : Polynomial R) ^ l ^ k) ^ i

variable {l : ℕ} {R S : Type} [CommRing R] [CommRing S]

theorem lvlPoly_coe (k : ℕ) : ((lvlPoly l R k : Polynomial R) : R⟦X⟧) = lvl l R k := by
  have := map_sum (Polynomial.coeToPowerSeries.ringHom (R := R))
    (fun i => ((1 + Polynomial.X : Polynomial R) ^ l ^ k) ^ i) (Finset.range l)
  rw [Polynomial.coeToPowerSeries.ringHom_apply] at this
  rw [lvlPoly, this, lvl]
  simp

theorem lvlPoly_map (j : R →+* S) (k : ℕ) : (lvlPoly l R k).map j = lvlPoly l S k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lvlPoly, Polynomial.map_sum]

theorem lvlPoly_mul (k : ℕ) :
    lvlPoly l R k * ((1 + Polynomial.X) ^ l ^ k - 1) = (1 + Polynomial.X) ^ l ^ (k + 1) - 1 := by
  rw [lvlPoly, geom_sum_mul, ← pow_mul, pow_succ]

theorem lvlPoly_monic [Nontrivial R] [hl : Fact l.Prime] (k : ℕ) : (lvlPoly l R k).Monic := by
  have h : lvlPoly l R k =
      (Polynomial.cyclotomic (l ^ (k + 1)) R).comp (Polynomial.X + Polynomial.C 1) := by
    rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl.out, lvlPoly]
    simp [Polynomial.sum_comp, add_comm]
  rw [h]
  exact (Polynomial.cyclotomic.monic _ _).comp_X_add_C _

theorem lvlPoly_charP {F : Type} [Field F] [hl : Fact l.Prime] [CharP F l] (k : ℕ) :
    lvlPoly l F k = Polynomial.X ^ (l ^ (k + 1) - l ^ k) := by
  have h := lvlPoly_mul (l := l) (R := F) k
  rw [add_pow_char_pow, add_pow_char_pow, one_pow, one_pow, add_sub_cancel_left,
    add_sub_cancel_left] at h
  have hle : l ^ k ≤ l ^ (k + 1) := Nat.pow_le_pow_right hl.out.pos (Nat.le_succ k)
  apply mul_right_cancel₀ (pow_ne_zero (l ^ k) Polynomial.X_ne_zero)
  rw [h, ← pow_add, Nat.sub_add_cancel hle]

theorem lvlPoly_distinguished [hl : Fact l.Prime] [IsLocalRing R] (h : ¬ IsUnit (l : R)) (k : ℕ) :
    (lvlPoly l R k).IsDistinguishedAt (IsLocalRing.maximalIdeal R) := by
  refine ⟨⟨fun {n} hn => ?_⟩, lvlPoly_monic k⟩
  have h0 : (l : IsLocalRing.ResidueField R) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]; exact h
  haveI : CharP (IsLocalRing.ResidueField R) l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0
  have h1 := lvlPoly_map (l := l) (IsLocalRing.residue R) k
  rw [lvlPoly_charP] at h1
  have h2 : (lvlPoly l R k).natDegree = l ^ (k + 1) - l ^ k := by
    rw [← (lvlPoly_monic (l := l) (R := R) k).natDegree_map (IsLocalRing.residue R), h1,
      Polynomial.natDegree_X_pow]
  have h3 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) h1
  rw [h2] at hn
  simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow, hn.ne, if_false] at h3
  exact (IsLocalRing.residue_eq_zero_iff _).1 h3

theorem lvlPoly_separable {K : Type} [Field K] [CharZero K] [hl : Fact l.Prime] (k : ℕ) :
    (lvlPoly l K k).Separable := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.out.pos _
  have hs : ((1 + Polynomial.X : Polynomial K) ^ l ^ (k + 1) - 1).Separable := by
    obtain ⟨M, hM⟩ : ∃ M, l ^ (k + 1) = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN).symm⟩
    rw [hM, Polynomial.separable_def']
    have hc : ((M : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    refine ⟨-1, Polynomial.C ((M : K) + 1)⁻¹ * (1 + Polynomial.X), ?_⟩
    have e : Polynomial.C ((M : K) + 1)⁻¹ * Polynomial.C ((M : K) + 1) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_pow_succ,
      Polynomial.derivative_add, Polynomial.derivative_X, zero_add, mul_one, sub_zero]
    linear_combination ((1 + Polynomial.X : Polynomial K) ^ (M + 1)) * e
  rw [← lvlPoly_mul] at hs
  exact hs.of_mul_left

theorem lvl_dvd_of_dvd_sq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O]
    (h : ¬ IsUnit (l : O)) (k : ℕ) (a : O⟦X⟧) (ha : lvl l O k ∣ a ^ 2) : lvl l O k ∣ a := by
  rw [← lvlPoly_coe] at ha ⊢
  have H := lvlPoly_distinguished h k
  obtain ⟨r, -, hr⟩ := GlobalTheory.NB.LT.exists_poly_mod H a
  have h1 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ ((r ^ 2 : Polynomial O) : O⟦X⟧) := by
    rw [Polynomial.coe_pow,
      show (r : O⟦X⟧) ^ 2 = a ^ 2 - (a - r) * (a + r) by ring]
    exact ha.sub (hr.mul_right _)
  have h2 := GlobalTheory.NB.LT.poly_dvd_of_dvd H h1
  let K := FractionRing O
  haveI : CharZero K := algebraRat.charZero K
  have h3 := Polynomial.map_dvd (algebraMap O K) h2
  rw [Polynomial.map_pow, lvlPoly_map] at h3
  have h4 := (lvlPoly_separable (l := l) (K := K) k).squarefree.dvd_pow_iff_dvd two_ne_zero |>.1 h3
  rw [← lvlPoly_map (algebraMap O K),
    Polynomial.map_dvd_map _ (IsFractionRing.injective O K) H.monic] at h4
  obtain ⟨s, hs⟩ := h4
  have h5 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ (r : O⟦X⟧) :=
    ⟨s, by rw [hs, Polynomial.coe_mul]⟩
  simpa using hr.add h5

end GlobalTheory.CycFr.Red
end
end

section


theorem _root_.GlobalTheory.T.chain_le_iInf_sup_pow_smul_top_of_precomplete : ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ) (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
  first | exact @GlobalTheory.chain_le_iInf_sup_pow_smul_top | exact GlobalTheory.chain_le_iInf_sup_pow_smul_top | (intros; apply GlobalTheory.chain_le_iInf_sup_pow_smul_top <;> assumption)
end
