module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLengthFiltrationInterKerCofactorLinearFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Mathlib.FieldTheory.Galois.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle279
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle281
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle004

@[expose] public section

section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.finite_gaussianExtension_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  first | exact @GlobalTheory.GaussExt.finite_units_quot_units | exact GlobalTheory.GaussExt.finite_units_quot_units | (intros; apply GlobalTheory.GaussExt.finite_units_quot_units <;> assumption)
end

section

open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_isPow_on_excisionNbhd : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro k B _ _ _ _ _ _ q hq f g hg u t n' d' hn hd hu
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨a, bn, ha⟩ := hn
  obtain ⟨a', bd, hb⟩ := hd
  have hw : (a * a' * g - a - a') * g = n' * d' * (bn * bd) - 1 := by
    linear_combination (-(bd * d')) * ha + (a * g - 1) * hb
  have hC' : IsExcisionNbhd B (Localization.Away (n' * d')) g :=
    GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B B g (isExcisionNbhd_self B g) (n' * d') (bn * bd)
      (Ideal.mem_span_singleton'.mpr ⟨_, hw⟩)
  set C' := Localization.Away (n' * d') with hC'def
  have hnd : IsUnit (algebraMap B C' (n' * d')) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at hnd
  have hnC : IsUnit (algebraMap B C' n') := isUnit_of_mul_isUnit_left hnd
  have hdC : IsUnit (algebraMap B C' d') := isUnit_of_mul_isUnit_right hnd
  set Di : C' := ((hdC.unit⁻¹ : C'ˣ) : C') with hDi
  have hDi1 : Di * algebraMap B C' d' = 1 := by rw [hDi]; exact hdC.val_inv_mul
  set ε : C' := algebraMap B C' n' * Di with hεdef
  have hε : IsUnit ε := hnC.mul (Units.isUnit _)
  have hεd : ε * algebraMap B C' d' = algebraMap B C' n' := by rw [hεdef, mul_assoc, hDi1, mul_one]
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B q hq g hg (n' * bd) (bn * d')
    (Ideal.mem_span_singleton'.mpr ⟨a * a' * g - a - a', by linear_combination hw⟩)
  obtain ⟨w, hw'⟩ := Ideal.mem_span_singleton'.mp hr
  have hqC : IsUnit (q : C') := by simpa using hq.map ((algebraMap B C').comp (algebraMap k B))
  have hεr : ε - algebraMap B C' r ^ q ∈ Ideal.span {algebraMap B C' g} := by
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap B C' n' * Di * algebraMap B C' a' + algebraMap B C' w, ?_⟩
    have e1 := congrArg (algebraMap B C') hw'
    have e2 := congrArg (algebraMap B C') hb
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_one] at e1 e2
    rw [hεdef]
    linear_combination e1 + (algebraMap B C' n' * Di) * e2 - (algebraMap B C' n' * algebraMap B C' bd) * hDi1
  obtain ⟨C, _, _, hC, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit C' (algebraMap B C' g) q hqC ε (algebraMap B C' r) hε hεr
  letI : Algebra B C := ((algebraMap C' C).comp (algebraMap B C')).toAlgebra
  haveI : IsScalarTower B C' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨C, inferInstance, inferInstance, GlobalTheory.T.isExcisionNbhd_trans' B C' C g hC' hC, ?_⟩
  set L := Localization.Away (algebraMap B C (f * g))
  set ψ : B →+* L := (algebraMap C L).comp (algebraMap B C) with hψ
  set ρ : C' →+* L := (algebraMap C L).comp (algebraMap C' C) with hρ
  have hψρ : ∀ y : B, ψ y = ρ (algebraMap B C' y) := fun _ => rfl
  have hφ : ∀ y : B, Localization.awayMap (algebraMap B C) (f * g)
      (algebraMap B (Localization.Away (f * g)) y) = ψ y := by
    intro y; exact IsLocalization.map_eq _ _
  have hu' : Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d') = ψ n' := by
    have h := congrArg (Localization.awayMap (algebraMap B C) (f * g)) hu
    rw [map_mul (Localization.awayMap (algebraMap B C) (f * g)), hφ, hφ] at h
    rw [← map_pow ψ, ← map_mul ψ]; exact h
  have hnL : IsUnit (ψ n') := by rw [hψρ]; exact hnC.map ρ
  have hdL : IsUnit (ψ d') := by rw [hψρ]; exact hdC.map ρ
  have hεL : ρ ε * ψ d' = ψ n' := by
    have := congrArg ρ hεd; rw [map_mul] at this; rw [hψρ, hψρ]; exact this
  have hxL : algebraMap C L x ^ q = ρ ε := by
    have := congrArg (algebraMap C L) hx; rw [map_pow] at this; exact this.symm
  have hXU : algebraMap C L x ^ q = Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * ψ t ^ q := by
    rw [← hdL.mul_left_inj, hxL, hεL, ← hu', mul_assoc]
  have hTq : IsUnit (ψ t ^ q) := by
    have h : IsUnit (Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d')) := by
      rw [hu']; exact hnL
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)
  have hT : IsUnit (ψ t) := (isUnit_pow_iff hq0).mp hTq
  have hX : IsUnit (algebraMap C L x) := by
    refine (isUnit_pow_iff hq0).mp ?_
    rw [hXU]; exact ((Units.map (Localization.awayMap (algebraMap B C) (f * g) : Localization.Away (f * g) →* L)) u).isUnit.mul hTq
  refine ⟨hX.unit * hT.unit⁻¹, ?_⟩
  rw [Units.val_mul, mul_pow, IsUnit.unit_spec, hXU, mul_assoc, ← mul_pow, hT.mul_val_inv, one_pow, mul_one]

end GlobalTheory.EtC
end

section

open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_eq_mul_qth_power_near_zeroLocus : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∀ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} → algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) → ∀ g : B, IsCoprime f g → ∀ (u : (Localization.Away (f * g))ˣ) (n d : B), IsCoprime f n → IsCoprime f d → algebraMap B (Localization.Away (f * g)) (b₁ * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) → ∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q := by
  intro k B _ _ _ _ _ _ q hq f hf A₂ _ _ hA₂ c b₁ m e he hc g hg u n d hn hd hu
  have hq0 : q ≠ 0 := by
    rintro rfl; simp at hq
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  obtain ⟨x₁, y₁, hxy₁⟩ := (hg.mul_right hn).mul_right hd
  obtain ⟨a, ha⟩ : ∃ a : A₂, a = algebraMap B A₂ (g * n * d) * e := ⟨_, rfl⟩
  have hab : a * algebraMap B A₂ y₁ - 1 ∈ Ideal.span {algebraMap B A₂ f} := by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp he
    have h1 := congrArg (algebraMap B A₂) hxy₁
    simp only [map_add (f := _), map_mul, map_one] at h1
    rw [Ideal.mem_span_singleton, ha]
    refine ⟨-(algebraMap B A₂ x₁) * e + t, ?_⟩
    simp only [map_mul]
    linear_combination e * h1 + ht
  have hA₂' : IsExcisionNbhd B (Localization.Away a) f := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA₂ a (algebraMap B A₂ y₁) hab
  have hdvd : ∀ z : A₂, z ∣ a → IsUnit (algebraMap A₂ (Localization.Away a) z) := fun z hz =>
    isUnit_of_dvd_unit (map_dvd _ hz) (IsLocalization.Away.algebraMap_isUnit a)
  have hgu := hdvd (algebraMap B A₂ g) ⟨algebraMap B A₂ n * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hnu := hdvd (algebraMap B A₂ n) ⟨algebraMap B A₂ g * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hdu := hdvd (algebraMap B A₂ d) ⟨algebraMap B A₂ g * algebraMap B A₂ n * e, by rw [ha]; simp only [map_mul]; ring⟩
  have heu := hdvd e ⟨algebraMap B A₂ (g * n * d), by rw [ha]; ring⟩
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : A₂, ε₀ = algebraMap B A₂ n * (algebraMap B A₂ d * e) ^ j := ⟨_, rfl⟩
  have hεu : IsUnit (algebraMap A₂ (Localization.Away a) ε₀) := by
    rw [hε₀, map_mul, map_pow, map_mul]; exact hnu.mul ((hdu.mul heu).pow j)
  obtain ⟨x₂, y₂, h₂⟩ := hn.mul_right (hd.pow_right (n := j))
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B (j + 1) hq f hf (n * d ^ j) y₂
    (Ideal.mem_span_singleton.mpr ⟨-x₂, by linear_combination h₂⟩)
  have hcong : ε₀ - algebraMap B A₂ r ^ (j + 1) ∈ Ideal.span {algebraMap B A₂ f} := by
    have h1 : algebraMap B A₂ f ∣ algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) :=
      map_dvd _ (Ideal.mem_span_singleton.mp hr)
    have h2 : algebraMap B A₂ f ∣ e ^ j - 1 :=
      (Ideal.mem_span_singleton.mp he).trans (by simpa using sub_dvd_pow_sub_pow e 1 j)
    have h3 : ε₀ - algebraMap B A₂ r ^ (j + 1) = algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) +
        algebraMap B A₂ n * algebraMap B A₂ d ^ j * (e ^ j - 1) := by
      rw [hε₀]; simp only [map_sub, map_mul, map_pow]; ring
    rw [Ideal.mem_span_singleton, h3]; exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)
  have hcong' : algebraMap A₂ (Localization.Away a) ε₀ - algebraMap B (Localization.Away a) r ^ (j + 1) ∈
      Ideal.span {algebraMap B (Localization.Away a) f} := by
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) r,
      IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) f, ← map_pow, ← map_sub,
      Ideal.mem_span_singleton]
    exact map_dvd _ (Ideal.mem_span_singleton.mp hcong)
  have hqu : IsUnit ((j + 1 : ℕ) : Localization.Away a) := by
    have := hq.map ((algebraMap B (Localization.Away a)).comp (algebraMap k B)); rwa [map_natCast] at this
  obtain ⟨A₃, _, _, hA₃, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit (Localization.Away a) (algebraMap B (Localization.Away a) f)
    (j + 1) hqu _ _ hεu hcong'
  letI : Algebra B A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap B (Localization.Away a)))
  letI : Algebra A₂ A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap A₂ (Localization.Away a)))
  haveI t1 : IsScalarTower B (Localization.Away a) A₃ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t3 : IsScalarTower B A₂ A₃ := IsScalarTower.of_algebraMap_eq (fun z => by
    show algebraMap (Localization.Away a) A₃ (algebraMap B (Localization.Away a) z) =
      algebraMap (Localization.Away a) A₃ (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ z))
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) z])
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, t3, GlobalTheory.T.isExcisionNbhd_trans' B (Localization.Away a) A₃ f hA₂' hA₃, ?_, ?_⟩
  · have : algebraMap B A₃ g = algebraMap (Localization.Away a) A₃
        (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ g)) := by
      rw [← IsScalarTower.algebraMap_apply B A₂ (Localization.Away a)]; rfl
    rw [this]; exact hgu.map _
  have hDu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f))
      (algebraMap A₂ A₃ (algebraMap B A₂ d * e))) := by
    have hde : IsUnit (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ d * e)) := by
      rw [map_mul]; exact hdu.mul heu
    exact (hde.map (algebraMap (Localization.Away a) A₃)).map _
  have hX : algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x ^ (j + 1) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) *
      (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
       algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j := by
    rw [← map_pow, ← hx]
    show algebraMap A₃ _ (algebraMap A₂ A₃ ε₀) = _
    rw [hε₀]; simp only [map_mul, map_pow]
  have hXu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x) :=
    (isUnit_pow_iff (Nat.succ_ne_zero j)).mp (by rw [← map_pow, ← hx]; exact (hεu.map _).map _)
  have hFu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ f))) := by
    rw [← IsScalarTower.algebraMap_apply B A₂ A₃]; exact IsLocalization.Away.algebraMap_isUnit _
  refine ⟨hXu.unit * hDu.unit⁻¹, fun φ ψ hφ hψ => ?_⟩
  have hφ' : ∀ y, φ (algebraMap A₂ _ y) = algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ y) :=
    fun y => RingHom.congr_fun hφ y
  have hψ' : ∀ z, ψ (algebraMap B _ z) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ z)) := fun z => by
    have := RingHom.congr_fun hψ z
    simp only [RingHom.comp_apply] at this
    rw [this, IsScalarTower.algebraMap_apply B A₂ A₃ z]
  have H1 := congrArg φ hc
  have H2 := congrArg ψ hu
  simp only [map_mul, map_pow, hφ'] at H1
  simp only [map_mul, map_pow, hψ'] at H2
  have hW := hDu.mul_val_inv
  rw [Units.val_mul, IsUnit.unit_spec]
  generalize (↑hDu.unit⁻¹ : Localization.Away (algebraMap B A₃ f)) = W at hW ⊢
  simp only [map_mul] at hW hFu
  have key0 : φ c * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) =
      ψ u * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) := by
    apply (hFu.pow m).mul_right_cancel
    linear_combination -(algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d))) * H1 + H2
  calc φ c = φ c * (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) * W) ^ (j + 1) := by
        rw [hW, one_pow, mul_one]
    _ = _ := by
      linear_combination (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j * W ^ (j + 1) * key0 -
        ψ u * W ^ (j + 1) * hX

end GlobalTheory.EtC
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodEtale

theorem noTorsion_of_faithfullyFlat_point : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O],
    Nonempty (C →ₐ[R] O) → GlobalTheory.GoodEtale.TorsionFreeOver A R C →
    ∀ (a : A), a ≠ 0 → ∀ v : O, algebraMap R O (algebraMap A R a) * v = 0 → v = 0 := by
  intro A R C O _ _ _ _ _ _ _ _ hσ hTF a ha v hv
  obtain ⟨σ⟩ := hσ
  have hRO : Function.Injective (algebraMap R O) :=
    RingHom.FaithfullyFlat.injective (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hreg : IsSMulRegular R (algebraMap A R a) := by
    intro r s hrs
    simp only [smul_eq_mul] at hrs
    have h0 : algebraMap A R a * (r - s) = 0 := by rw [mul_sub, hrs, sub_self]
    have h1 : algebraMap A R a • algebraMap R C (r - s) = 0 := by
      rw [Algebra.smul_def, ← map_mul, h0, map_zero]
    have h2 := hTF a ha _ h1
    have h3 : algebraMap R O (r - s) = 0 := by
      rw [← σ.commutes, h2, map_zero]
    exact sub_eq_zero.mp (hRO (by rw [h3, map_zero]))
  have hO : IsSMulRegular O (algebraMap R O (algebraMap A R a)) := IsSMulRegular.of_flat hreg
  apply hO
  simp only [smul_eq_mul, mul_zero]
  exact hv

theorem hart_of_local : ∀ (A O M : Type) [CommRing A] [CommRing O] [Algebra A O] [AddCommGroup M] [Module O M],
    GlobalTheory.GoodEtale.Hart A O M → ∀ (a : A), a ≠ 0 → ∀ m : M,
    (∀ Q : Ideal O, Q.IsPrime → (Q.comap (algebraMap A O)).height ≤ 1 →
      ∃ s ∉ Q, ∃ m' : M, s • m = algebraMap A O a • m') →
    ∃ m' : M, m = algebraMap A O a • m' := by
  intro A O M _ _ _ _ _ hH a ha m hloc
  apply hH a ha m
  intro p hp hpht
  by_contra hcon
  push_neg at hcon
  let J : Ideal O :=
    { carrier := {o | ∃ m' : M, o • m = algebraMap A O a • m'}
      add_mem' := by
        rintro x y ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
        exact ⟨m₁ + m₂, by rw [add_smul, h₁, h₂, smul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨m₁, h₁⟩
        refine ⟨c • m₁, ?_⟩
        simp only [smul_eq_mul]
        rw [mul_smul, h₁, smul_comm] }
  have hdisj : Disjoint (J : Set O) ((p.primeCompl.map (algebraMap A O) : Submonoid O) : Set O) := by
    rw [Set.disjoint_left]
    rintro _ ⟨m', hm'⟩ ⟨u, hu, rfl⟩
    exact hcon u hu m' hm'
  obtain ⟨Q, hQ, hJQ, hQd⟩ := Ideal.exists_le_prime_disjoint J _ hdisj
  have hle : Q.comap (algebraMap A O) ≤ p := by
    intro u hu
    by_contra hup
    exact Set.disjoint_left.mp hQd hu ⟨u, hup, rfl⟩
  obtain ⟨s, hs, m', hm'⟩ := hloc Q hQ ((Ideal.height_mono hle).trans hpht)
  exact hs (hJQ ⟨m', hm'⟩)

theorem descent_finiteEtale : ∀ (A R C O : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [IsNoetherianRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → GlobalTheory.GoodEtale.Hart A R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    Nonempty (C →ₐ[R] O) →
    Module.Finite R C ∧ Algebra.Etale R C := by
  intro A R C O _ _ _ _ _ _ _ _ _ _ _ G _ _ _ act T hT a ha n x y hxy hTF hH hE hσ
  obtain ⟨σ⟩ := hσ
  refine ⟨GlobalTheory.T.finite_of_galois_trace_relation A R C G act T hT a ha n x y hxy hTF, ?_⟩
  letI : Algebra A O := ((algebraMap R O).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hHO : Hart A O (O ⊗[R] C) := GlobalTheory.T.hart_baseChange_of_flat A R C O hH
  set b := algebraMap A R a with hb
  have hdiv : ∀ h : G, ∃ m' : O ⊗[R] C, galElt act σ x y h = algebraMap R O b • m' := by
    intro h
    refine hart_of_local A O (O ⊗[R] C) hHO a ha (galElt act σ x y h) ?_
    intro Q hQ hht
    haveI := hQ
    haveI : Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) :=
      GlobalTheory.T.etale_localizationAtPrime_tensor_of_low_height A R C O Q hE (by first | exact hht | (rw [Ideal.comap_comap]; exact hht))
    let σQ : C →ₐ[R] Localization.AtPrime Q := (IsScalarTower.toAlgHom R O _).comp σ
    have hinj := GlobalTheory.T.galoisComparisonMap_injective_of_flat A R C (Localization.AtPrime Q) G act T hT a ha n x y hxy hTF σQ
    obtain ⟨m'', hm''⟩ := GlobalTheory.T.galoisElement_dvd_of_formallyUnramified R C (Localization.AtPrime Q) G act b n x y hxy σQ hinj h
    have hcomp : (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C
        (galElt act σ x y h) = galElt act σQ x y h := by

      simp [galElt, map_sum, σQ]
    obtain ⟨s, hs, m', hm'⟩ := GlobalTheory.T.exists_smul_dvd_of_localization_atPrime_tensor' R C O Q b _ ⟨m'', hcomp.trans hm''⟩
    exact ⟨s, hs, m', hm'⟩
  have key : ∀ h, ∃ m, galMap act σ m = Pi.single h 1 := by
    intro h
    obtain ⟨m', hm'⟩ := hdiv h
    refine ⟨m', ?_⟩
    have h1 := galMap_galElt act σ x y b (by simpa [hb] using hxy) h
    rw [hm', map_smul] at h1
    funext g
    have h2 := congrFun h1 g
    refine sub_eq_zero.mp (noTorsion_of_faithfullyFlat_point A R C O ⟨σ⟩ hTF a ha _ ?_)
    rw [mul_sub]
    by_cases hg : g = h
    · subst hg; simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at h2 ⊢; rw [h2]; simp [hb]
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hg] at h2 ⊢; rw [h2]; simp
  have hsurj : Function.Surjective (galMap act σ) := by
    intro v
    choose m hm using key
    refine ⟨∑ h, v h • m h, ?_⟩

    rw [map_sum]
    simp only [map_smul, hm]
    funext g
    simp [Finset.sum_apply, Pi.single_apply]
  let e := AlgEquiv.ofBijective (galMap act σ)
    ⟨GlobalTheory.T.galoisComparisonMap_injective_of_flat A R C O G act T hT a ha n x y hxy hTF σ, hsurj⟩
  haveI : Algebra.Etale O (O ⊗[R] C) := Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat O

end GlobalTheory.GoodEtale
end
end

section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

def Fits (T O : Type) [CommRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O]
    (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T)
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
    (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)) :
    Prop :=
  Function.Injective i ∧ IsLocalHom i ∧ IsUnit (q : A) ∧
    QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
    ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA ∧
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA

def Retracts (T O : Type) [CommRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O]
    (A : Type) [CommRing A] (i : A →+* T)
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
    (ρ : Localization.AtPrime QA →+* A) : Prop :=
  ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A ∧
    RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} ∧
    ∀ x : Localization.AtPrime QA,
      algebraMap T O (i (ρ x)) - jA x ∈ Ideal.span {algebraMap (Polynomial T) O Polynomial.X}

def PointAtZero (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) : Prop :=
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  ∃ s : GlobalTheory.KeyOriginNoeth.closure A R D →+* FractionRing A,
    s.comp (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D)) = (algebraMap A (FractionRing A)).comp ρ

end GlobalTheory.KeyOriginEnlarge
end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.zmodTorsor_field_eq_prod_galois : ∀ (K M : Type) [Field K] [CommRing M] [Algebra K M] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)), 0 < q →
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)),
      (∀ i, FiniteDimensional K (L i)) ∧ (∀ i, IsGalois K (L i)) ∧
      (∀ i, Module.finrank K (L i) ∣ q) ∧ Nonempty (M ≃ₐ[K] ∀ i, L i) := by
  first | (exact @GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (exact GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (intros; apply GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois  <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.finite_eigenFiltration_pieces_addValInt : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) ∧ Module.Finite (Int0 v) (preEig a Fil τ) ∧ Module.Finite (Int0 v) (filKer a Fil τ) ∧ Module.Finite (Int0 v) (eigSub a τ (Fin N → RS a)) ∧ Module.Finite (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) ∧ Module.Finite (Int0 v) (eigSub a τ Fil) ∧ Module.Finite (Int0 v) (kerMul a (cofac a τ) Fil) := by
  first | exact @GlobalTheory.HerbFin.finite_main | exact GlobalTheory.HerbFin.finite_main | (intros; apply GlobalTheory.HerbFin.finite_main <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.relLength_filtrationInterKerCofactor_linearFactor : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((filKer a Fil τ).map (mulR a N (lin a τ))) (filKer a Fil τ) r := by
  first | exact @GlobalTheory.HerbCore.relLen_lin_filKer | exact GlobalTheory.HerbCore.relLen_lin_filKer | (intros; apply GlobalTheory.HerbCore.relLen_lin_filKer <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.genericFibreBase_flat_noetherian_intClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    Module.Flat A (Localization.AtPrime QA) ∧ IsNoetherianRing (Localization.AtPrime QA) ∧
      algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X ∈ nonZeroDivisors (Localization.AtPrime QA) ∧
      ∀ f : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA), IsIntegral (Localization.AtPrime QA) f →
        ∃ r : Localization.AtPrime QA, algebraMap _ (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) r = f := by
  first | (exact @GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed) | (exact GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed) | (intros; apply GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed  <;> assumption)
end
