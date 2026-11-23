module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import ReciprocityTheory.GaloisValuations.Global
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB

@[expose] public section

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

def ball (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := by
    intro a b ha hb
    simp only [cball, Set.mem_setOf_eq] at ha hb ⊢
    exact Valuation.map_add_le _ ha hb
  neg_mem' := by
    intro a ha
    simp only [cball, Set.mem_setOf_eq] at ha ⊢
    rwa [Valuation.map_neg]

theorem mem_ball {s : kˣ} {a : k} : a ∈ ball s ↔ valuation k a ≤ valuation k (s : k) := Iff.rfl

theorem ball_mono {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) {a : k} (ha : a ∈ ball s) :
    a ∈ ball t := mem_ball.2 (le_trans (mem_ball.1 ha) h)

theorem mul_mem_ball {s t : kˣ} {a b : k} (ha : a ∈ ball s) (hb : b ∈ ball t) : a * b ∈ ball (s * t) := by
  rw [mem_ball, map_mul, Units.val_mul, map_mul]
  exact mul_le_mul' ha hb

theorem isOpen_ball (s : kˣ) : IsOpen ((ball s : AddSubgroup k) : Set k) := isOpen_cball s

abbrev Q (s t : kˣ) : Type := ↥(ball t) ⧸ (ball s).addSubgroupOf (ball t)

instance finite_Q (s t : kˣ) : Finite (Q (k := k) s t) := by
  haveI : CompactSpace ↥(ball t) := isCompact_iff_compactSpace.mp (isCompact_cball t)
  refine AddSubgroup.quotient_finite_of_isOpen _ ?_
  rw [AddSubgroup.coe_addSubgroupOf]
  exact (isOpen_ball s).preimage continuous_subtype_val

noncomputable instance (s t : kˣ) : Fintype (Q (k := k) s t) := Fintype.ofFinite _

theorem out_eq_add {s t : kˣ} (x : ↥(ball t)) (q : Q s t) (hq : q = QuotientAddGroup.mk x) :
    ∃ h ∈ ball s, ((Quotient.out q : ↥(ball t)) : k) = (x : k) + h := by
  have h1 : (QuotientAddGroup.mk (Quotient.out q) : Q s t) = QuotientAddGroup.mk x := by
    rw [← hq]; exact QuotientAddGroup.out_eq' q
  rw [QuotientAddGroup.eq] at h1
  refine ⟨((Quotient.out q : ↥(ball t)) : k) - x, ?_, by ring⟩
  have h2 := AddSubgroup.mem_addSubgroupOf.1 (neg_mem h1)
  convert h2 using 1
  push_cast
  ring

theorem apply_out {M : Type} {s t : kˣ} (g : k → M) (hg : ∀ b, ∀ h ∈ ball s, g (b + h) = g b)
    (x : ↥(ball t)) (q : Q s t) (hq : q = QuotientAddGroup.mk x) :
    g ((Quotient.out q : ↥(ball t)) : k) = g x := by
  obtain ⟨h, hh, he⟩ := out_eq_add x q hq
  rw [he, hg _ _ hh]

theorem out_mem {s t : kˣ} (q : Q s t) : ((Quotient.out q : ↥(ball t)) : k) ∈ ball t := (Quotient.out q).2

theorem out_zero_mem {s t : kˣ} : ((Quotient.out (0 : Q s t) : ↥(ball t)) : k) ∈ ball s := by
  obtain ⟨h, hh, he⟩ := out_eq_add (s := s) (0 : ↥(ball t)) 0 rfl
  rw [he]; simpa using hh

theorem out_mem_iff {s t : kˣ} (q : Q s t) : ((Quotient.out q : ↥(ball t)) : k) ∈ ball s ↔ q = 0 := by
  constructor
  · intro h
    rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_addSubgroupOf.2 h
  · rintro rfl; exact out_zero_mem

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def avg (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (s t : kˣ) (ξ : k) : V →ₗ[ℂ] V :=
  ∑ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) • σ ((Quotient.out q : ↥(ball t)) : k)

theorem ch_add (ψ : AddChar k Circle) (a b : k) : ((ψ (a + b) : Circle) : ℂ) = (ψ a : ℂ) * (ψ b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem ch_neg_mul (ψ : AddChar k Circle) (a : k) : ((ψ (-a) : Circle) : ℂ) * (ψ a : ℂ) = 1 := by
  rw [← ch_add ψ, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

section Avg

variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (hadd : ∀ a b, σ (a + b) = σ a * σ b)
include hadd

theorem comm (a b : k) : σ a * σ b = σ b * σ a := by rw [← hadd, ← hadd, add_comm]

theorem avg_comm (s t : kˣ) (ξ : k) (b : k) : avg ψ σ s t ξ * σ b = σ b * avg ψ σ s t ξ := by
  simp only [avg, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, comm σ hadd]

theorem avg_comm_avg (s t s' t' : kˣ) (ξ ξ' : k) :
    avg ψ σ s t ξ * avg ψ σ s' t' ξ' = avg ψ σ s' t' ξ' * avg ψ σ s t ξ := by
  rw [avg, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, avg_comm ψ σ hadd]

omit hadd in
theorem avg_mem (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W) (s t : kˣ) (ξ : k) {w : V} (hw : w ∈ W) :
    avg ψ σ s t ξ w ∈ W := by
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply]
  exact W.sum_mem fun q _ => W.smul_mem _ (hW _ _ hw)

theorem avg_eigen {s t : kˣ} {ξ : k} (hξ : ∀ h ∈ ball s, ψ (ξ * h) = 1) {y : V} (hy : ∀ h ∈ ball s, σ h y = y)
    {a : k} (ha : a ∈ ball t) : σ a (avg ψ σ s t ξ y) = ((ψ (ξ * a) : Circle) : ℂ) • avg ψ σ s t ξ y := by
  rw [← Module.End.mul_apply, ← avg_comm ψ σ hadd, Module.End.mul_apply]
  let g : k → V := fun b => ((ψ (-(ξ * b)) : Circle) : ℂ) • σ b y
  have hg : ∀ b, ∀ h ∈ ball s, g (b + h) = g b := by
    intro b h hh
    simp only [g, hadd, Module.End.mul_apply, hy h hh, mul_add, neg_add, ch_add ψ, hξ h hh]
    have : ((ψ (-(ξ * h)) : Circle) : ℂ) = 1 := by
      have := ch_neg_mul ψ (ξ * h); rwa [hξ h hh, Circle.coe_one, mul_one] at this
    rw [this, mul_one]
  let a' : ↥(ball t) := ⟨a, ha⟩
  have key : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) •
      σ ((Quotient.out q : ↥(ball t)) : k) (σ a y) =
      ((ψ (ξ * a) : Circle) : ℂ) • g ((Quotient.out (q + QuotientAddGroup.mk a') : ↥(ball t)) : k) := by
    intro q
    rw [apply_out g hg (Quotient.out q + a') _ (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq'])]
    simp only [g, AddSubgroup.coe_add, a', ← Module.End.mul_apply, ← hadd, smul_smul]
    congr 1
    rw [mul_add, neg_add, ch_add ψ, ← mul_assoc, mul_comm ((ψ (ξ * a) : Circle) : ℂ), mul_assoc]
    rw [mul_comm ((ψ (ξ * a) : Circle) : ℂ), ch_neg_mul, mul_one]
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, key, ← Finset.smul_sum]
  congr 1
  exact (Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk a' : Q s t)) (fun q => g ((Quotient.out q : ↥(ball t)) : k)))

end Avg

end DiscreteGroups.sglob.LConvGenF
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace DiscreteGroups.sglob.DzType

section Fix

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
  [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω]

theorem natCast_mem_of_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (g n : ℕ)
    (hn : 0 < n) (hN : normV v = g ^ n) : ((g : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 K ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card, show Nat.card (𝓞 K ⧸ v.asIdeal) = g ^ n from hN, Nat.cast_pow] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact (pow_eq_zero_iff hn.ne').1 hc

theorem fix_of_ine (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (he : ∀ [w'.asIdeal.LiesOver w.asIdeal], w'.asIdeal.ramificationIdx (𝓞 E) = 1)
    (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) (e : E') : σ (algebraMap E' Ω e) = algebraMap E' Ω e := by
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  let LL := IntermediateField.normalClosure E E' Ω
  have : NumberField (LL) :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap E (LL)).injective
      to_finiteDimensional := Module.Finite.trans E (LL) }
  have : IsGalois E' (LL) := IsGalois.tower_top_of_isGalois E E' (LL)
  have hmem : ∀ x : 𝓞 (LL), (((x : LL) : Ω)) ∈ A := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A ((x.2).map (IsScalarTower.toAlgHom ℤ (LL) Ω))
  let ψ : 𝓞 (LL) →+* A :=
    { toFun := fun x => ⟨((x : LL) : Ω), hmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let P : Ideal (𝓞 (LL)) := (IsLocalRing.maximalIdeal A).comap ψ
  have hP : ∀ x : 𝓞 (LL), x ∈ P ↔ A.valuation (((x : LL) : Ω)) < 1 := fun x => A.valuation_lt_one_iff (ψ x)
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hcE : ∀ x : 𝓞 E, (((algebraMap (𝓞 E) (𝓞 (LL)) x : 𝓞 (LL)) : LL) : Ω) = algebraMap E Ω (x : E) :=
    fun x => rfl
  have hcE' : ∀ x : 𝓞 E', (((algebraMap (𝓞 E') (𝓞 (LL)) x : 𝓞 (LL)) : LL) : Ω) = algebraMap E' Ω (x : E') :=
    fun x => rfl
  have : P.LiesOver w.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, hP, hcE]
    exact (h x).symm⟩
  have : P.LiesOver w'.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, hP, hcE']
    exact (h' x).symm⟩
  have : w'.asIdeal.LiesOver w.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, ← h' _, ← h x]
    have e1 : algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') x : 𝓞 E') : E') = algebraMap E Ω (x : E) :=
      (IsScalarTower.algebraMap_apply E E' Ω (x : E)).symm
    rw [e1]⟩
  have : IsGaloisGroup (LL ≃ₐ[E] LL) (𝓞 E) (𝓞 (LL)) :=
    IsGaloisGroup.of_isFractionRing (LL ≃ₐ[E] LL) (𝓞 E) (𝓞 (LL)) E (LL)
  have : IsGaloisGroup (LL ≃ₐ[E'] LL) (𝓞 E') (𝓞 (LL)) :=
    IsGaloisGroup.of_isFractionRing (LL ≃ₐ[E'] LL) (𝓞 E') (𝓞 (LL)) E' (LL)
  have c1 := Ideal.card_inertia_eq_ramificationIdxIn (G := LL ≃ₐ[E] LL) w.asIdeal P
  have c2 := Ideal.card_inertia_eq_ramificationIdxIn (G := LL ≃ₐ[E'] LL) w'.asIdeal P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal P (LL ≃ₐ[E] LL)] at c1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx w'.asIdeal P (LL ≃ₐ[E'] LL)] at c2
  have tower := Ideal.ramificationIdx_tower (R := 𝓞 E) w'.asIdeal P
  have hcard : Nat.card (P.inertia (LL ≃ₐ[E] LL)) ≤ Nat.card (P.inertia (LL ≃ₐ[E'] LL)) := by
    rw [c1, c2, tower, he, one_mul]
  let f : P.inertia (LL ≃ₐ[E'] LL) → P.inertia (LL ≃ₐ[E] LL) := fun τ => ⟨τ.1.restrictScalars E, fun x => τ.2 x⟩
  have hf : Function.Injective f := fun τ τ' hτ =>
    Subtype.ext (AlgEquiv.restrictScalars_injective E (congrArg Subtype.val hτ))
  have hbij := hf.bijective_of_nat_card_le hcard
  let σb : LL ≃ₐ[E] LL := σ.restrictNormal (LL)
  have hcomm : ∀ y : LL, ((σb y : LL) : Ω) = σ ((y : LL) : Ω) := fun y => AlgEquiv.restrictNormal_commutes σ (LL) y
  have hσb : σb ∈ P.inertia (LL ≃ₐ[E] LL) := fun x => by
    show σb • x - x ∈ P
    rw [hP]
    have e2 : (((σb • x - x : 𝓞 (LL)) : LL) : Ω) = ((σb (x : LL) : LL) : Ω) - ((x : LL) : Ω) := rfl
    rw [e2, hcomm]
    exact hσ.2 _ ((A.valuation_le_one_iff _).2 (hmem x))
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨σb, hσb⟩
  have hτ' : τ.1.restrictScalars E = σb := congrArg Subtype.val hτ
  have key : σb (algebraMap E' (LL) e) = algebraMap E' (LL) e := by
    rw [← hτ']
    exact τ.1.commutes e
  have e5 : (((algebraMap E' (LL) e : LL)) : Ω) = algebraMap E' Ω e := rfl
  rw [← e5, ← hcomm, key]

end Fix

theorem ine_lift {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ) (hn : 0 < n)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) :
    ∃ t : G E' Ω, t ∈ Ine (F := E') A ∧ AlgEquiv.restrictScalars E t = σ := by
  have hgw' := natCast_mem_of_normV w' g n hn hN
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    refine (h _).1 ?_
    have e1 : algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) = algebraMap E' Ω (((g : ℕ) : 𝓞 E') : E') := by simp
    rw [e1]
    exact (h' _).2 hgw'
  have he : ∀ [w'.asIdeal.LiesOver w.asIdeal], w'.asIdeal.ramificationIdx (𝓞 E) = 1 := by
    intro _
    have hmap : ¬ Ideal.map (algebraMap (𝓞 E) (𝓞 E')) w.asIdeal ≤ w'.asIdeal ^ 2 := fun hle => hg (by
      have := hle (Ideal.mem_map_of_mem (algebraMap (𝓞 E) (𝓞 E')) hgw)
      rwa [map_natCast] at this)
    have hlt := Ideal.ramificationIdx'_lt hmap
    rw [Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal w'.asIdeal w.ne_bot] at hlt
    have hpos := Ideal.ramificationIdx_pos (R := 𝓞 E) w'.asIdeal
    omega
  have hfix := fix_of_ine A w h w' h' he σ hσ
  let t : G E' Ω := { σ.toRingEquiv with commutes' := hfix }
  refine ⟨t, ⟨?_, fun x hx => hσ.2 x hx⟩, AlgEquiv.ext fun x => rfl⟩
  show t • A = A
  have hd : σ • A = A := hσ.1
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

end DiscreteGroups.sglob.DzType
end
end
