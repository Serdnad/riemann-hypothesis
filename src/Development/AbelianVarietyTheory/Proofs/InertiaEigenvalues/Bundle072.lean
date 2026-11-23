module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Formalism.CharacterColumnKernels.Bundle001
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle029
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle011
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ReciprocityTheory.GaloisValuations.GlobalA
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

section

open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

def levCongr {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (e : M ≃ₗ[O] N) (c : O) : Lev M c ≃ Lev N c where
  toFun x := Lev.mk (e x.val) (by rw [← map_smul, Lev.smul_val, map_zero])
  invFun y := Lev.mk (e.symm y.val) (by rw [← map_smul, Lev.smul_val, map_zero])
  left_inv x := Lev.ext (by simp [Lev.val_mk])
  right_inv y := Lev.ext (by simp [Lev.val_mk])

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def divPowQ (ϖ : O) (n : ℕ) : O →ₗ[O] Formalism.NG.KO O :=
  (1 : Submodule O (FractionRing O)).mkQ ∘ₗ
    LinearMap.mulLeft O ((algebraMap O (FractionRing O) ϖ ^ n)⁻¹) ∘ₗ
      Algebra.linearMap O (FractionRing O)

theorem divPowQ_apply (ϖ : O) (n : ℕ) (a : O) :
    divPowQ ϖ n a = Submodule.Quotient.mk
      ((algebraMap O (FractionRing O) ϖ ^ n)⁻¹ * algebraMap O (FractionRing O) a) := rfl

theorem ker_divPowQ {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    LinearMap.ker (divPowQ ϖ n) = Ideal.span {ϖ ^ n} := by
  have hπ : (algebraMap O (FractionRing O) ϖ) ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ)
  ext a
  rw [LinearMap.mem_ker, divPowQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
    rw [map_mul, map_pow, hb, mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
  · rintro ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    rw [map_mul, map_pow, mul_comm (algebraMap O (FractionRing O) b), ← mul_assoc,
      inv_mul_cancel₀ hπ, one_mul]

theorem range_divPowQ {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    LinearMap.range (divPowQ ϖ n) = LinearMap.ker ((ϖ ^ n) • LinearMap.id : Formalism.NG.KO O →ₗ[O] Formalism.NG.KO O) := by
  have hπ : (algebraMap O (FractionRing O) ϖ) ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ)
  ext y
  rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨a, rfl⟩
    rw [divPowQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_one, Algebra.smul_def, map_pow, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
    exact ⟨a, rfl⟩
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one,
      Algebra.smul_def, map_pow] at hy
    obtain ⟨b, hb⟩ := hy
    refine ⟨b, ?_⟩
    rw [divPowQ_apply, hb, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

theorem natCard_lev_KO {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    Nat.card (Lev (Formalism.NG.KO O) (ϖ ^ n)) = Nat.card (O ⧸ Ideal.span {ϖ ^ n}) := by
  have h1 : Nat.card (Lev (Formalism.NG.KO O) (ϖ ^ n)) = Nat.card (LinearMap.range (divPowQ ϖ n)) := by
    rw [range_divPowQ hϖ n]; rfl
  rw [h1, ← Nat.card_congr (LinearMap.quotKerEquivRange (divPowQ ϖ n)).toEquiv, ker_divPowQ hϖ n]

theorem natCard_quot_pow {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {ϖ ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hp : (Ideal.span {ϖ}).IsPrime := hϖ.maximalIdeal_eq ▸ inferInstance
  have hq := cardQuot_pow_of_prime (P := Ideal.span {ϖ})
    (fun h => hϖ.ne_zero (Ideal.span_singleton_eq_bot.1 h)) (i := n)
  rw [Ideal.span_singleton_pow, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  rw [hq, ← hϖ.maximalIdeal_eq]
  rfl

theorem lev_pow_card {ϖ : O} (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (e : M ≃ₗ[O] Formalism.NG.KO O) (n : ℕ) [Finite (IsLocalRing.ResidueField O)] :
    Finite (Lev M (ϖ ^ n)) ∧
      Nat.card (Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hc : Nat.card (Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
    rw [Nat.card_congr (levCongr e (ϖ ^ n)), natCard_lev_KO hϖ.ne_zero, natCard_quot_pow hϖ]
  refine ⟨Nat.finite_of_card_ne_zero ?_, hc⟩
  rw [hc]
  exact pow_ne_zero _ Nat.card_pos.ne'

end DVR

theorem levKO_card : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ n : ℕ,
    Finite (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) ∧
      Nat.card (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  fun hϖ _ _ _ e n => lev_pow_card hϖ e n

end GlobalTheory.ShapeNeg
end
end

section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT

theorem factorPow_evalₐ_adic {B : Type} [CommRing B] (J : Ideal B) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion J B) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J B x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have hs := s.prop h
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hs
  rw [← neg_sub]
  exact (J ^ m).neg_mem hs

theorem exists_adicCompletion_extension {B : Type} [CommRing B] (l : ℕ)
    (f : B →+* AdicCompletion (Ideal.span {(l : B)}) B) :
    ∃ g : AdicCompletion (Ideal.span {(l : B)}) B →+* AdicCompletion (Ideal.span {(l : B)}) B,
      ∀ b, g (algebraMap B _ b) = f b := by
  have hJ : ∀ n, ∀ b ∈ Ideal.span {(l : B)} ^ n,
      AdicCompletion.evalₐ (Ideal.span {(l : B)}) n (f b) = 0 := by
    intro n b hb
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]
    have hl : ((l : B ⧸ Ideal.span {(l : B)} ^ n)) ^ n = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : B)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    rw [hl, zero_mul]
  let ψ : ∀ n, B ⧸ Ideal.span {(l : B)} ^ n →+* B ⧸ Ideal.span {(l : B)} ^ n := fun n =>
    Ideal.Quotient.lift (Ideal.span {(l : B)} ^ n)
      ((AdicCompletion.evalₐ (Ideal.span {(l : B)}) n : _ →+* _).comp f) (hJ n)
  have hψ : ∀ n b, ψ n (Ideal.Quotient.mk _ b) =
      AdicCompletion.evalₐ (Ideal.span {(l : B)}) n (f b) := fun n b => rfl
  let F : ∀ n, AdicCompletion (Ideal.span {(l : B)}) B →+* B ⧸ Ideal.span {(l : B)} ^ n :=
    fun n => (ψ n).comp (AdicCompletion.evalₐ (Ideal.span {(l : B)}) n : _ →+* _)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (Ideal.span {(l : B)}) hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨b, hb⟩ :=
      Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(l : B)}) n x)
    simp only [F, RingHom.comp_apply, RingHom.coe_coe]
    rw [← factorPow_evalₐ_adic _ hle x, ← hb, hψ, factorPow_evalₐ_adic, Ideal.Quotient.factor_mk, hψ]
  refine ⟨AdicCompletion.liftRingHom _ F hF, fun b => ?_⟩
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [AdicCompletion.evalₐ_liftRingHom]
  simp only [F, RingHom.comp_apply, RingHom.coe_coe]
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, hψ]
  rfl

theorem exists_EE_extension {l : ℕ} {O : Type} [CommRing O] (ψ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hu : IsUnit (algebraMap O⟦X⟧ (EE O l) (ψ X))) :
    ∃ ψE : EE O l →ₐ[O] EE O l,
      ∀ a, ψE (algebraMap O⟦X⟧ (EE O l) a) = algebraMap O⟦X⟧ (EE O l) (ψ a) := by
  have hu' : IsUnit (((algebraMap O⟦X⟧ (EE O l)).comp (ψ : O⟦X⟧ →+* O⟦X⟧)) X) := hu
  obtain ⟨g, hg⟩ := exists_adicCompletion_extension l
    (IsLocalization.Away.lift (X : O⟦X⟧) (S := Localization.Away (X : O⟦X⟧)) hu')
  have key : ∀ a, g (algebraMap O⟦X⟧ (EE O l) a) = algebraMap O⟦X⟧ (EE O l) (ψ a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (EE O l), hg,
      IsLocalization.Away.lift_eq]
    rfl
  refine ⟨{ g with commutes' := fun c => ?_ }, key⟩
  show g (algebraMap O (EE O l) c) = algebraMap O (EE O l) c
  rw [IsScalarTower.algebraMap_apply O O⟦X⟧ (EE O l), key, AlgHom.commutes]

end GlobalTheory.NB.LT
end

section

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr


open PowerSeries in
theorem _root_.GlobalTheory.CycFr.eq_act_of_comm {l : ℕ} [Fact l.Prime] {O : Type}
    [CommRing O] [IsDomain O] [CharZero O]
    [Algebra ℤ_[l] O] (φ₀ g : O⟦X⟧ →ₐ[O] O⟦X⟧) (c : ℤ_[l]) (hφ : φ₀ X = (1 + X) ^ l - 1)
    (hc : ∀ a, φ₀ (g a) = g (φ₀ a)) (h0 : constantCoeff (g X) = 0)
    (h1 : coeff 1 (g X) = algebraMap ℤ_[l] O c) :
    g = _root_.GlobalTheory.CycFr.act O c := by
  set A := _root_.GlobalTheory.CycFr.act O c X with hAdef
  set G := g X with hGdef
  set P : O⟦X⟧ := ∑ i ∈ Finset.range l, (1 + X) ^ i with hPdef
  have hP : (1 + X : O⟦X⟧) ^ l - 1 = X * P := by
    rw [← geom_sum_mul, add_sub_cancel_left, mul_comm]
  have hPc : constantCoeff P = (l : O) := by simp [P]
  have hXφ : X ∣ φ₀ X := by rw [hφ, hP]; exact dvd_mul_right _ _
  have hφact : φ₀ = _root_.GlobalTheory.CycFr.act O (l : ℤ_[l]) := by
    apply _root_.GlobalTheory.CycFr.algHom_ext_X _ _ hXφ
    rw [hφ, _root_.GlobalTheory.CycFr.act_nat_X]
  have hA0 : constantCoeff A = 0 :=
    PowerSeries.X_dvd_iff.mp (_root_.GlobalTheory.CycFr.X_dvd_act_X c)
  have hG : φ₀ G = (1 + G) ^ l - 1 := by
    rw [hGdef, hc, hφ]; simp [map_sub, map_pow, map_add (f := _), map_one]
  have hA : φ₀ A = (1 + A) ^ l - 1 := by
    rw [hAdef, hφact, _root_.GlobalTheory.CycFr.act_comm, ← hφact, hφ]
    simp [map_sub, map_pow, map_add (f := _), map_one]
  have hstep : ∀ n, 2 ≤ n → ∀ E : O⟦X⟧, G - A = X ^ n * E → constantCoeff E = 0 := by
    intro n hn E hE
    set S : O⟦X⟧ := ∑ i ∈ Finset.range l, (1 + G) ^ i * (1 + A) ^ (l - 1 - i) with hSdef
    have hSc : constantCoeff S = (l : O) := by simp [S, hA0, h0]
    have hD : φ₀ (G - A) = (G - A) * S := by
      have hgs := geom_sum₂_mul (1 + G) (1 + A) l
      rw [add_sub_add_left_eq_sub] at hgs
      rw [map_sub, hG, hA, mul_comm, hgs]; ring
    rw [hE, map_mul, map_pow, hφ, hP, mul_pow, mul_assoc, mul_assoc] at hD
    have hcancel := mul_left_cancel₀ (pow_ne_zero n PowerSeries.X_ne_zero) hD
    have hcc := congrArg constantCoeff hcancel
    rw [map_mul, map_mul, map_pow, hPc, hSc,
      _root_.GlobalTheory.CycFr.constantCoeff_algHom φ₀ hXφ E] at hcc
    have hne : ((l : O) ^ n) ≠ (l : O) := by
      rw [← Nat.cast_pow, Ne, Nat.cast_inj]
      intro h
      have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
      have := Nat.pow_right_injective h2 (h.trans (pow_one l).symm)
      omega
    have : constantCoeff E * ((l : O) ^ n - l) = 0 := by linear_combination hcc
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hdvd : ∀ n, X ^ (n + 2) ∣ G - A := by
    intro n
    induction n with
    | zero =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [hA0, h0]
      · rw [map_sub, h1, hAdef, _root_.GlobalTheory.CycFr.coeff_one_act_X, sub_self]
    | succ k ih =>
      obtain ⟨E, hE⟩ := ih
      have he := hstep (k + 2) (by omega) E hE
      obtain ⟨F, hF⟩ := PowerSeries.X_dvd_iff.mpr he
      exact ⟨F, by rw [hE, hF]; ring⟩
  have hGA : G = A := by
    rw [← sub_eq_zero]
    ext m
    have := PowerSeries.X_pow_dvd_iff.mp (hdvd m) m (by omega)
    simpa using this
  exact _root_.GlobalTheory.CycFr.algHom_ext_X _ _ (PowerSeries.X_dvd_iff.mpr h0) hGA

end GlobalTheory.CycFr
end

section

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr

theorem padicInt_algebraMap_injective_of_charZero {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] : Function.Injective (algebraMap ℤ_[l] O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] O (PadicInt.unitCoeff hx0 : ℤ_[l])) :=
    (PadicInt.unitCoeff hx0).isUnit.map _
  have hp : (l : O) ^ x.valuation = 0 := (mul_eq_zero.1 hx).resolve_left hu.ne_zero
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) (pow_eq_zero_iff'.1 hp).1

theorem exists_eq_X_pow_mul_of_ne_zero {O : Type} [CommRing O] {a : O⟦X⟧} (ha : a ≠ 0) :
    ∃ (m : ℕ) (w : O⟦X⟧), a = X ^ m * w ∧ constantCoeff w ≠ 0 := by
  refine ⟨a.order.toNat, a.divXPowOrder, X_pow_order_mul_divXPowOrder.symm, ?_⟩
  rw [constantCoeff_divXPowOrder]
  exact coeff_order ha

theorem X_pow_card_dvd_of_invariant {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (a : O⟦X⟧)
    (h0 : constantCoeff a = 0) (ha : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a) :
    (X : O⟦X⟧) ^ Nat.card Δ ∣ a := by
  by_cases ha0 : a = 0
  · rw [ha0]
    exact dvd_zero _
  obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero ha0
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp only [pow_zero, one_mul] at h0
      exact absurd h0 hw
    · exact h
  have hpow : ∀ δ ∈ Δ, (δ : ℤ_[l]) ^ m = 1 := by
    intro δ hδ
    obtain ⟨v, hv, hv0⟩ := exists_act_X (O := O) (δ : ℤ_[l])
    have e := ha δ hδ
    rw [map_mul, map_pow, hv, mul_pow, mul_assoc] at e
    have e' := mul_left_cancel₀ (pow_ne_zero m X_ne_zero) e
    have e'' := congrArg constantCoeff e'
    rw [map_mul, map_pow, hv0, constantCoeff_act] at e''
    have h1 : (algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m = 1 := by
      have h2 : ((algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m - 1) * constantCoeff w = 0 := by
        rw [sub_mul, one_mul, e'', sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hw)
    apply padicInt_algebraMap_injective_of_charZero O
    rw [map_pow, h1, map_one]
  have hexp : Monoid.exponent Δ ∣ m := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    apply Subtype.ext
    apply Units.ext
    simp [hpow g g.2]
  rw [IsCyclic.exponent_eq_card] at hexp
  exact (pow_dvd_pow X (Nat.le_of_dvd hm hexp)).trans (dvd_mul_right _ _)

theorem X_pow_dvd_mk_sub_sum {O : Type} [CommRing O] (c : ℕ → O) (N : ℕ) :
    (X : O⟦X⟧) ^ N ∣ PowerSeries.mk c - ∑ k ∈ Finset.range N, C (c k) * X ^ k := by
  rw [X_pow_dvd_iff]
  intro m hm

  simp [map_sum, hm]

theorem injective_and_range_eq_invariants {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ]
    (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (hj : Associated (j X) (X ^ Nat.card Δ))
    (hinv : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (j X) = j X) :
    Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a := by
  have hd : 0 < Nat.card Δ := Nat.card_pos
  obtain ⟨u, hu⟩ := hj
  have hjX0 : j X ≠ 0 := by
    intro h
    rw [h, zero_mul] at hu
    exact pow_ne_zero _ X_ne_zero hu.symm
  have hXj : (X : O⟦X⟧) ∣ j X := by
    have e : j X = X ^ Nat.card Δ * ((u⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact (dvd_pow_self (X : O⟦X⟧) hd.ne').mul_right _
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero hb0
    rw [map_mul, map_pow] at hb
    rcases mul_eq_zero.1 hb with h | h
    · exact pow_ne_zero m hjX0 h
    · apply hw
      rw [← constantCoeff_algHom j hXj w, h, map_zero]
  have hact : ∀ δ ∈ Δ, (act O (δ : ℤ_[l])).comp j = j := fun δ hδ =>
    algHom_ext_X _ _ (by rw [AlgHom.comp_apply, hinv δ hδ]; exact hXj)
      (by rw [AlgHom.comp_apply, hinv δ hδ])
  have hstep : ∀ q : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q) →
      ∃ q' : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q' = q') ∧
        q = C (constantCoeff q) + j X * q' := by
    intro q hq
    have h0 : constantCoeff (q - C (constantCoeff q)) = 0 := by simp
    have hi : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (q - C (constantCoeff q)) = q - C (constantCoeff q) := by
      intro δ hδ
      rw [map_sub, hq δ hδ, act_C]
    obtain ⟨r, hr⟩ := X_pow_card_dvd_of_invariant Δ _ h0 hi
    have hq' : q - C (constantCoeff q) = j X * (↑u * r) := by rw [hr, ← mul_assoc, hu]
    refine ⟨↑u * r, fun δ hδ => ?_, by rw [← hq']; ring⟩
    apply mul_left_cancel₀ hjX0
    rw [← hq', ← hinv δ hδ, ← map_mul, ← hq', hi δ hδ]
  choose f hf1 hf2 using hstep
  refine ⟨hinj, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨b, rfl⟩ δ hδ
    exact DFunLike.congr_fun (hact δ hδ) b
  · intro ha
    let S := {q : O⟦X⟧ // ∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q}
    let nxt : S → S := fun q => ⟨f q.1 q.2, hf1 q.1 q.2⟩
    let sq : ℕ → S := fun n => nxt^[n] ⟨a, ha⟩
    let c : ℕ → O := fun k => constantCoeff (sq k).1
    have hexp : ∀ N, a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := by
      intro N
      induction N with
      | zero => simp [sq]
      | succ N ih =>
        have e1 : (sq (N + 1)).1 = f (sq N).1 (sq N).2 := by
          simp only [sq, Function.iterate_succ_apply']
          rfl
        have e2 : (sq N).1 = C (c N) + j X * (sq (N + 1)).1 := by
          rw [e1]
          exact hf2 _ _
        calc a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := ih
          _ = ∑ k ∈ Finset.range N, C (c k) * j X ^ k +
              j X ^ N * (C (c N) + j X * (sq (N + 1)).1) := by rw [← e2]
          _ = _ := by rw [Finset.sum_range_succ]; ring
    have hjsum : ∀ N, j (∑ k ∈ Finset.range N, C (c k) * X ^ k) =
        ∑ k ∈ Finset.range N, C (c k) * j X ^ k := by
      intro N

      simp [map_sum, algHom_C]
    have hdvd : ∀ N, (X : O⟦X⟧) ^ N ∣ j (PowerSeries.mk c) - a := by
      intro N
      obtain ⟨r, hr⟩ := X_pow_dvd_mk_sub_sum c N
      have e3 : PowerSeries.mk c = ∑ k ∈ Finset.range N, C (c k) * X ^ k + X ^ N * r := by
        rw [← hr]
        ring
      have e4 : j (PowerSeries.mk c) - a = j X ^ N * (j r - (sq N).1) := by
        conv_lhs => rw [e3, map_add (f := _), map_mul, map_pow, hjsum, hexp N]
        ring
      rw [e4]
      exact (pow_dvd_pow_of_dvd hXj N).trans (dvd_mul_right _ _)
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    have h' := (X_pow_dvd_iff.1 (hdvd (n + 1))) n (Nat.lt_succ_self n)
    rw [map_sub, sub_eq_zero] at h'
    exact h'

end GlobalTheory.CycFr
end

section


theorem _root_.GlobalTheory.T.mem_span_fixed_of_semilinear_action : ∀ {G L Ω M : Type} [Group G] [Field L] [Field Ω] [Algebra L Ω] [AddCommGroup M] [Module Ω M] [Module L M] [IsScalarTower L Ω M] (b : G → Ω → Ω) (a : G → L →+* Ω) (σ : G → M →+ M) (W : Submodule L M), (∀ g h c, a (g * h) c = b g (a h c)) → (∀ c, a 1 c = algebraMap L Ω c) → (∀ m, σ 1 m = m) → (∀ g h m, σ (g * h) m = σ g (σ h m)) → (∀ g (c : L) m, σ g (c • m) = a g c • σ g m) → (Set.range a).Finite → (∀ g, ∀ m ∈ W, σ g m ∈ W) → (∀ g, (∀ c, a g c = algebraMap L Ω c) → ∀ m ∈ W, σ g m = m) → ∀ m ∈ W, m ∈ Submodule.span Ω {m | m ∈ W ∧ ∀ g, σ g m = m} := by
  first | exact @GlobalTheory.speiser_descent_span | exact GlobalTheory.speiser_descent_span | (intros; apply GlobalTheory.speiser_descent_span <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.laurent_degeneration_first_order_kernel : ∀ (k : Type) [Field k], ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ : K), ∀ (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U] (t u : V →ₗ[k] U), e ≤ 1 → (∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → ∀ y : Fin (e + 1) → Fin a → K, (∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧ (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') → ¬ LinearIndependent K y := by
  first | exact @GlobalTheory.laurent_degeneration | exact GlobalTheory.laurent_degeneration | (intros; apply GlobalTheory.laurent_degeneration <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_compatible_generators_tower_local_ring : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (M : ℕ → Type) [∀ n, AddCommGroup (M n)] [∀ n, Module Λ (M n)] [∀ n, Module.Finite Λ (M n)]
  (t : ∀ n, M (n + 1) →ₗ[Λ] M n), (∀ n, Function.Surjective (t n)) →
  (∀ n, LinearMap.ker (t n) ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ (M (n + 1)))) →
  ∃ (a : ℕ) (p : ∀ n, (Fin a → Λ) →ₗ[Λ] M n), (∀ n, Function.Surjective (p n)) ∧ (∀ n, (t n) ∘ₗ (p (n + 1)) = p n) ∧
    ∀ x, p 0 x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by
  first | exact @GlobalTheory.exists_compatible_generators_tower | exact GlobalTheory.exists_compatible_generators_tower | (intros; apply GlobalTheory.exists_compatible_generators_tower <;> assumption)
end
