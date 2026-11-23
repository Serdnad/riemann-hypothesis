module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle537
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle538
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_quotient_eisenstein_equiv : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [Algebra (Wq l a) O] (π : O) (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → (Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f) → ∃ str : O ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)}), ∀ f : Polynomial (Wq l a), str (Polynomial.aeval π f) = Ideal.Quotient.mk _ (f : (Wq l a)⟦X⟧) := by
  first | exact @GlobalTheory.bkStr_quotient_equiv | exact GlobalTheory.bkStr_quotient_equiv | (intros; apply GlobalTheory.bkStr_quotient_equiv <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix


theorem _root_.GlobalTheory.T.coeff_zero_ne_zero_of_wittFrobenius_expand_dvd : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P E : Polynomial (Wq l a)) (M : ℕ), P.Monic → E.coeff 0 ≠ 0 →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ E ^ M * P → P.coeff 0 ≠ 0 := by
  first | exact @GlobalTheory.coeff_zero_ne_zero_of_frobenius_dvd_pow_mul | exact GlobalTheory.coeff_zero_ne_zero_of_frobenius_dvd_pow_mul | (intros; apply GlobalTheory.coeff_zero_ne_zero_of_frobenius_dvd_pow_mul <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.eisenstein_distinguished_powerSeries_adicComplete : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) ∧ IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧ := by
  first | exact @GlobalTheory.BKReal.eisPoly_distinguished_complete | exact GlobalTheory.BKReal.eisPoly_distinguished_complete | (intros; apply GlobalTheory.BKReal.eisPoly_distinguished_complete <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_breuilKisin_eval_teichmuller_tilt : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (π : OC l), ¬ IsUnit π → ∃ (fl : OCb l) (ev : (Wq l a)⟦X⟧ →+* Ainf l), Per.θ l (WittVector.teichmuller l fl) = π ∧ ev X = WittVector.teichmuller l fl ∧ (∀ w, ev (C w) = wA l a w) ∧ ∀ x, ev (frobS l a x) = WittVector.frobenius (ev x) := by
  first | exact @GlobalTheory.BKReal.exists_ev_of_root | exact GlobalTheory.BKReal.exists_ev_of_root | (intros; apply GlobalTheory.BKReal.exists_ev_of_root <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix


theorem _root_.GlobalTheory.T.expand_map_dvd_of_breuilKisinFrobenius_dvd : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P Q : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → frobS l a (P : (Wq l a)⟦X⟧) ∣ (Q : (Wq l a)⟦X⟧) →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ Q := by
  first | exact @GlobalTheory.expand_map_dvd_of_frobS_dvd | exact GlobalTheory.expand_map_dvd_of_frobS_dvd | (intros; apply GlobalTheory.expand_map_dvd_of_frobS_dvd <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix


theorem _root_.GlobalTheory.T.norm_eq_of_isRoot_minpoly_unramifiedRootsOfUnityField : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (z z' : Om l),
    Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ‖z'‖ = ‖z‖ := by
  first | exact @GlobalTheory.conj_norm_eq_of_minpoly_root | exact GlobalTheory.conj_norm_eq_of_minpoly_root | (intros; apply GlobalTheory.conj_norm_eq_of_minpoly_root <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix


theorem _root_.GlobalTheory.T.weierstrass_preparation_wittOfTiltFiniteField : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : (Wq l a)⟦X⟧), ¬ (l : (Wq l a)⟦X⟧) ∣ g →
    ∃ (P : Polynomial (Wq l a)) (U : (Wq l a)⟦X⟧), IsUnit U ∧ P.Monic ∧
      (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) ∧ g = U * (P : (Wq l a)⟦X⟧) := by
  first | exact @GlobalTheory.weierstrass_prep_not_dvd_l | exact GlobalTheory.weierstrass_prep_not_dvd_l | (intros; apply GlobalTheory.weierstrass_prep_not_dvd_l <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∀ π : O, Irreducible π → ∃ Ep : Polynomial (Wq l a), Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  first | exact @GlobalTheory.TotRam.eisenstein_minpoly_Wq | exact GlobalTheory.TotRam.eisenstein_minpoly_Wq | (intros; apply GlobalTheory.TotRam.eisenstein_minpoly_Wq <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP.AinfDiv
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem cc_l : WittVector.constantCoeff (p := l) (R := OCb l) ((l : ℕ) : Ainf l) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem dvd_iff (y : Ainf l) :
    ((l : ℕ) : Ainf l) ∣ y ↔ WittVector.constantCoeff (p := l) (R := OCb l) y = 0 := by
  rw [← RingHom.mem_ker, WittVector.ker_constantCoeff, Ideal.mem_span_singleton]

theorem dvd_E : ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree := by
  have h := bk.monic.as_sum
  have : bk.E = X ^ bk.Ep.natDegree + ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * X ^ i := by
    change ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
    conv_lhs => rw [h]
    rw [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
    congr 1

    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp

  rw [this, map_add (f := _), map_pow, add_sub_cancel_left, map_sum]
  refine Finset.dvd_sum fun i hi => ?_
  obtain ⟨d, hd⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  rw [hd, map_mul, map_mul, map_mul, map_natCast, map_natCast, mul_assoc]
  exact dvd_mul_right _ _

theorem cc_E : WittVector.constantCoeff (p := l) (R := OCb l) (bk.ev bk.E) = bk.flat ^ bk.Ep.natDegree := by
  have h := (dvd_iff _).1 (dvd_E bk)
  rw [map_sub, sub_eq_zero, map_pow, bk.ev_X] at h
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h ⊢
  exact h

theorem cc_E_ne : WittVector.constantCoeff (p := l) (R := OCb l) (bk.ev bk.E) ≠ 0 := by
  intro h
  have hu := (isUnit_inclW_of_span bk.span_ev).map (WittVector.constantCoeff (p := l) (R := Cb l))
  rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, ← WittVector.constantCoeff_apply, h,
    map_zero] at hu
  exact not_isUnit_zero hu

theorem flat_ne : bk.flat ≠ 0 := by
  intro h
  apply cc_E_ne bk
  rw [cc_E, h, zero_pow bk.deg_pos.ne']

theorem flat_not_unit : ¬ IsUnit bk.flat := by
  intro h
  have h1 : IsUnit (bk.ev bk.E) := by
    refine GlobalTheory.Per.AinfComplete.witt_isUnit _ ?_
    rw [cc_E]; exact h.pow _
  have h2 : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have := h1.map (Per.θ l)
  rw [h2] at this
  exact not_isUnit_zero this

theorem flat_nil : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 bk.flat) :=
  GlobalTheory.Per.AinfComplete.nilpotent_of_not_isUnit l _ fun h =>
    flat_not_unit bk (GlobalTheory.Per.AinfComplete.perfection_isUnit _ h)

theorem flat_haus (x : OCb l) (hx : ∀ n, bk.flat ^ n ∣ x) : x = 0 :=
  GlobalTheory.Per.AinfComplete.perfection_haus (flat_nil bk) x hx

theorem complete : IsAdicComplete (Ideal.span {bk.flat}) (OCb l) := {
  haus' x hx := by
    refine flat_haus bk x fun n => ?_
    have := hx n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero] at this
    exact Ideal.mem_span_singleton.1 this,
  prec' := (GlobalTheory.Per.AinfComplete.precomplete_of_summ
    (GlobalTheory.Per.AinfComplete.summ_of_tails
      (GlobalTheory.Per.AinfComplete.perfection_tails (flat_nil bk)))).prec' }

theorem dvd_of_dvd_X_mul (y : Ainf l) (h : ((l : ℕ) : Ainf l) ∣ bk.ev X * y) : ((l : ℕ) : Ainf l) ∣ y := by
  rw [dvd_iff] at h ⊢
  rw [map_mul, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (flat_ne bk)

theorem dvd_of_forall (y : Ainf l) (h : ∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) :
    ((l : ℕ) : Ainf l) ∣ y := by
  rw [dvd_iff]
  refine flat_haus bk _ fun m => ?_
  obtain ⟨z, hz⟩ := h m
  rw [dvd_iff, map_sub, sub_eq_zero, map_mul, map_pow, bk.ev_X] at hz
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at hz ⊢
  rw [hz]
  exact dvd_mul_right _ _


include bk in
theorem mem_pow (n : ℕ) (y : Ainf l)
    (h : ((l : ℕ) : Ainf l) * y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2)) :
    y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n := by
  rw [← bk.span_ev] at h ⊢
  have h1 : (Ideal.span {((l : ℕ) : Ainf l)} ⊔ Ideal.span {bk.ev bk.E}) ^ (2 * n + 2) ≤
      Ideal.span {((l : ℕ) : Ainf l)} ^ (n + 1) ⊔ Ideal.span {bk.ev bk.E} ^ (n + 1) := by
    rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring]
    exact Ideal.sup_pow_add_le_pow_sup_pow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (h1 h)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hu hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  have hb : ((l : ℕ) : Ainf l) ∣ b := by
    rw [dvd_iff]
    have := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) huv
    simp only [map_add (f := _), map_mul, map_pow, cc_l, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_mul,
      zero_add] at this
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (cc_E_ne bk))
  obtain ⟨b', rfl⟩ := hb
  have hy : y = a * ((l : ℕ) : Ainf l) ^ n + b' * bk.ev bk.E ^ (n + 1) := by
    rw [← sub_eq_zero]
    apply ainf_torsionFree
    linear_combination -huv
  rw [hy]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_right_mono le_sup_left n ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · refine Ideal.pow_right_mono le_sup_right n ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 ⟨b' * bk.ev bk.E, by ring⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ (n : ℕ) (y : Ainf l), ((l : ℕ) : Ainf l) * y ∈
        (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2) →
      y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n) ∧
    (∀ y : Ainf l, ((l : ℕ) : Ainf l) ∣ bk.ev X * y → ((l : ℕ) : Ainf l) ∣ y) ∧
    (∀ y : Ainf l, (∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) → ((l : ℕ) : Ainf l) ∣ y) ∧
    bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ IsAdicComplete (Ideal.span {bk.flat}) (OCb l) ∧
    ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree :=
  fun _ _ _ bk => ⟨mem_pow bk, dvd_of_dvd_X_mul bk, dvd_of_forall bk, flat_ne bk, flat_not_unit bk,
    complete bk, dvd_E bk⟩

end GlobalTheory.BSP.AinfDiv
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSmall

def ballIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (r : ℝ) : Ideal A :=
  Submodule.comap (Algebra.linearMap A (PreDisc l u ρ)) (ball l u ρ r)

theorem mem_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} {x : A} :
    x ∈ ballIdeal l u ρ r ↔ algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ r := Iff.rfl

theorem ballIdeal_mul_le {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r s : ℝ} (hr : 0 ≤ r) :
    ballIdeal l u ρ r * ballIdeal l u ρ s ≤ ballIdeal l u ρ (r * s) :=
  Ideal.mul_le.2 fun x hx y hy => by
    rw [mem_ballIdeal, map_mul]
    exact mul_mem_ball l u ρ hr hx hy

theorem pow_le_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} (hr : 0 ≤ r)
    {I : Ideal A} (hI : I ≤ ballIdeal l u ρ r) : ∀ n : ℕ, I ^ n ≤ ballIdeal l u ρ (r ^ n)
  | 0 => by
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    refine (Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one).ge
    rw [mem_ballIdeal, map_one]
    exact Submodule.subset_span ⟨0, 0, 0, by simp, by simp⟩
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono (pow_le_ballIdeal hr hI n) hI).trans (ballIdeal_mul_le (pow_nonneg hr n))

theorem exists_E_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : bk.S, bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).2 fun i => ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
    · rw [h, if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
  obtain ⟨q, hq⟩ := hd
  have h2 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  refine ⟨(q : bk.S), ?_⟩
  show ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
  nth_rewrite 1 [h2]
  simp [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C]
  left
  exact map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) l

end GlobalTheory.BSP.DiscSmall


open GlobalTheory.BSP.DiscSmall in
theorem GlobalTheory.BSP.norm_toDisc_J_pow_small : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s,
    ‖toDisc l (s X) ρ x‖ ≤ r := by
  intro l hl K bk A _ s ρ hρ0 hρ1 r hr
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt
  set t : ℝ := max (1 / (l : ℝ)) ((ρ : ℝ) ^ bk.Ep.natDegree) with ht
  have ht0 : 0 < t := lt_max_of_lt_left (one_div_pos.2 hl0)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  have ht1 : t < 1 := max_lt ((div_lt_one hl0).2 hl1) (pow_lt_one₀ ρ.2 hρ1' bk.deg_pos.ne')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr ht1
  have hlmem : algebraMap A (PreDisc l (s X) ρ) (l : A) ∈ ball l (s X) ρ t := by
    refine Submodule.subset_span ⟨1, 0, 0, ?_, by simp⟩
    have : 1 / (l : ℝ) * l ≤ t * l := mul_le_mul_of_nonneg_right (le_max_left _ _) hl0.le
    rw [one_div_mul_cancel hl0.ne'] at this
    simpa using this
  have hJ : bk.J.map s ≤ ballIdeal l (s X) ρ t := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, sup_le_iff,
      Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff, Set.singleton_subset_iff]
    constructor
    · show s (l : bk.S) ∈ ballIdeal l (s X) ρ t
      rw [map_natCast, mem_ballIdeal]
      exact hlmem
    · show s bk.E ∈ ballIdeal l (s X) ρ t
      obtain ⟨q, hq⟩ := exists_E_eq bk
      rw [hq, map_add (f := _), map_mul, map_pow, map_natCast, mem_ballIdeal, map_add (f := _), map_mul, mul_comm, ← Algebra.smul_def]
      refine add_mem (Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, by simp⟩) (Submodule.smul_mem _ _ hlmem)
      show (l:ℝ)^0 * (ρ:ℝ)^bk.Ep.natDegree ≤ t * (l:ℝ)^0
      simp only [pow_zero, one_mul, mul_one]
      exact le_max_right _ _
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.map_pow] at hx
  have hx' := pow_le_ballIdeal ht0.le hJ n hx
  rw [toDisc, RingHom.comp_apply, norm_ofPre]
  exact (gauge_le l (s X) ρ (pow_pos ht0 n) hx').trans hn.le
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.FlatDisc
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem exists_eq_add (bk : BK K) : ∃ Q : Polynomial (Wq l bk.a),
    bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * Q := by
  have hd : ∀ i ∈ Finset.range bk.Ep.natDegree, ∃ c, bk.Ep.coeff i = (l : Wq l bk.a) * c :=
    fun i hi => bk.dvd_coeff i (Finset.mem_range.1 hi)
  choose d hd using hd
  refine ⟨∑ i ∈ (Finset.range bk.Ep.natDegree).attach, Polynomial.C (d i.1 i.2) * Polynomial.X ^ i.1, ?_⟩
  refine bk.monic.as_sum.trans (congrArg (Polynomial.X ^ bk.Ep.natDegree + ·) ?_)
  rw [Finset.mul_sum, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i.1 i.2, Polynomial.C_mul, mul_assoc]

theorem exists_E_eq (bk : BK K) : ∃ Q : Polynomial (Wq l bk.a),
    bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * (Q : bk.S) := by
  obtain ⟨Q, hQ⟩ := exists_eq_add bk
  refine ⟨Q, ?_⟩
  change ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
  conv_lhs => rw [hQ]
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, map_natCast]

theorem ev_coe (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    bk.ev (p : bk.S) = p.eval₂ (bk.ev.comp (C (R := Wq l bk.a))) (bk.ev X) := by
  have h : bk.ev.comp (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) =
      Polynomial.eval₂RingHom (bk.ev.comp (C (R := Wq l bk.a))) (bk.ev X) := by
    refine Polynomial.ringHom_ext (fun w => ?_) ?_
    · simp [Polynomial.coeToPowerSeries.ringHom_apply]
    · simp [Polynomial.coeToPowerSeries.ringHom_apply]
  exact RingHom.congr_fun h p

theorem theta_ev_E (bk : BK K) : Per.θ l (bk.ev bk.E) = 0 := by
  have h : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := by
    rw [← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  exact h

theorem natCast_l_ne_zero : ((l : ℕ) : Per.OC l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem flat_ne_zero (bk : BK K) : bk.flat ≠ 0 := by
  intro h0
  have hX : bk.ev X = 0 := by rw [bk.ev_X, h0, WittVector.teichmuller_zero]
  have h := theta_ev_E bk
  rw [BK.E, ev_coe, hX, Polynomial.eval₂_at_zero, RingHom.comp_apply, bk.ev_C] at h
  obtain ⟨w, hw⟩ := bk.coeff_zero
  rw [hw, map_mul, map_natCast, map_mul, map_natCast] at h
  have hu : IsUnit (Per.θ l (wA l bk.a (w : Wq l bk.a))) := (w.isUnit.map (wA l bk.a)).map (Per.θ l)
  exact natCast_l_ne_zero ((mul_eq_zero.1 h).resolve_right hu.ne_zero)

theorem not_isUnit_flat (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  obtain ⟨Q, hQ⟩ := exists_E_eq bk
  have h := theta_ev_E bk
  rw [hQ, map_add (f := _), map_mul, map_pow, map_natCast, bk.ev_X, map_add (f := _), map_mul, map_pow, map_natCast] at h
  have h1 : IsUnit (Per.θ l (WittVector.teichmuller l bk.flat) ^ bk.Ep.natDegree) :=
    ((hu.map (WittVector.teichmuller l)).map (Per.θ l)).pow _
  rw [eq_neg_of_add_eq_zero_left h, IsUnit.neg_iff] at h1
  exact OC_l_not_unit l (isUnit_of_mul_isUnit_left h1)

theorem rho_spec (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
    rw [neg_lt_zero]; positivity), ?_⟩
  rw [BK.ρ₀, ← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he.ne', NNReal.rpow_neg_one]

theorem J_eq (bk : BK K) :
    Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J := by
  obtain ⟨Q, hQ⟩ := exists_E_eq bk
  have hl : (l : bk.S) * (Q : bk.S) ∈ Ideal.span {(l : bk.S)} := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rw [Ideal.span_singleton_le_iff_mem]
    have : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * (Q : bk.S) := by rw [hQ]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hl)
  · rw [Ideal.span_singleton_le_iff_mem, hQ]
    exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hl)

end GlobalTheory.BSP.FlatDisc

theorem GlobalTheory.BSP.flat_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧
    (0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹) ∧
    Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J :=
  fun _ _ _ bk => ⟨FlatDisc.flat_ne_zero bk, FlatDisc.not_isUnit_flat bk, FlatDisc.rho_spec bk, FlatDisc.J_eq bk⟩
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K))
      (g : Hom bk.prism C), C.D.δ (BK.hf (bk := bk) g X) = 0 ∧
      Ideal.Quotient.mk C.I (BK.hf (bk := bk) g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  intro l _ K bk C g
  have hδX : (deltaS l bk.a).δ (X : bk.S) = 0 := by
    have h := (deltaS l bk.a).φ_eq (X : bk.S)
    have hφ : (deltaS l bk.a).φ (X : bk.S) = X ^ l := frobS_X l bk.a
    rw [hφ] at h
    have hmul : (l : bk.S) * (deltaS l bk.a).δ X = 0 := by linear_combination -h
    exact (mul_eq_zero.1 hmul).resolve_left (l_ne_zero l bk.a)
  refine ⟨?_, ?_⟩
  · have h := g.f_δ (X : bk.S)
    change C.D.δ (g.f X) = 0
    rw [← h]
    change g.f ((deltaS l bk.a).δ X) = 0
    rw [hδX]
    exact g.f.map_zero
  · refine g.f_str (bk.str.symm (Ideal.Quotient.mk _ X)) X ?_
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str (bk.str.symm (Ideal.Quotient.mk _ X))
    rw [RingEquiv.apply_symm_apply]
end
