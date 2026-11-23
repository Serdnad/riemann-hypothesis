module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle295
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.CharP.Subring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle519
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle520
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle522
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKReal.Roots

variable (l : ℕ) [hl : Fact l.Prime]

theorem exists_roots (π : OC l) : ∃ s : ℕ → OC l, s 0 = π ∧ ∀ n, s (n + 1) ^ l = s n := by
  choose r hr using fun x : ℂ_[l] => IsAlgClosed.exists_pow_nat_eq x hl.out.pos
  have hn : ∀ x : ℂ_[l], ‖x‖ ≤ 1 → ‖r x‖ ≤ 1 := fun x hx => by
    have h := congrArg norm (hr x)
    rw [norm_pow] at h
    by_contra h1
    exact absurd (h ▸ one_lt_pow₀ (not_le.1 h1) hl.out.ne_zero) (not_lt.2 hx)
  let t : OC l → OC l := fun x => ⟨r x, (GlobalTheory.RingBasics.mem_OC _).2 (hn _ ((GlobalTheory.RingBasics.mem_OC _).1 x.2))⟩
  exact ⟨fun n => t^[n] π, rfl, fun n => by
    show (t^[n + 1] π) ^ l = t^[n] π
    rw [Function.iterate_succ_apply']
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hr _)⟩


variable {l} in
def flatOf (s : ℕ → OC l) (hs : ∀ n, s (n + 1) ^ l = s n) : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (s n), fun n => by rw [← map_pow, hs]⟩ :
    Perfection (ModP (OC l) l) l)


variable {l} in
theorem untilt_flatOf (s : ℕ → OC l) (hs : ∀ n, s (n + 1) ^ l = s n) : (flatOf s hs).untilt = s 0 := by
  have hp : ∀ n, s n ^ l ^ n = s 0 := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, hs, ih]
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ⟨s n, rfl, ?_⟩
  rw [hp]

end GlobalTheory.BKReal.Roots

namespace GlobalTheory.BKReal

theorem exists_ev_of_root : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (π : OC l), ¬ IsUnit π →
    ∃ (fl : OCb l) (ev : (Wq l a)⟦X⟧ →+* Ainf l), Per.θ l (WittVector.teichmuller l fl) = π ∧
      ev X = WittVector.teichmuller l fl ∧ (∀ w, ev (C w) = wA l a w) ∧
      ∀ x, ev (frobS l a x) = WittVector.frobenius (ev x) := by
  intro l hl a _ π hπ
  obtain ⟨s, hs0, hs⟩ := Roots.exists_roots l π
  set fl := Roots.flatOf s hs
  set t : Ainf l := WittVector.teichmuller l fl
  have ht : Per.θ l t = π := (WittVector.fontaineTheta_teichmuller _).trans
    ((Roots.untilt_flatOf s hs).trans hs0)
  have htu : ¬ IsUnit t := fun h => hπ (ht ▸ h.map (Per.θ l))
  have hc : IsAdicComplete (Ideal.span {t}) (Ainf l) := (GlobalTheory.Per.AinfComplete.main l _ htu).2
  have hsep : ∀ x : Ainf l, (∀ n, t ^ n ∣ x) → x = 0 := fun x h =>
    GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (h n)
  letI : Algebra (Wq l a) (Ainf l) := (wA l a).toRingHom.toAlgebra
  obtain ⟨f, hfX⟩ := GlobalTheory.Cyc.IoMap.algHom_exists (R := Wq l a) t
    (GlobalTheory.Per.AinfComplete.summ_of_precomplete _) hsep
  have hfC : ∀ w, f.toRingHom (C w) = wA l a w := f.commutes
  have h1 : WittVector.frobenius t = t ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  refine ⟨fl, f.toRingHom, ht, hfX, hfC, fun x => ?_⟩
  refine RingHom.congr_fun (ringHom_ext_of_sep (f.toRingHom.comp (frobS l a))
    (WittVector.frobenius.comp f.toRingHom) (fun w => ?_) ?_ fun y hy => hsep y fun n => ?_) x
  · simp only [RingHom.comp_apply, frobS_C, hfC, wA_sigma]
  · simp only [RingHom.comp_apply, frobS_X, map_pow]
    rw [show f.toRingHom X = t from hfX, h1]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, frobS_X, map_pow]
    rw [show f.toRingHom X = t from hfX]
    exact pow_dvd_pow_of_dvd (dvd_pow_self _ hl.out.ne_zero) n

end GlobalTheory.BKReal
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem coeff_zero_ne_zero_of_expand_map_dvd {R : Type*} [CommRing R] [IsDomain R] (l : ℕ) (hl : 2 ≤ l)
    (σ : R →+* R) (P E : Polynomial R) (M : ℕ) (hP : P ≠ 0) (hE : E.coeff 0 ≠ 0)
    (h : Polynomial.expand R l (P.map σ) ∣ E ^ M * P) : P.coeff 0 ≠ 0 := by
  obtain ⟨P0, hP0, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  generalize Polynomial.rootMultiplicity 0 P = k at hP0
  simp only [map_zero, sub_zero] at hP0 hnd
  intro h0
  have hk : k ≠ 0 := by
    rintro rfl
    apply hnd
    rw [Polynomial.X_dvd_iff]
    simpa [hP0] using h0
  have h1 : (Polynomial.X : Polynomial R) ^ k * Polynomial.X ∣ Polynomial.expand R l (P.map σ) := by
    rw [hP0, Polynomial.map_mul, map_mul, Polynomial.map_pow, Polynomial.map_X, map_pow,
      Polynomial.expand_X, ← pow_mul, ← pow_succ]
    refine Dvd.dvd.mul_right (pow_dvd_pow _ ?_) _
    have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
  have h2 := h1.trans h
  have h3 : E ^ M * P = Polynomial.X ^ k * (E ^ M * P0) := by rw [hP0]; ring
  rw [h3, mul_dvd_mul_iff_left (pow_ne_zero _ Polynomial.X_ne_zero)] at h2
  rcases Polynomial.prime_X.dvd_or_dvd h2 with h4 | h4
  · exact hE (Polynomial.X_dvd_iff.mp (Polynomial.prime_X.dvd_of_dvd_pow h4))
  · exact hnd h4

theorem coeff_zero_ne_zero_of_frobenius_dvd_pow_mul :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P E : Polynomial (Wq l a)) (M : ℕ), P.Monic → E.coeff 0 ≠ 0 →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ E ^ M * P → P.coeff 0 ≠ 0 := by
  intro l hl a _ P E M hP hE h
  exact coeff_zero_ne_zero_of_expand_map_dvd l hl.out.two_le _ P E M hP.ne_zero hE h

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.FrobeniusPower

open Polynomial

theorem ringHom_eq_pow_frob (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F] [CharP F p]
    (φ : F →+* F) : ∃ m : ℕ, ∀ x : F, φ x = x ^ p ^ m := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let ψ : F →ₐ[ZMod p] F :=
    { φ with
      commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (φ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }
  have hinj : Function.Injective ψ := ψ.toRingHom.injective
  let σ : F ≃ₐ[ZMod p] F := AlgEquiv.ofBijective ψ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σ
  refine ⟨n, fun x => ?_⟩
  have h1 : σ x = φ x := rfl
  rw [← h1, ← hn, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

theorem finite_Fq (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [NeZero a] : Finite (GlobalTheory.BKReal.Fq l a) := by
  have hq : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) hl.out.one_lt
  have hp : (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]) ≠ 0 := by
    intro h
    have h2 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f (l ^ a)) h
    simp only [coeff_sub, coeff_X_pow, coeff_X, if_true, coeff_zero, if_neg hq.ne] at h2
    simp at h2
  have hsub : ((GlobalTheory.BKReal.resSub l a : Subring (Formalism.BasicNotions.Loc.OCb l)) : Set (Formalism.BasicNotions.Loc.OCb l)) ⊆
      {x | (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]).IsRoot x} := by
    intro x hx
    have hx' : iterateFrobenius (Formalism.BasicNotions.Loc.OCb l) l a x = x := hx
    rw [iterateFrobenius_def] at hx'
    show Polynomial.eval x (X ^ (l ^ a) - X) = 0
    rw [eval_sub, eval_pow, eval_X, hx', sub_self]
  have h : Finite ↥(GlobalTheory.BKReal.resSub l a) := ((Polynomial.finite_setOf_isRoot hp).subset hsub).to_subtype
  exact h

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [inst : NeZero a]
    (φ : GlobalTheory.BKReal.Fq l a →+* GlobalTheory.BKReal.Fq l a), ∃ (m : ℕ), ∀ (x : GlobalTheory.BKReal.Fq l a),
      (φ : GlobalTheory.BKReal.Fq l a → GlobalTheory.BKReal.Fq l a) x = x ^ l ^ m := by
  intro l hl a _ φ
  haveI := finite_Fq l a
  haveI : IsDomain (GlobalTheory.BKReal.Fq l a) := inferInstanceAs (IsDomain ↥(GlobalTheory.BKReal.resSub l a))
  haveI : CharP (GlobalTheory.BKReal.Fq l a) l :=
    inferInstanceAs (CharP ↥(GlobalTheory.BKReal.resSub l a) l)
  letI : Field (GlobalTheory.BKReal.Fq l a) := (Finite.isDomain_to_isField _).toField
  exact ringHom_eq_pow_frob l (GlobalTheory.BKReal.Fq l a) φ

end GlobalTheory.FrobeniusPower
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKReal

theorem constantCoeff_frobS_apply (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (p : (Wq l a)⟦X⟧) :
    constantCoeff (frobS l a p) = sigma l a (constantCoeff p) := by
  simp only [frobS]
  simp only [RingHom.coe_comp, Function.comp_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
  simp

theorem eisPoly_distinguished_complete : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) ∧ IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧ := by
  intro l _ a _ Ep ⟨hmon, hdeg, hdvd, w, hw⟩
  constructor
  · have hφ := (deltaS l a).φ_eq (Ep : (Wq l a)⟦X⟧)
    have h1 := congrArg constantCoeff hφ
    rw [show (deltaS l a).φ (Ep : (Wq l a)⟦X⟧) = frobS l a Ep from rfl, constantCoeff_frobS_apply] at h1
    simp only [Polynomial.constantCoeff_coe, map_add (f := _), map_pow, map_mul, map_natCast, hw] at h1
    set c := constantCoeff ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) with hc
    obtain ⟨k, hk⟩ : ∃ k, l = k + 2 := ⟨l - 2, by have := (Fact.out : l.Prime).two_le; omega⟩
    have h2 : c = sigma l a (w : Wq l a) - (l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l := by
      have hl0 : (l : Wq l a) ≠ 0 := WittVector.p_nonzero l (Fq l a)
      apply mul_left_cancel₀ hl0
      have : ((l : Wq l a) * w) ^ l = (l : Wq l a) * ((l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l) := by
        have e : (l : Wq l a) ^ l = (l : Wq l a) ^ (k + 2) := by rw [← hk]
        rw [mul_pow, e]; ring
      rw [this] at h1
      linear_combination -h1
    rw [isUnit_iff_constantCoeff, ← hc, h2]
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [← WittVector.constantCoeff_apply]
    simp only [map_sub, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow k.succ_ne_zero, zero_mul, sub_zero]
    rw [WittVector.constantCoeff_apply, coeff_sigma, ← WittVector.constantCoeff_apply]
    exact pow_ne_zero _ ((w.isUnit.map (WittVector.constantCoeff (p := l) (R := Fq l a))).ne_zero)
  · set e := Ep.natDegree with he
    haveI : NeZero e := ⟨hdeg.ne'⟩
    have hP : Polynomial.C (l : Wq l a) ∣ Ep - Polynomial.X ^ e := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases lt_trichotomy i e with h | rfl | h
      · rw [if_neg h.ne, sub_zero]; exact hdvd i h
      · have h1 : Ep.coeff e = 1 := hmon.coeff_natDegree
        rw [if_pos rfl, h1, sub_self]; exact dvd_zero _
      · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_zero]; exact dvd_zero _
    obtain ⟨q, hq⟩ := hP
    have hS : (Ep : (Wq l a)⟦X⟧) = X ^ e + (l : (Wq l a)⟦X⟧) * (q : (Wq l a)⟦X⟧) := by
      have := congrArg (fun p : Polynomial (Wq l a) => (p : (Wq l a)⟦X⟧)) hq
      simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
        map_natCast] at this
      have hc : ((l : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = l := map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l a)) l
      rw [hc] at this
      linear_combination this
    have hJ : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)} =
        Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {eis l a e} := by
      apply le_antisymm
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem, hS,
          show (X : (Wq l a)⟦X⟧) ^ e + (l : (Wq l a)⟦X⟧) * q = eis l a e + (l : (Wq l a)⟦X⟧) * (q - 1) by
            rw [eis]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem,
          show eis l a e = (Ep : (Wq l a)⟦X⟧) + (l : (Wq l a)⟦X⟧) * (1 - q) by rw [eis, hS]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    rw [hJ]
    exact complete_eis l a e

end GlobalTheory.BKReal
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem conj_norm_eq_of_minpoly_root :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (z z' : Om l),
    Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ‖z'‖ = ‖z‖ := by
  intro l _ a _ z z' h
  have hint : IsIntegral (↥(Kunr l a)) z := Algebra.IsIntegral.isIntegral z
  have hm : minpoly (↥(Kunr l a)) z' = minpoly (↥(Kunr l a)) z :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) h (minpoly.monic hint)).symm
  obtain ⟨τ, hτ⟩ := ((Normal.minpoly_eq_iff_mem_orbit (Om l)).1 hm)
  have hτ' : τ • z = z' := hτ
  rw [← hτ']
  exact (spectralNorm_eq_of_equiv (τ.restrictScalars ℚ_[l]) z).symm

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem weierstrass_prep_not_dvd_l : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : (Wq l a)⟦X⟧), ¬ (l : (Wq l a)⟦X⟧) ∣ g →
    ∃ (P : Polynomial (Wq l a)) (U : (Wq l a)⟦X⟧), IsUnit U ∧ P.Monic ∧
      (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) ∧ g = U * (P : (Wq l a)⟦X⟧) := by
  intro l _ a _ g hg
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have hsurj : Function.Surjective (WittVector.constantCoeff (p := l) (R := Fq l a)) :=
    fun x => ⟨WittVector.teichmuller l x, by simp⟩
  have hm : IsLocalRing.maximalIdeal (Wq l a) = Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff]
    haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact (IsLocalRing.eq_maximalIdeal this).symm
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (Wq l a)) (Wq l a) := hm ▸ inferInstance
  have hg' : g.map (IsLocalRing.residue (Wq l a)) ≠ 0 := by
    intro h0
    apply hg
    apply dvd_of_map_eq_zero l a g
    ext n
    have h1 : IsLocalRing.residue (Wq l a) (coeff n g) = 0 := by
      simpa using congrArg (coeff n) h0
    rw [IsLocalRing.residue_eq_zero_iff, hm, ← WittVector.ker_constantCoeff, RingHom.mem_ker] at h1
    simpa using h1
  obtain ⟨f, h, H⟩ := g.exists_isWeierstrassFactorization hg'
  refine ⟨f, h, H.isUnit, H.isDistinguishedAt.monic, fun i hi => ?_, ?_⟩
  · have := H.isDistinguishedAt.mem hi
    rw [hm] at this
    exact Ideal.mem_span_singleton.1 this
  · rw [H.eq_mul, mul_comm]

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem bkStr_quotient_equiv : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [Algebra (Wq l a) O] (π : O) (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → (Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f) → ∃ str : O ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)}), ∀ f : Polynomial (Wq l a), str (Polynomial.aeval π f) = Ideal.Quotient.mk _ (f : (Wq l a)⟦X⟧) := by
  intro l _ a _ O _ _ π Ep hE hπ
  obtain ⟨hmon, -, hdvd, -⟩ := hE
  obtain ⟨h0, hsurj, hker⟩ := hπ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have H : Ep.IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun hn => Ideal.mem_span_singleton.2 (hdvd _ hn)
      monic := hmon }
  have hK : RingHom.ker (Polynomial.aeval (R := Wq l a) π) = Ideal.span {Ep} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · exact hker f
    · rintro ⟨g, rfl⟩
      simp [h0]
  let e1 := Ideal.quotientKerAlgEquivOfSurjective (f := Polynomial.aeval (R := Wq l a) π)
    (fun x => hsurj x)
  let e2 := Ideal.quotientEquivAlgOfEq (Wq l a) hK
  let e := (e1.symm.trans (e2.trans H.algEquivQuotient)).toRingEquiv
  refine ⟨e, fun f => ?_⟩
  have h1 : e1.symm (Polynomial.aeval π f) = Ideal.Quotient.mk _ f := by
    apply e1.injective
    simp only [AlgEquiv.apply_symm_apply, e1]
    rfl
  simp only [e, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, h1]
  simp [e2, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory

theorem expand_map_dvd_of_frobS_dvd : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P Q : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → frobS l a (P : (Wq l a)⟦X⟧) ∣ (Q : (Wq l a)⟦X⟧) →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ Q := by
  intro l hl a _ P Q hP hdvd hQ
  have hl0 : 0 < l := hl.out.pos
  set σ : Wq l a →+* Wq l a := (sigma l a : Wq l a →+* Wq l a) with hσ
  have hσinj : Function.Injective σ := (sigma l a).injective
  have hcoe : frobS l a (P : (Wq l a)⟦X⟧) =
      ((Polynomial.expand (Wq l a) l (P.map σ) : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) := by
    refine PowerSeries.ext fun n => ?_
    change PowerSeries.coeff n (PowerSeries.map σ (PowerSeries.expand l hl.out.ne_zero (P : (Wq l a)⟦X⟧))) = _
    rw [PowerSeries.coeff_map, PowerSeries.coeff_expand, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_expand hl0]
    split_ifs <;> simp [Polynomial.coeff_map]
  rw [hcoe] at hQ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have hmon : (Polynomial.expand (Wq l a) l (P.map σ)).Monic := (hP.map σ).expand hl0
  have hdeg : (Polynomial.expand (Wq l a) l (P.map σ)).natDegree = P.natDegree * l := by
    rw [Polynomial.natDegree_expand, Polynomial.natDegree_map_eq_of_injective hσinj]
  have H : (Polynomial.expand (Wq l a) l (P.map σ)).IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun {n} hn => by
        rw [Ideal.mem_span_singleton, Polynomial.coeff_expand hl0]
        rw [hdeg] at hn
        split_ifs with h
        · rw [Polynomial.coeff_map]
          have hlt : n / l < P.natDegree := by
            rw [Nat.div_lt_iff_lt_mul hl0]; exact hn
          obtain ⟨c, hc⟩ := hdvd _ hlt
          refine ⟨σ c, ?_⟩
          rw [hc, map_mul, map_natCast]
        · exact dvd_zero _
      monic := hmon }
  exact GlobalTheory.NB.LT.poly_dvd_of_dvd H hQ

end GlobalTheory
end
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ →
      ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ := by
  first | exact @GlobalTheory.JSW.isRapidInf_mul_adCoef | exact GlobalTheory.JSW.isRapidInf_mul_adCoef | (intros; apply GlobalTheory.JSW.isRapidInf_mul_adCoef <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

theorem _root_.GlobalTheory.T.hodgeTateSymbolMatrix_isUnit_det : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K : FinExt l} {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → (∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) → ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i) → LinearIndependent P.R.BdR u → IsUnit (colHT J u k).det := by
  first | (exact @GlobalTheory.HTBasis.colHT_isUnit_det) | (exact GlobalTheory.HTBasis.colHT_isUnit_det) | (intros; apply GlobalTheory.HTBasis.colHT_isUnit_det  <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_isFundamentalDomain_rationalUpperUnitriangular : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (μ : Measure (GA E a)),
    ∃ 𝓕₀ : Set (GA E a), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
  first | exact @GlobalTheory.CellDec.exists_isFundamentalDomain_NE | exact GlobalTheory.CellDec.exists_isFundamentalDomain_NE | (intros; apply GlobalTheory.CellDec.exists_isFundamentalDomain_NE <;> assumption)
end
