module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Formalism.ConjugateSelfDual.Bundle001
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
open scoped nonZeroDivisors

namespace GlobalTheory.HilbertThetaSeries.DualIdele

variable {K : Type} [Field K] [NumberField K]

theorem count_span_int (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r)) =
      -WithZero.log (v.valuation K (algebraMap (𝓞 K) K r)) := by
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
    (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]),
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hr, WithZero.log_exp,
    neg_neg]

theorem count_span (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = -WithZero.log (v.valuation K x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ x
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hr : r ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs
  have e : IsLocalization.mk' K r s * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K r :=
    IsLocalization.mk'_spec K r s
  have e2 := congrArg (FractionalIdeal.count K v) (congrArg (FractionalIdeal.spanSingleton (𝓞 K)⁰) e)
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hx) ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hs'),
    count_span_int v hs, count_span_int v hr] at e2
  have e3 := congrArg (v.valuation K) e
  rw [map_mul] at e3
  have hv1 : v.valuation K (algebraMap (𝓞 K) K s) ≠ 0 := (map_ne_zero _).mpr hs'
  have hv2 : v.valuation K (IsLocalization.mk' K r s) ≠ 0 := (map_ne_zero _).mpr hx
  rw [← e3, WithZero.log_mul hv2 hv1] at e2
  linarith

theorem exists_ideal (y : (Af K)ˣ) : ∃ I : FractionalIdeal (𝓞 K)⁰ K, I ≠ 0 ∧
    ∀ w, FractionalIdeal.count K w I = -WithZero.log (Valued.v (pLoc K w (y : Af K))) := by
  have hy := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  refine ⟨∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
    (-WithZero.log (Valued.v (pLoc K w (y : Af K)))), ?_, fun w => ?_⟩
  · refine finprod_induction (fun I : FractionalIdeal (𝓞 K)⁰ K => I ≠ 0) one_ne_zero
      (fun _ _ => mul_ne_zero) fun w => zpow_ne_zero _ ?_
    exact FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot
  · refine FractionalIdeal.count_finprod K w (fun w => -WithZero.log (Valued.v (pLoc K w (y : Af K)))) ?_
    filter_upwards [hy] with v hv
    have : Valued.v (pLoc K v (y : Af K)) = 1 := hv
    rw [this, WithZero.log_one, neg_zero]

theorem genD_of_trace : ∀ (F : Type) [Field F] [NumberField F] (y : (Af F)ˣ) (ξ : F), ξ ≠ 0 → (∀ b : F, (∀ w, w.valuation F b ≤ Valued.v (pLoc F w (y : Af F))) → ∃ n : ℤ, Algebra.trace ℚ F (ξ * b) = n) → ∃ 𝔪, GenD (algebraMap F (Af F) ξ * (y : Af F)) 𝔪 := by
  intro F _ _ y ξ hξ h
  obtain ⟨I, hI, hc⟩ := exists_ideal y
  have hy0 : ∀ w, Valued.v (pLoc F w (y : Af F)) ≠ 0 := fun w =>
    (map_ne_zero _).2 ((FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 w)
  have hmem : ξ ∈ FractionalIdeal.dual ℤ ℚ I := by
    rw [FractionalIdeal.mem_dual hI]
    intro b hb
    obtain ⟨n, hn⟩ := h b fun w => by
      rcases eq_or_ne b 0 with rfl | hb0
      · simp
      have h1 := FractionalIdeal.count_mono F w ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hb0)
        (FractionalIdeal.spanSingleton_le_iff_mem.2 hb)
      rw [hc, count_span w hb0, neg_le_neg_iff] at h1
      exact (WithZero.log_le_log ((map_ne_zero _).2 hb0) (hy0 w)).1 h1
    exact ⟨n, by rw [Algebra.traceForm_apply]; simpa using hn.symm⟩
  have hD := FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
  have hd := coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hd0 : (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := hd ▸ inv_ne_zero hD
  have hs0 : FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ ≠ 0 := (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hξ
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ * (I * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)) ≤ 1 := by
    have h1 := FractionalIdeal.spanSingleton_le_iff_mem.2 hmem
    rw [FractionalIdeal.dual_eq_mul_inv] at h1
    refine (mul_le_mul_left h1 _).trans (le_of_eq ?_)
    rw [hd]
    field_simp
  obtain ⟨𝔪, h𝔪⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hm0 : 𝔪 ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.1 (h𝔪 ▸ mul_ne_zero hs0 (mul_ne_zero hI hd0))
  refine ⟨𝔪, hm0, fun w => ?_⟩
  have h2 := congrArg (FractionalIdeal.count F w) h𝔪
  rw [FractionalIdeal.count_mul F w hs0 (mul_ne_zero hI hd0), FractionalIdeal.count_mul F w hI hd0,
    FractionalIdeal.count_coe F w hm0, FractionalIdeal.count_coe F w (FractionalIdeal.coeIdeal_ne_zero.1 hd0),
    hc, count_span w hξ] at h2
  have h3 : Valued.v (pLoc F w (algebraMap F (Af F) ξ)) = w.valuation F ξ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ξ
  have hx0 : w.valuation F ξ ≠ 0 := (map_ne_zero _).2 hξ
  rw [map_mul, map_mul, h3, ← WithZero.exp_log hx0, ← WithZero.exp_log (hy0 w), ← WithZero.exp_add]
  congr 1
  unfold ordI
  linarith

end GlobalTheory.HilbertThetaSeries.DualIdele
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.IdeleAbs

theorem not_dvd_absNorm_of_not_mem {F : Type} [Field F] [NumberField F] (p : ℕ) [hp : Fact p.Prime]
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) : ¬ p ∣ Ideal.absNorm w.asIdeal := by
  intro h
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have := w.isPrime
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
  have h1 : ((p : ℕ) : 𝓞 F ⧸ w.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.out.one_lt.ne hx
  have h2 : ((p : ℕ) : 𝓞 F ⧸ w.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa using h2

theorem norm_natCast_eq_one (p : ℕ) [Fact p.Prime] (N : ℕ) (h : ¬ p ∣ N) : ‖((N : ℚ) : ℚ_[p])‖ = 1 := by
  rw [Padic.eq_padicNorm]
  exact_mod_cast (padicNorm.nat_eq_one_iff N).2 h

theorem absF_eq_rat (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (z : (Af F)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → Valued.v (pLoc F w (z : Af F)) = 1) :
    ∃ r : ℚ, 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ absF z = r := by
  have key : ∃ r : ℚ, 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ (r : ℝ) = absF z := by
    refine finprod_induction (fun t : ℝ => ∃ r : ℚ, 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ (r : ℝ) = t) ⟨1, one_pos, by simp, by simp⟩ ?_ ?_
    · rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
      exact ⟨a * b, mul_pos ha hb, by rw [Rat.cast_mul, norm_mul, ha', hb', one_mul], by rw [Rat.cast_mul]⟩
    · intro w
      by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
      · refine ⟨1, one_pos, by simp, ?_⟩
        rw [FinitePlace.norm_def, hz w hw, map_one]
        simp
      · have hne : Valued.v (pLoc F w (z : Af F)) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 (z.isUnit.map (pLoc F w)).ne_zero
        have hN : 0 < Ideal.absNorm w.asIdeal :=
          Nat.pos_of_ne_zero fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
        refine ⟨(Ideal.absNorm w.asIdeal : ℚ) ^ (WithZero.unzero hne).toAdd, zpow_pos (by exact_mod_cast hN) _, ?_, ?_⟩
        · rw [Rat.cast_zpow, norm_zpow, norm_natCast_eq_one p _ (not_dvd_absNorm_of_not_mem p w hw), one_zpow]
        · rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hne]
          push_cast
          rw [WithZero.toAdd_unzero_eq_log hne]
  obtain ⟨r, h1, h2, h3⟩ := key
  exact ⟨r, h1, h2, h3.symm⟩

end GlobalTheory.HilbertThetaSeries.IdeleAbs
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.KMem

variable {F : Type} [Field F] [NumberField F]

theorem mem_Ohat_iff {x : Af F} : x ∈ Ohat F ↔ ∀ w, Valued.v (pLoc F w x) ≤ 1 := by
  simp only [Ohat, Subring.mem_iInf, Subring.mem_comap, ValuationSubring.mem_toSubring,
    HeightOneSpectrum.mem_adicCompletionIntegers]

theorem eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = a * b := h.symm
    _ ≤ a * 1 := by gcongr
    _ = a := mul_one a

theorem det_le {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (A : Matrix (Fin 2) (Fin 2) K) (h : ∀ i j, v (A i j) ≤ 1) : v A.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (v.map_sub _ _).trans (max_le ?_ ?_) <;> rw [v.map_mul]
  · exact mul_le_one' (h 0 0) (h 1 1)
  · exact mul_le_one' (h 0 1) (h 1 0)

theorem det_mul_det_inv (g : GL (Fin 2) (Af F)) :
    (g : Matrix (Fin 2) (Fin 2) (Af F)).det * ((g⁻¹ : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)).det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem v_det (g : GL (Fin 2) (Af F)) (w : HeightOneSpectrum (𝓞 F)) (h : ∀ i j, Valued.v (pLoc F w (g.val i j)) ≤ 1) :
    Valued.v (pLoc F w g.val.det) ≤ 1 := by
  rw [RingHom.map_det]
  exact det_le _ _ h

theorem mem_KLev_iff (u : GL (Fin 2) (Af F)) :
    u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1 := by
  rw [mem_KLev]
  constructor
  · rintro ⟨ha, hb, -⟩
    have ha' : ∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1 := fun w i j => mem_Ohat_iff.1 (ha i j) w
    have hb' : ∀ w i j, Valued.v (pLoc F w ((u⁻¹ : GL (Fin 2) (Af F)).val i j)) ≤ 1 :=
      fun w i j => mem_Ohat_iff.1 (hb i j) w
    refine ⟨ha', fun w => eq_one_of_mul (v_det u w (ha' w)) (v_det _ w (hb' w)) ?_⟩
    rw [← Valuation.map_mul, ← map_mul, det_mul_det_inv, map_one, Valuation.map_one]
  · rintro ⟨ha, hd⟩
    have hinv : ∀ w, Valued.v (pLoc F w (((Matrix.GeneralLinearGroup.det u)⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
      intro w
      have h1 : Valued.v (pLoc F w ((Matrix.GeneralLinearGroup.det u : (Af F)ˣ) : Af F)) *
          Valued.v (pLoc F w (((Matrix.GeneralLinearGroup.det u)⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, Units.mul_inv, map_one, Valuation.map_one]
      rw [Matrix.GeneralLinearGroup.val_det_apply, hd w, one_mul] at h1
      exact h1
    have hO : ∀ a b, u a b ∈ Ohat F := fun a b => mem_Ohat_iff.2 fun w => ha w a b
    refine ⟨hO, fun a b => mem_Ohat_iff.2 fun w => ?_, fun a b => ⟨u a b - (1 : Matrix (Fin 2) (Fin 2) (Af F)) a b, ?_, by simp⟩⟩
    · rw [Matrix.coe_units_inv, Matrix.inv_def, ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit,
        Matrix.smul_apply, smul_eq_mul, map_mul, Valuation.map_mul, hinv w, one_mul, Matrix.adjugate_fin_two]
      fin_cases a <;> fin_cases b <;> simp [ha w]
    · refine sub_mem (hO a b) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _

end GlobalTheory.HilbertThetaSeries.KMem


open GlobalTheory.HilbertThetaSeries.KMem in
theorem GlobalTheory.HilbertThetaSeries.kMem : ∀ (F : Type) [Field F] [NumberField F], (∀ u : GL (Fin 2) (Af F), u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1) ∧ (∀ (u : (Af F)ˣ) (x : Af F), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → (∀ w, Valued.v (pLoc F w x) ≤ 1) → aff u x ∈ KLev F 2 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ KLev F 2 1) ∧ (∀ w, ∀ g ∈ K1 w 0, locGL F 2 w g ∈ KLev F 2 1) ∧ (∀ (x : F) w, Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x) ∧ ∀ x : F, (∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1) ↔ IsIntegral ℤ x := by
  intro F _ _
  refine ⟨mem_KLev_iff, fun u x hu hx => ⟨?_, ?_⟩, fun w g hg => ?_, fun x w => ?_, fun x => ?_⟩
  · refine (mem_KLev_iff _).2 ⟨fun w i j => ?_, fun w => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [aff, (hu w).le, hx w]
    · simp [aff, Matrix.det_fin_two, hu w]
  · refine (mem_KLev_iff _).2 ⟨fun w i j => ?_, fun w => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, (hu w).le]
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two, hu w]
  · obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hg
    have hk : ∀ i j, Valued.v ((k.val i j : w.adicCompletionIntegers F) : w.adicCompletion F) ≤ 1 :=
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (k.val i j).2
    refine (mem_KLev_iff _).2 ⟨fun v i j => ?_, fun v => ?_⟩
    · change Valued.v ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w _)).val i j) ≤ 1
      by_cases hv : v = w
      · subst hv; rw [pLoc_locGL]; exact hk i j
      · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    · rw [RingHom.map_det]
      change Valued.v ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w _)).val.det) = 1
      by_cases hv : v = w
      · subst hv
        rw [pLoc_locGL]
        have e : ((Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers F).subtype k).val).det =
            (((Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) := by
          rw [Matrix.GeneralLinearGroup.val_det_apply]
          exact ((v.adicCompletionIntegers F).subtype.map_det k.val).symm
        rw [e]
        refine eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers F)ˣ).val.2)
          ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletionIntegers F)ˣ).val.2) ?_
        rw [← Valuation.map_mul]
        have h := congrArg (fun y : v.adicCompletionIntegers F => (y : v.adicCompletion F)) (Matrix.GeneralLinearGroup.det k).mul_inv
        exact (congrArg Valued.v h).trans (Valuation.map_one _)
      · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.det_one, Valuation.map_one]
  · exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  · constructor
    · intro h
      obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x h
      exact NumberField.RingOfIntegers.isIntegral_coe r
    · intro h w
      have e : x = algebraMap (𝓞 F) F ⟨x, h⟩ := rfl
      rw [e]
      exact HeightOneSpectrum.valuation_le_one w _

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization : ∀ (F : Type) [Field F] [NumberField F], (∀ u : GL (Fin 2) (Af F), u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1) ∧ (∀ (u : (Af F)ˣ) (x : Af F), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → (∀ w, Valued.v (pLoc F w x) ≤ 1) → aff u x ∈ KLev F 2 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ KLev F 2 1) ∧ (∀ w, ∀ g ∈ K1 w 0, locGL F 2 w g ∈ KLev F 2 1) ∧ (∀ (x : F) w, Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x) ∧ ∀ x : F, (∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1) ↔ IsIntegral ℤ x := by
  first | exact @GlobalTheory.HilbertThetaSeries.kMem | exact GlobalTheory.HilbertThetaSeries.kMem | (intros; apply GlobalTheory.HilbertThetaSeries.kMem <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem freeOrbit_prime_dvd_card {p : ℕ} [Fact p.Prime] {α : Type} (σ : α → α) (F : Finset α)
    (hF : ∀ x ∈ F, σ x ∈ F) (hp : ∀ x ∈ F, σ^[p] x = x) (hfree : ∀ x ∈ F, σ x ≠ x) :
    p ∣ F.card := by
  classical
  let f : Function.End F := fun y => ⟨σ y, hF y y.2⟩
  have hf : ∀ (n : ℕ) (y : F), (((f ^ n) y : F) : α) = σ^[n] y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', Function.iterate_succ_apply', ← ih y]
      rfl
  have h1 : f ^ p ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    rw [pow_one, hf]
    exact hp y y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) h1
  have h3 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨y, hy⟩
    exact hfree y y.2 (congrArg Subtype.val hy)
  rw [h3, Fintype.card_coe] at h2
  exact Nat.modEq_zero_iff_dvd.mp h2

theorem norm_prime_Qbar_eq (p : ℕ) [Fact p.Prime] : ‖(p : Qbar p)‖ = (p : ℝ)⁻¹ := by
  have h := PadicAlgCl.valuation_p p
  rw [← PadicAlgCl.valuation_coe, h]
  simp

theorem norm_sum_free_orbits_le : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  intro p _ ι α σ s Φ hs hp hfree hinv hle
  classical
  have hna := PadicAlgCl.isNonarchimedean p
  have key : ∀ c ∈ s.image Φ,
      ‖ι.symm ((s.filter (fun x => Φ x = c)).card • c)‖ ≤ (p : ℝ)⁻¹ := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    have hd : p ∣ (s.filter (fun x => Φ x = Φ y)).card := by
      apply freeOrbit_prime_dvd_card σ
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hs x hx.1, (hinv x hx.1).trans hx.2⟩
      · intro x hx
        exact hp x (Finset.mem_filter.1 hx).1
      · intro x hx
        exact hfree x (Finset.mem_filter.1 hx).1
    obtain ⟨k, hk⟩ := hd
    rw [map_nsmul, nsmul_eq_mul, norm_mul, hk, Nat.cast_mul, norm_mul, norm_prime_Qbar_eq]
    have h1 : ‖((k : ℕ) : Qbar p)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
    have h2 := hle y hy
    calc (p : ℝ)⁻¹ * ‖((k : ℕ) : Qbar p)‖ * ‖ι.symm (Φ y)‖ ≤ (p : ℝ)⁻¹ * 1 * 1 := by gcongr
      _ = (p : ℝ)⁻¹ := by ring
  have hsum : ∑ x ∈ s, Φ x = ∑ c ∈ s.image Φ, (s.filter (fun x => Φ x = c)).card • c :=
    Finset.sum_comp (fun c => c) Φ

  rw [hsum, map_sum]
  generalize s.image Φ = T at key
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (hna _ _).trans (max_le (key a (Finset.mem_insert_self a T))
      (ih fun c hc => key c (Finset.mem_insert_of_mem hc)))

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.norm_sum_free_orbits_le_inv_prime : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | exact GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | (intros; apply GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le <;> assumption)
end
