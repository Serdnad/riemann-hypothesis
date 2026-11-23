module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.RingTheory.DedekindDomain.Different
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

namespace DictInter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def tau (w : E) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ
    TensorProduct.map ((Algebra.trace F E) ∘ₗ LinearMap.mulLeft F w) LinearMap.id

lemma tau_tmul (w e : E) (a : Af F) : tau w (e ⊗ₜ[F] a) = Algebra.trace F E (w * e) • a := by
  first
    | simp [tau]
    | rfl


variable (F E) in
def dualSet : Set E := {w | ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range}

lemma tau_mul_left (w a : E) (r : E ⊗[F] Af F) :
    tau w ((a ⊗ₜ[F] (1 : Af F)) * r) = tau (w * a) r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tau_tmul, tau_tmul, mul_assoc]
  | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy]

lemma tau_mul_right (w : E) (b : Af F) (r : E ⊗[F] Af F) :
    tau w (((1 : E) ⊗ₜ[F] b) * r) = b * tau w r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tau_tmul, tau_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]

lemma tau_incl (w e : E) :
    tau w (Formalism.UG.inclE (F := F) (Af F) e) = algebraMap F (Af F) (Algebra.trace F E (w * e)) := by
  show tau w (e ⊗ₜ[F] (1 : Af F)) = _
  rw [tau_tmul, Algebra.algebraMap_eq_smul_one]

lemma algebraMap_mem_intAd (x : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F x) ∈ Formalism.UG.intAd F := by
  intro v
  have h1 : Valued.v (((algebraMap (𝓞 F) F x : F)) : v.adicCompletion F) ≤ 1 := by
    first
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
  first
    | exact h1
    | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1

lemma of_algebraMap_mem_intAd (f : F) (h : algebraMap F (Af F) f ∈ Formalism.UG.intAd F) :
    f ∈ (algebraMap (𝓞 F) F).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) f ?_
  intro v
  have hv : Valued.v ((f : F) : v.adicCompletion F) ≤ 1 := h v
  first
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at hv

def tSet (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Set (E ⊗[F] Af F) :=
  {r | ∀ w ∈ dualSet F E, tau w r ∈ Formalism.UG.intAd F}

lemma one_mem_tSet : (1 : E ⊗[F] Af F) ∈ tSet F E := by
  show ∀ w ∈ dualSet F E, tau w ((1 : E) ⊗ₜ[F] (1 : Af F)) ∈ Formalism.UG.intAd F
  intro w hw
  have hw1 := (show ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range from hw) 1
  obtain ⟨x, hx⟩ := hw1
  rw [tau_tmul, ← Algebra.algebraMap_eq_smul_one]
  have hx' : Algebra.trace F E (w * (1 : E)) = algebraMap (𝓞 F) F x := by
    rw [hx]
    rfl
  rw [hx']
  exact algebraMap_mem_intAd x

private theorem mul_algebraMap_mem_dualSet {w : E} (hw : w ∈ dualSet F E) (a : 𝓞 E) :
    w * algebraMap (𝓞 E) E a ∈ dualSet F E := by
  show ∀ b : 𝓞 E, Algebra.trace F E (w * algebraMap (𝓞 E) E a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
  intro b
  have h := (show ∀ b : 𝓞 E, Algebra.trace F E (w * (b : E)) ∈ (algebraMap (𝓞 F) F).range from hw) (a * b)
  rw [mul_assoc]
  exact h

lemma mem_tSet (r : E ⊗[F] Af F) (hr : r ∈ IntAf F E) : r ∈ tSet F E := by
  have hr' : r ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
      Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) := hr
  clear hr
  suffices h : ∀ s ∈ tSet F E, r * s ∈ tSet F E by
    have h1 := h 1 one_mem_tSet
    rwa [mul_one] at h1
  induction hr' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨a, rfl⟩ := he
      intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_left]
      exact (show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) _ (mul_algebraMap_mem_dualSet hw a)
    · intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_right]
      exact mul_mem hb ((show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) w hw)
  | zero =>
    intro s _
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w _
    rw [zero_mul, map_zero]
    exact zero_mem _
  | one =>
    intro s hs
    rwa [one_mul]
  | add x y _ _ hx hy =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [add_mul, map_add (f := _)]
    exact add_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
      ((show ∀ w ∈ dualSet F E, tau w (y * s) ∈ Formalism.UG.intAd F from hy s hs) w hw)
  | neg x _ hx =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [neg_mul, map_neg]
    exact neg_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
  | mul x y _ _ hx hy =>
    intro s hs
    rw [mul_assoc]
    exact hx _ (hy s hs)

end DictInter

open DictInter in
theorem dual_intersection : DInter := by
  intro F E _ _ _ _ _ e he
  have ht := mem_tSet (F := F) (E := E) _ he
  have key : ∀ w ∈ dualSet F E, Algebra.trace F E (w * e) ∈ (algebraMap (𝓞 F) F).range := by
    intro w hw
    apply of_algebraMap_mem_intAd
    rw [← tau_incl]
    exact (show ∀ w ∈ dualSet F E, tau w (Formalism.UG.inclE (F := F) (Af F) e) ∈ Formalism.UG.intAd F from ht) w hw
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    first
      | exact FractionalIdeal.dual_ne_zero (𝓞 F) F h1
      | exact FractionalIdeal.dual_ne_zero h1
  have hmem : e ∈ FractionalIdeal.dual (𝓞 F) F
      (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)) := by
    rw [FractionalIdeal.mem_dual hd]
    intro a ha
    rw [FractionalIdeal.mem_dual h1] at ha
    rw [Algebra.traceForm_apply, mul_comm]
    apply key
    show ∀ b : 𝓞 E, Algebra.trace F E (a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
    intro b
    have hb := ha (b : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨b, rfl⟩)
    rwa [Algebra.traceForm_apply] at hb
  rw [FractionalIdeal.dual_dual] at hmem
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp hmem
  exact ⟨x, hx⟩

end PIW.AdelClassFin
end
end

section

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix ComplexOrder

section Defs

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def gramTr {m N : ℕ} (J : Matrix (Fin m) (Fin m) E) (e : Fin N → Fin m → E) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j))

def IsMajFam {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ φ : E →+* ℂ, (H φ).PosDef ∧ (H φ).det = ((‖(J.map φ).det‖ : ℝ) : ℂ) ∧
    (∀ z : Fin m → ℂ, ‖star z ⬝ᵥ (J.map φ *ᵥ z)‖ ≤ (star z ⬝ᵥ (H φ *ᵥ z)).re) ∧
    H (ComplexEmbedding.conjugate φ) = (H φ).map (starRingEnd ℂ)

end Defs

def SvCodiffAt (E : Type) [Field E] [NumberField E] (δ : ℕ) : Prop :=
  ∀ y : E, (∀ a : 𝓞 E, Algebra.trace ℚ E (algebraMap (𝓞 E) E a * y) ∈ (algebraMap ℤ ℚ).range) →
    (δ : E) * y ∈ (algebraMap (𝓞 E) E).range

def SvCodiff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], ∃ δ : ℕ, 1 ≤ δ ∧ SvCodiffAt E δ

def SvMaj : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.IsHermitian → J.det ≠ 0 →
    ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ H.det = ((‖J.det‖ : ℝ) : ℂ) ∧
      ∀ z : Fin n → ℂ, ‖star z ⬝ᵥ (J *ᵥ z)‖ ≤ (star z ⬝ᵥ (H *ᵥ z)).re

def SvMajE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J → J.det ≠ 0 →
      ∃ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H

def SvBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (M : Submodule (𝓞 E) (Fin m → E)),
    M.FG → Submodule.span E (M : Set (Fin m → E)) = ⊤ →
      ∃ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e ∧ (∀ i, e i ∈ M) ∧
        ∀ x ∈ M, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i

def SvGramDet : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ m d δ : ℕ, 1 ≤ d → 1 ≤ δ → SvCodiffAt E δ → ∀ p ∈ Lat E m d,
      ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e → (∀ i, e i ∈ p.2) →
        (∀ x ∈ p.2, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i) →
          (gramTr p.1 e).det ≠ 0 ∧ |(gramTr p.1 e).det| ≤ ((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E)

def SvReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J →
      ∀ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H →
        ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, (gramTr J e).det ≠ 0 →
          ∃ R : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℝ,
            R.PosDef ∧ R.det = |((gramTr J e).det : ℝ)| ∧
              ∀ c : Fin (m * Module.finrank ℚ E) → ℤ,
                ∑ φ : E →+* ℂ, ‖φ (hform (starRingEnd E) J (∑ i, (c i : E) • e i) (∑ i, (c i : E) • e i))‖ ≤
                  (fun i => (c i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (c i : ℝ))

theorem partShort_of (hM : PartMink) (hMaj : SvMajE) (hCod : SvCodiff) (hB : SvBasis)
    (hD : SvGramDet) (hR : SvReal) : PartShort := by
  intro F E _ _ _ _ _ _ hCM m d hm hd
  obtain ⟨δ, hδ1, hδ⟩ := hCod E
  have hn1 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hN1 : 1 ≤ m * Module.finrank ℚ E :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨Kc, hK⟩ := hM _ hN1
  set S : ℝ := max Kc 0 * ((d * δ : ℕ) : ℝ) with hS
  refine ⟨((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℚ), fun p hp => ?_⟩
  obtain ⟨hherm, hdet, hfg, hspan, -, -⟩ := id hp
  obtain ⟨H, hH⟩ := hMaj F E hCM m p.1 hherm hdet
  obtain ⟨e, hlin, hemem, hegen⟩ := hB E m p.2 hfg hspan
  obtain ⟨hgd, hgb⟩ := hD F E hCM m d δ hd hδ1 hδ p hp e hlin hemem hegen
  obtain ⟨R, hRpd, hRdet, hRle⟩ := hR F E hCM m p.1 hherm H hH e hgd
  obtain ⟨c, hc0, hcR⟩ := hK R hRpd
  set x : Fin m → E := ∑ i, (c i : E) • e i with hx
  have hxmem : x ∈ p.2 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul E]
    exact p.2.toAddSubgroup.zsmul_mem (hemem i) (c i)
  have hx0 : x ≠ 0 := by
    intro h0
    apply hc0
    funext i
    have h0' : ∑ i, (c i : ℚ) • e i = 0 := by
      rw [← h0, hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul ℚ, Int.cast_smul_eq_zsmul E]
    exact_mod_cast Fintype.linearIndependent_iff.1 hlin _ h0' i
  refine ⟨x, hxmem, hx0, ?_⟩
  set a := hform (starRingEnd E) p.1 x x with ha
  have hsumle : ∑ φ : E →+* ℂ, ‖φ a‖ ≤ S := by
    have h1 := hRle c
    have hdetR : R.det ≤ ((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E) := by
      rw [hRdet]
      have h' : ((|(gramTr p.1 e).det| : ℚ) : ℝ) ≤
          ((((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E) : ℚ) : ℝ) := by exact_mod_cast hgb
      rw [Rat.cast_abs, Rat.cast_pow, Rat.cast_natCast] at h'
      exact h'
    have hR0 : 0 ≤ R.det := hRpd.det_pos.le
    have hroot : R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) ≤ ((d * δ : ℕ) : ℝ) := by
      calc R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ))
          ≤ (((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E)) ^
              ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
            Real.rpow_le_rpow hR0 hdetR (by positivity)
        _ = ((d * δ : ℕ) : ℝ) := by
            rw [one_div]; exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
    have hroot0 : 0 ≤ R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := Real.rpow_nonneg hR0 _
    calc ∑ φ : E →+* ℂ, ‖φ a‖ ≤ _ := h1
      _ ≤ Kc * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := hcR
      _ ≤ max Kc 0 * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hroot0
      _ ≤ S := mul_le_mul_of_nonneg_left hroot (le_max_right _ _)
  have hnorm : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ S ^ Module.finrank ℚ E := by
    have h2 := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)
    simp only [norm_prod] at h2
    rw [show ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ a)‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| by simp] at h2
    rw [Rat.cast_abs, h2]
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ ≤ ∏ σ : E →ₐ[ℚ] ℂ, S :=
          Finset.prod_le_prod₀ (fun σ _ => norm_nonneg _) (fun σ _ =>
            (Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ a‖) (fun φ _ => norm_nonneg _)
              (Finset.mem_univ (σ : E →+* ℂ))).trans hsumle)
      _ = S ^ Module.finrank ℚ E := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card ℚ E ℂ]
  have hfin : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ ((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℝ) :=
    hnorm.trans (Nat.le_ceil _)
  exact_mod_cast hfin

end PIW.AdelClassFin
end
end

section

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG
open scoped Matrix

section
variable {E : Type} [Field E] [StarRing E]

theorem cT_star {a b : Type} (A : Matrix a b E) : cT (starRingEnd E) A = Aᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply, starRingEnd_apply]

theorem isHerm_iff {n : Type} (J : Matrix n n E) : IsHerm (starRingEnd E) J ↔ Jᴴ = J := by
  unfold IsHerm
  rw [cT_star]

theorem hform_eq {n : Type} [Fintype n] (J : Matrix n n E) (x y : n → E) :
    hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem hform_mulVec {n a : Type} [Fintype n] [Fintype a] (J : Matrix n n E) (A B : Matrix n a E)
    (x y : a → E) :
    hform (starRingEnd E) J (A *ᵥ x) (B *ᵥ y) = hform (starRingEnd E) (cT (starRingEnd E) A * J * B) x y := by
  rw [hform_eq, hform_eq, cT_star, Matrix.star_mulVec]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem hform_add_left {n : Type} [Fintype n] (J : Matrix n n E) (x x' y : n → E) :
    hform (starRingEnd E) J (x + x') y = hform (starRingEnd E) J x y + hform (starRingEnd E) J x' y := by
  simp [hform_eq, star_add, add_dotProduct]

theorem hform_single_left {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (i : n) (y : n → E) :
    hform (starRingEnd E) J (Pi.single i 1) y = (J *ᵥ y) i := by
  have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
    ext r
    by_cases h : r = i
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [hform_eq, hs]
  simp

theorem hform_single {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (i j : n) :
    hform (starRingEnd E) J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform_single_left]
  simp [Matrix.mulVec]

theorem cT_mulVec_apply {n k : Type} [Fintype n] (J : Matrix n n E) (V : Matrix n k E) (z : n → E) (i : k) :
    ((cT (starRingEnd E) V * J) *ᵥ z) i = hform (starRingEnd E) J (fun r => V r i) z := by
  rw [hform_eq, ← Matrix.mulVec_mulVec, cT_star]
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]

theorem gram_eq [NumberField E] {m k : ℕ} (J : Matrix (Fin m) (Fin m) E) (v : Fin k → Fin m → E) :
    gram J v = cT (starRingEnd E) (Matrix.of fun r i => v i r) * J * Matrix.of fun r i => v i r := by
  ext i j
  have h1 : (cT (starRingEnd E) (Matrix.of fun r i => v i r) * J * Matrix.of fun r i => v i r) i j =
      ((cT (starRingEnd E) (Matrix.of fun r i => v i r) * J) *ᵥ v j) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, cT_mulVec_apply]
  simp [PIW.AdelClassFin.gram]

end

end PIW.AdelClassFin
end
end

section

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

def SpComp : Prop :=
  ∀ (E : Type) [Field E] (k m : ℕ) (P : Matrix (Fin k) (Fin m) E) (R : Matrix (Fin m) (Fin k) E), P * R = 1 →
    k ≤ m ∧ ∃ U : Matrix (Fin m) (Fin (m - k)) E, P * U = 0 ∧ Function.Injective U.mulVec ∧
      ∀ w : Fin m → E, P *ᵥ w = 0 → ∃ y, U *ᵥ y = w

def SpDen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (X : Matrix (Fin k) (Fin k) E), ∃ D : ℕ, 1 ≤ D ∧
    ∀ i j, (D : E) * X i j ∈ (algebraMap (𝓞 E) E).range

def SpLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (m k n d D : ℕ) (J : Matrix (Fin m) (Fin m) E)
    (M : Submodule (𝓞 E) (Fin m → E)) (V : Matrix (Fin m) (Fin k) E) (U : Matrix (Fin m) (Fin n) E),
    (J, M) ∈ Lat E m d → (∀ i, (fun r => V r i) ∈ M) → 1 ≤ D →
    (cT (starRingEnd E) V * J * V).det ≠ 0 →
    (∀ i j, (D : E) * (cT (starRingEnd E) V * J * V)⁻¹ i j ∈ (algebraMap (𝓞 E) E).range) →
    cT (starRingEnd E) V * J * U = 0 → Function.Injective U.mulVec →
    (∀ w : Fin m → E, (cT (starRingEnd E) V * J) *ᵥ w = 0 → ∃ y, U *ᵥ y = w) →
    (cT (starRingEnd E) U * J * U, M.comap ((Matrix.mulVecLin U).restrictScalars (𝓞 E))) ∈ Lat E n (d * D) ∧
    ∀ z ∈ M, ∃ c : Fin k → E, (∀ i, c i ∈ (algebraMap (𝓞 E) E).range) ∧ ∃ y : Fin n → E, U *ᵥ y ∈ M ∧
      (D : E) • z = V *ᵥ c + U *ᵥ y

def SpOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (m k : ℕ), 1 ≤ k → (∀ j < m, HL E j) →
    ∀ d : ℕ, 1 ≤ d → ∀ Γ : Matrix (Fin k) (Fin k) E, Γ.det ≠ 0 → FinCl (SplitSet E m k d {Γ})

theorem partSplit_of_one (h : SpOne) : PartSplit := by
  unfold PartSplit
  unfold SpOne at h
  intro F E _ _ _ _ _ _ _ m k hk hHL d hd G hG hdet

  have h1 : ∀ Γ ∈ G, FinCl (SplitSet E m k d {Γ}) := fun Γ hΓ => h E m k hk hHL d hd Γ (hdet Γ hΓ)
  choose T hTfin hT using h1
  refine ⟨⋃ (Γ) (hΓ : Γ ∈ G), T Γ hΓ, hG.biUnion' hTfin, ?_⟩
  rintro p ⟨hpL, v, hv, hvG⟩
  obtain ⟨q, hq, hiso⟩ := hT _ hvG p ⟨hpL, v, hv, Set.mem_singleton _⟩
  exact ⟨q, Set.mem_iUnion₂.mpr ⟨_, hvG, hq⟩, hiso⟩

end PIW.AdelClassFin
end
end
