module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle175
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle117
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LatSumZ

theorem difdif (L : ℕ) (hL : 0 < L) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    dif L v (dif L v F) x = ((L : ℂ) ^ 2)⁻¹ * ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L,
      (F x - F (x + (r : ℤ) • v) - F (x + (r' : ℤ) • v) + F (x + (r' : ℤ) • v + (r : ℤ) • v)) := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set S := ∑ r ∈ Finset.range L, F (x + (r : ℤ) • v)
  set T := ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L, F (x + (r' : ℤ) • v + (r : ℤ) • v)
  have e : ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L,
      (F x - F (x + (r : ℤ) • v) - F (x + (r' : ℤ) • v) + F (x + (r' : ℤ) • v + (r : ℤ) • v))
      = (L : ℂ) * L * F x - L * S - L * S + T := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, S, T]
    rw [← Finset.mul_sum]; ring
  have e2 : ∑ r' ∈ Finset.range L, (F (x + (r' : ℤ) • v) - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, F (x + (r' : ℤ) • v + (r : ℤ) • v))
      = S - (L : ℂ)⁻¹ * T := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [e]
  simp only [dif]
  rw [e2]
  field_simp
  ring

theorem trm_zero (j : ℕ) (y : ℂ) : trm j 0 y = (y ^ j)⁻¹ := by
  simp [trm]

theorem lin_shift (τ : ℍ) (x v : ℤ × ℤ) (r : ℕ) :
    (((x + (r : ℤ) • v).1 : ℤ) : ℂ) * (τ : ℂ) + (((x + (r : ℤ) • v).2 : ℤ) : ℂ)
      = ((x.1 : ℂ) * τ + x.2) + (r : ℂ) * ((v.1 : ℂ) * τ + v.2) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast; ring

theorem lin_shift2 (τ : ℍ) (x v : ℤ × ℤ) (r' r : ℕ) :
    (((x + (r' : ℤ) • v + (r : ℤ) • v).1 : ℤ) : ℂ) * (τ : ℂ) + (((x + (r' : ℤ) • v + (r : ℤ) • v).2 : ℤ) : ℂ)
      = ((x.1 : ℂ) * τ + x.2) + (r' : ℂ) * ((v.1 : ℂ) * τ + v.2) + (r : ℂ) * ((v.1 : ℂ) * τ + v.2) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast; ring

theorem difdif_bound (j L : ℕ) (v : ℤ × ℤ) (τ : ℍ) (hj : 1 ≤ j) (hL : 0 < L) (C : ℝ)
    (hC : ∀ z a b : ℂ, z ≠ 0 → 4 * ‖a‖ ≤ ‖z‖ → 4 * ‖b‖ ≤ ‖z‖ →
      ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹‖ ≤ C * ‖a‖ * ‖b‖ / ‖z‖ ^ (j + 2))
    (x : ℤ × ℤ)
    (h1 : 1 ≤ ‖(x.1 : ℂ) * τ + x.2‖) (h4 : 4 * (L * ‖(v.1 : ℂ) * τ + v.2‖) ≤ ‖(x.1 : ℂ) * τ + x.2‖) :
    ‖dif L v (dif L v (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2))) x‖
      ≤ max C 0 * (L * ‖(v.1 : ℂ) * τ + v.2‖) ^ 2 / ‖(x.1 : ℂ) * τ + x.2‖ ^ 3 := by
  set z : ℂ := (x.1 : ℂ) * τ + x.2 with hz
  set w : ℂ := (v.1 : ℂ) * τ + v.2 with hw
  set B : ℝ := max C 0 * (L * ‖w‖) ^ 2 / ‖z‖ ^ 3 with hB
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hterm : ∀ r' ∈ Finset.range L, ∀ r ∈ Finset.range L,
      ‖trm j 0 z - trm j 0 (z + (r : ℂ) * w) - trm j 0 (z + (r' : ℂ) * w)
        + trm j 0 (z + (r' : ℂ) * w + (r : ℂ) * w)‖ ≤ B := by
    intro r' hr' r hr
    have hr'L : (r' : ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hr').le
    have hrL : (r : ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hr).le
    have na : ‖(r' : ℂ) * w‖ ≤ L * ‖w‖ := by
      rw [norm_mul, Complex.norm_natCast]; exact mul_le_mul_of_nonneg_right hr'L (norm_nonneg _)
    have nb : ‖(r : ℂ) * w‖ ≤ L * ‖w‖ := by
      rw [norm_mul, Complex.norm_natCast]; exact mul_le_mul_of_nonneg_right hrL (norm_nonneg _)
    have key := hC z ((r' : ℂ) * w) ((r : ℂ) * w) hz0 (by linarith) (by linarith)
    simp only [trm_zero]
    have eq : (z ^ j)⁻¹ - ((z + (r : ℂ) * w) ^ j)⁻¹ - ((z + (r' : ℂ) * w) ^ j)⁻¹
        + ((z + (r' : ℂ) * w + (r : ℂ) * w) ^ j)⁻¹
        = (z ^ j)⁻¹ - ((z + (r' : ℂ) * w) ^ j)⁻¹ - ((z + (r : ℂ) * w) ^ j)⁻¹
        + ((z + (r' : ℂ) * w + (r : ℂ) * w) ^ j)⁻¹ := by ring
    rw [eq]
    refine key.trans ?_
    have hpow : ‖z‖ ^ 3 ≤ ‖z‖ ^ (j + 2) := pow_le_pow_right₀ h1 (by omega)
    have hp3 : 0 < ‖z‖ ^ 3 := by positivity
    have hM : 0 ≤ max C 0 := le_max_right _ _
    calc C * ‖(r' : ℂ) * w‖ * ‖(r : ℂ) * w‖ / ‖z‖ ^ (j + 2)
        ≤ max C 0 * ‖(r' : ℂ) * w‖ * ‖(r : ℂ) * w‖ / ‖z‖ ^ (j + 2) := by
          gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (L * ‖w‖) * (L * ‖w‖) / ‖z‖ ^ (j + 2) := by gcongr
      _ ≤ max C 0 * (L * ‖w‖) * (L * ‖w‖) / ‖z‖ ^ 3 := by
          apply div_le_div_of_nonneg_left (by positivity) hp3 hpow
      _ = B := by rw [hB]; ring
  rw [difdif L hL v _ x]
  simp only [lin_shift τ, lin_shift2 τ]
  rw [← hz, ← hw]
  calc ‖((L : ℂ) ^ 2)⁻¹ * ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L,
        (trm j 0 z - trm j 0 (z + (r : ℂ) * w) - trm j 0 (z + (r' : ℂ) * w)
          + trm j 0 (z + (r' : ℂ) * w + (r : ℂ) * w))‖
      ≤ ((L : ℝ) ^ 2)⁻¹ * ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L, B := by
        rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r' hr' => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => hterm r' hr' r hr)
    _ = B := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

theorem latsum_summable : ∀ (j L : ℕ) (v : ℤ × ℤ) (τ : ℍ), 1 ≤ j → 0 < L →
    Summable fun x => ‖dif L v (dif L v (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2))) x‖ := by
  intro j L v τ hj hL
  obtain ⟨C, hC⟩ := GlobalTheory.T.second_difference_inv_pow_bound j
  set w : ℂ := (v.1 : ℂ) * τ + v.2 with hw
  set R : ℝ := max (4 * (L * ‖w‖)) 1 with hR
  have hrτ : 0 < EisensteinSeries.r τ := EisensteinSeries.r_pos τ
  set M : ℝ := R / EisensteinSeries.r τ + 1 with hM
  set K : ℝ := max C 0 * (L * ‖w‖) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  rw [← (finTwoArrowEquiv ℤ).summable_iff]
  have hs : Summable fun y : Fin 2 → ℤ => K * (EisensteinSeries.r τ ^ 3)⁻¹ * ‖y‖ ^ (-(3 : ℝ)) :=
    (EisensteinSeries.summable_one_div_norm_rpow (by norm_num : (2 : ℝ) < 3)).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  have hev : ∀ᶠ y : Fin 2 → ℤ in cofinite, M ≤ ‖y‖ := by
    rw [← cocompact_eq_cofinite]
    exact tendsto_norm_cocompact_atTop.eventually_ge_atTop M
  filter_upwards [hev] with y hy
  have hR1 : 1 ≤ R := le_max_right _ _
  have hMpos : 0 < M := by positivity
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  have hlow := EisensteinSeries.r_mul_max_le τ hy0
  have hRle : R ≤ EisensteinSeries.r τ * ‖y‖ := by
    have : EisensteinSeries.r τ * M ≤ EisensteinSeries.r τ * ‖y‖ := mul_le_mul_of_nonneg_left hy hrτ.le
    have h2 : EisensteinSeries.r τ * M = R + EisensteinSeries.r τ := by
      rw [hM]; field_simp
    linarith
  have hxe : (((finTwoArrowEquiv ℤ y).1 : ℤ) : ℂ) * (τ : ℂ) + (((finTwoArrowEquiv ℤ y).2 : ℤ) : ℂ)
      = (y 0 : ℂ) * τ + y 1 := by simp
  have hzR : R ≤ ‖((finTwoArrowEquiv ℤ y).1 : ℂ) * τ + ((finTwoArrowEquiv ℤ y).2 : ℂ)‖ := by
    rw [hxe]; linarith
  have h1 : 1 ≤ ‖((finTwoArrowEquiv ℤ y).1 : ℂ) * τ + ((finTwoArrowEquiv ℤ y).2 : ℂ)‖ :=
    le_trans (le_max_right _ _) hzR
  have h4 : 4 * (L * ‖w‖) ≤ ‖((finTwoArrowEquiv ℤ y).1 : ℂ) * τ + ((finTwoArrowEquiv ℤ y).2 : ℂ)‖ :=
    le_trans (le_max_left _ _) hzR
  have hb := difdif_bound j L v τ hj hL C hC (finTwoArrowEquiv ℤ y) h1 h4
  rw [Function.comp_apply, norm_norm]
  refine hb.trans ?_
  rw [hxe] at h1 ⊢
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hprod : 0 < EisensteinSeries.r τ * ‖y‖ := mul_pos hrτ hypos
  have hrp : ‖y‖ ^ (-(3 : ℝ)) = (‖y‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg (norm_nonneg _), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrp, ← hw]
  calc max C 0 * (L * ‖w‖) ^ 2 / ‖(y 0 : ℂ) * τ + y 1‖ ^ 3
      ≤ K / (EisensteinSeries.r τ * ‖y‖) ^ 3 := by
        rw [hK]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hprod.le hlow 3
    _ = K * (EisensteinSeries.r τ ^ 3)⁻¹ * (‖y‖ ^ 3)⁻¹ := by
        rw [mul_pow]; field_simp

end GlobalTheory.LatSumZ
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

theorem vs_valuation_eq_one_iff {K : Type} [Field K] (V : ValuationSubring K) {x : K} (hx : x ≠ 0) :
    V.valuation x = 1 ↔ x ∈ V ∧ x⁻¹ ∈ V := by
  rw [← V.valuation_le_one_iff, ← V.valuation_le_one_iff, map_inv₀]
  have h0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  constructor
  · intro h; simp [h]
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have := one_lt_inv₀ (pos_iff_ne_zero.2 h0) |>.2 hlt
    exact absurd h2 (not_le.2 this)

theorem vs_comap_valuation_eq_one_iff {K : Type} [Field K] (φ : K →+* K) (V : ValuationSubring K) {x : K}
    (hx : x ≠ 0) : (V.comap φ).valuation x = 1 ↔ V.valuation (φ x) = 1 := by
  rw [vs_valuation_eq_one_iff _ hx, vs_valuation_eq_one_iff _ ((map_ne_zero φ).2 hx),
    ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀]

theorem Tower.Un_map {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (φ : X.K →+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ)) (m : ℕ) {f : X.Kˣ} (hf : f ∈ X.Un m)
    (u : X.Kˣ) (hu : (u : X.K) = φ (f : X.K)) : u ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf _ (hφ W hW)
  refine ⟨Units.map φ.toMonoidHom a, ?_⟩
  have hne : (f : X.K) / (a : X.K) ^ m ≠ 0 := div_ne_zero f.ne_zero (pow_ne_zero _ a.ne_zero)
  rw [vs_comap_valuation_eq_one_iff φ W hne, map_div₀, map_pow] at ha
  rw [hu]
  exact ha

theorem Tower.Un_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ) (f : X.Kˣ), f ∈ X.Un m →
      (∀ (g : GQ) (u : X.Kˣ), (u : X.K) = X.sl g (f : X.K) → u ∈ X.Un m) ∧
        ∀ (s : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), (u : X.K) = X.gal s (f : X.K) → u ∈ X.Un m := by
  intro Ω _ _ _ ε X hε hj m f hf
  refine ⟨fun g u hu => ?_, fun s u hu => ?_⟩
  · exact X.Un_map (X.sl g).toRingEquiv.toRingHom
      (fun W hW => (Tower.overY_comap_sl_gal ε X hε hj W hW).1 g) m hf u hu
  · exact X.Un_map (X.gal s).toRingHom
      (fun W hW => (Tower.overY_comap_sl_gal ε X hε hj W hW).2 s) m hf u hu

end GlobalTheory.KZ
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3.CocLift

open MvPolynomial CongruenceSubgroup

theorem gamma_of_dvd {a b : ℕ} (h : a ∣ b) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma b) : δ ∈ Gamma a := by
  rw [Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have key : ∀ x : ℤ, ZMod.castHom h (ZMod a) (x : ZMod b) = (x : ZMod a) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key, h1, map_one]
  · rw [← key, h2, map_zero]
  · rw [← key, h3, map_zero]
  · rw [← key, h4, map_one]

theorem gamma_le_gam {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    δ ∈ Gam N l := by
  have h1 := Gamma_mem.mp (gamma_of_dvd hN hδ)
  have h2 := Gamma_mem.mp (gamma_of_dvd hl hδ)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]; exact ⟨h1.1, h1.2.2.2, h1.2.2.1⟩
  · rw [Gamma0_mem]; exact h2.2.2.1

theorem entries_of_gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    ∀ i j, (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := Gamma_mem.mp hδ
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem step (N l w : ℕ) [Fact l.Prime] (hN : 0 < N) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hw : Odd w)
    (Φ : (n : ℕ) → SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))) (hΦ : IsFam l w (Gam N l) Φ)
    (n : ℕ) (y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (hy : IsCoc w (Gam N l) y) (hyn : Near y (Φ n)) :
    ∃ y' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))), IsCoc w (Gam N l) y' ∧ Near y' (Φ (n + 1)) ∧
      ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (y' γ) = y γ := by
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨z', hz', hz'n⟩ := GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ (n + 1)
  set c := ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) with hc
  have L := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ n))
  have L' := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ (n + 1)))
  let r : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) := fun δ => MvPolynomial.map c (z' δ)
  have hr : IsCoc w (Gam N l) r := by
    refine ⟨fun γ hγ => (hz'.1 γ hγ).map c, fun γ hγ δ hδ => ?_⟩
    simp only [r]
    rw [hz'.2 γ hγ δ hδ, map_add (f := _), L'.2.2.2.2.1 _ c]
  have hnear : Near r y := by
    obtain ⟨M1, hM1, h1⟩ := hz'n
    obtain ⟨M2, hM2, h2⟩ := hΦ.2.2.2 n
    obtain ⟨M3, hM3, h3⟩ := hyn
    refine ⟨M1 * M2 * M3, by positivity, fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl |>.trans (Dvd.intro _ rfl)) hδ
    have d2 := gamma_of_dvd ((Dvd.intro_left _ rfl).trans (Dvd.intro _ rfl)) hδ
    have d3 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only [r]
    rw [h1 δ d1]
    exact (h2 δ d2).trans (h3 δ d3).symm
  obtain ⟨p, hph, hpγ⟩ := GlobalTheory.T.homogeneousPolyCocycle_diff_coboundary_of_eqOn N l w n hN hp hl2 hlN hw r y hr hy hnear
  let pt : MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))) :=
    ∑ m ∈ p.support, MvPolynomial.monomial m (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1)))
  have hpc : ∀ m, pt.coeff m = (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1))) := by
    intro m
    simp only [pt, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff] at h
      rw [h, ZMod.val_zero, Nat.cast_zero]
  have hmap : MvPolynomial.map c pt = p := by
    ext m
    rw [MvPolynomial.coeff_map, hpc, map_natCast, ZMod.natCast_zmod_val]
  have hpth : pt.IsHomogeneous w := by
    intro m hm
    apply hph
    intro h0
    apply hm
    rw [hpc, h0, ZMod.val_zero, Nat.cast_zero]
  refine ⟨fun δ => z' δ - (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) pt - pt), ⟨fun γ hγ => ?_, fun γ hγ δ hδ => ?_⟩, ?_, ?_⟩
  · exact (hz'.1 γ hγ).sub ((L'.2.2.1 _ w pt hpth).sub hpth)
  · simp only
    rw [hz'.2 γ hγ δ hδ, Matrix.SpecialLinearGroup.coe_mul, L'.1, map_sub, map_sub]
    abel
  · obtain ⟨M1, hM1, h1⟩ := hz'n
    refine ⟨M1 * l ^ (n + 1), Nat.mul_pos hM1 (pow_pos hp.pos _), fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only
    rw [L'.2.2.2.2.2.1 _ 1 pt (entries_of_gamma d2), L'.2.1, sub_self, sub_zero, h1 δ d1]
  · intro γ hγ
    simp only
    rw [map_sub, map_sub, L'.2.2.2.2.1 _ c, hmap, ← hpγ γ hγ]
    simp only [r]
    abel

end GlobalTheory.KZ.H3.CocLift

namespace GlobalTheory.KZ.H3


open Classical in
theorem cocycle_lift_of_fam : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ →
    ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) ℤ_[l], IsCoc w (Gam N l) z ∧
      ∀ n, Near (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (z δ)) (Φ n) := by
  intro N l w _ hN hl2 hlN hw Φ hΦ
  have hp : l.Prime := Fact.out
  have lev := GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ
  choose F hF1 hF2 hF3 using CocLift.step N l w hN hl2 hlN hw Φ hΦ
  let seq : (n : ℕ) → {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) // IsCoc w (Gam N l) y ∧ Near y (Φ n)} :=
    fun n => Nat.rec (motive := fun n => {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) //
        IsCoc w (Gam N l) y ∧ Near y (Φ n)})
      ⟨(lev 0).choose, (lev 0).choose_spec⟩
      (fun n y => ⟨F n y.1 y.2.1 y.2.2, hF1 n y.1 y.2.1 y.2.2, hF2 n y.1 y.2.1 y.2.2⟩) n
  have hseq : ∀ n, ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      ((seq (n + 1)).1 γ) = (seq n).1 γ :=
    fun n => hF3 n (seq n).1 (seq n).2.1 (seq n).2.2
  let fam : SL(2, ℤ) → (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) :=
    fun δ n => if δ ∈ Gam N l then (seq n).1 δ else 0
  have hfam : ∀ δ ∈ Gam N l, ∀ n, fam δ n = (seq n).1 δ := fun δ hδ n => if_pos hδ
  have hhom : ∀ δ n, (fam δ n).IsHomogeneous w := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ]; exact (seq n).2.1.1 δ hδ
    · simp only [fam, if_neg hδ]; exact MvPolynomial.isHomogeneous_zero _ _ _
  have hcomp : ∀ δ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      (fam δ (n + 1)) = fam δ n := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ, hfam δ hδ]; exact hseq n δ hδ
    · simp only [fam, if_neg hδ, map_zero]
  choose q hq using fun δ => homogeneous_lift_compatible l w (fam δ) (hhom δ) (hcomp δ)
  have L := GlobalTheory.KZ.polySlash_laws ℤ_[l]
  refine ⟨q, ⟨fun γ _ => (hq γ).1, fun γ hγ δ hδ => ?_⟩, fun n => ?_⟩
  · refine ((hq (γ * δ)).2.2 _ fun n => ?_).symm
    have hγδ : γ * δ ∈ Gam N l := (Gam N l).mul_mem hγ hδ
    rw [map_add (f := _), L.2.2.2.2.1 _ _, (hq γ).2.1 n, (hq δ).2.1 n, hfam γ hγ, hfam δ hδ, hfam _ hγδ,
      (seq n).2.1.2 γ hγ δ hδ]
  · obtain ⟨M, hM, hMδ⟩ := (seq n).2.2
    refine ⟨M * (N * l), Nat.mul_pos hM (Nat.mul_pos hN hp.pos), fun δ hδ => ?_⟩
    have d1 := CocLift.gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := CocLift.gamma_le_gam (N := N) (l := l) ((Dvd.intro _ rfl).trans (Dvd.intro_left _ rfl))
      ((Dvd.intro_left _ rfl).trans (Dvd.intro_left _ rfl)) hδ
    simp only
    rw [(hq δ).2.1 n, hfam δ d2]
    exact hMδ δ d1

end GlobalTheory.KZ.H3
end

section

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.QDer

variable (p : ℕ) [Fact p.Prime]

abbrev qL : Lau p := HahnSeries.single (1 : ℤ) (1 : ℤ_[p])

def thetaFun (f : Lau p) : Lau p := qL p * Formalism.L2.Th1.A.dL f

theorem thetaFun_qL : thetaFun p (qL p) = qL p := by
  have h := Formalism.L2.Th1.A.dL_uPow (R := ℤ_[p]) 1
  simp only [Formalism.L2.Th1.A.uPow] at h
  simp [thetaFun, h, HahnSeries.single_zero_one]

theorem dL_algebraMap (r : ℤ_[p]) : Formalism.L2.Th1.A.dL (algebraMap ℤ_[p] (Lau p) r) = 0 :=
  (Formalism.L2.Th1.A.dLDR ℤ_[p]).map_algebraMap r

def thetaO :=
  letI : Module ℤ_[p] (Lau p) := Algebra.toModule
  GlobalTheory.BK.complDer (k := ℤ_[p]) (pI p)
    { toFun := thetaFun p
      map_add' := fun a b => by simp only [thetaFun, map_add (f := _), mul_add]
      map_smul' := fun r f => by
        simp only [thetaFun, Algebra.smul_def, RingHom.id_apply]
        rw [Formalism.L2.Th1.A.dL_mul, dL_algebraMap p r]
        ring
      map_one_eq_zero' := by
        show thetaFun p 1 = 0
        simp [thetaFun, Formalism.L2.Th1.A.dL_one]
      leibniz' := fun a b => by
        show thetaFun p (a * b) = a • thetaFun p b + b • thetaFun p a
        simp only [thetaFun, smul_eq_mul, Formalism.L2.Th1.A.dL_mul]
        ring }

theorem thetaO_qO : thetaO p (qO p) = qO p := by
  rw [thetaO, qO, GlobalTheory.BK.complDer_algebraMap]
  exact congrArg _ (thetaFun_qL p)

theorem thetaO_algebraMap (r : ℤ_[p]) : thetaO p (algebraMap ℤ_[p] (O0 p) r) = 0 :=
  (thetaO p).map_algebraMap r

def thetaZ : Derivation ℤ (O0 p) (O0 p) where
  toFun := thetaO p
  map_add' := map_add _
  map_smul' := fun r x => by
    simp [Algebra.smul_def, Derivation.leibniz]
  map_one_eq_zero' := (thetaO p).map_one_eq_zero
  leibniz' := (thetaO p).leibniz

theorem exists_qDer : ∀ (p : ℕ) [Fact p.Prime], ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := fun p _ =>
  ⟨thetaZ p, thetaO_qO p, thetaO_algebraMap p⟩

end GlobalTheory.K5.QDer
end
end
