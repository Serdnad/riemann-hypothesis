module

public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Formalism.HermitianCurvature.StatementLE
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.S3

namespace LocalVolumePositivity

variable {P : Type} [Fintype P] {B : MassData P}

theorem unit_level_volume_pos (hP : B.Pos) : 0 < B.unitLevelVolume := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.unitLevelVolume
  exact mul_pos xU0 (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2)

theorem pos_μK (hP : B.Pos) : 0 < B.μK := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μK
  exact mul_pos xKo (prod_pos fun p _ => (hp p).2.2.2.2.2.1)

theorem pos_μKpp (hP : B.Pos) : 0 < B.μKpp := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μKpp
  exact mul_pos xKo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.1)

theorem pos_MM (hP : B.Pos) : 0 < B.MM := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.MM
  exact mul_pos xMo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem pos_μSpp (hP : B.Pos) : 0 < B.μSpp := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μSpp
  exact mul_pos xSo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.1)

theorem pos_μSpp' (hP : B.Pos) : 0 < B.μSpp' := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μSpp'
  exact mul_pos xSo' (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.1)

theorem gamma_product_pos (hP : B.Pos) : 0 < B.Gam1 := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.Gam1
  exact prod_pos fun p _ => by unfold MassData.ga; exact div_pos (hp p).2.1 (hp p).2.2.1

theorem pos_tt (hP : B.Pos) : 0 < B.tt := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.tt
  exact prod_pos fun p _ => add_pos one_pos (div_pos (by norm_num) (hp p).1)

end LocalVolumePositivity

open LocalVolumePositivity

theorem middle_level_volume_index : KnatGamma := by
  intro P _ B hP hI p
  obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hP.1 p
  obtain ⟨h1, h2⟩ := hI p
  rw [div_eq_iff qKp.ne'] at h2
  rw [h2, h1]
  unfold MassData.ga
  field_simp

theorem column_identity : Columns := by
  intro P _ B hP hV hL hM hC
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨_, hNa1, hNa1'⟩ := hV
  obtain ⟨hLS, hLSpp, hLS', hLSpp'⟩ := hL
  obtain ⟨hρ, hNaN, hρ', hNaN'⟩ := hM
  obtain ⟨hdd, hG1, hdd', hG1'⟩ := hC
  have eN : B.volN = 1 / B.μN := by rw [eq_div_iff xN.ne', ← hNaN, hNa1]
  have eN' : B.volN' = 1 / B.μN' := by rw [eq_div_iff xN'.ne', ← hNaN', hNa1']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρ, eN, hLS]; field_simp
  · rw [hdd, ← hG1, hρ]; field_simp
  · unfold MassData.c0; rw [hdd, hLSpp, eN]; field_simp
  · rw [hρ', eN', hLS']; field_simp
  · rw [hdd', ← hG1', hρ']; field_simp
  · unfold MassData.c0'; rw [hdd', hLSpp', eN']; field_simp

theorem local_ratio_product : LocalProduct := by
  intro P _ B hP hO hT hI
  have hP0 := hP
  have hG1 := gamma_product_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hMo : B.Mo = B.μKo ^ 2 / (B.μSo * B.μSo') * B.localVolumeArchimedean := by
    rw [← hO]; field_simp
  have hM : ∏ p, B.Mp p = (∏ p, B.localVolumeAtPlace p) * (∏ p, B.μKp p) * (∏ p, B.μKnatp p) /
      ((∏ p, B.μSp p) * ∏ p, B.μSp' p) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib, ← prod_div_distrib]
    refine prod_congr rfl fun p _ => ?_
    obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hp p
    have h := (hT p).1
    rw [div_eq_iff qU.ne'] at h
    rw [h]; field_simp
  have hKn : ∏ p, B.μKnatp p = B.Gam1 * ∏ p, B.μKppp p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => middle_level_volume_index P B hP0 hI p
  have hSp : ∏ p, B.μSp p = B.Gam1 * ∏ p, B.μSppp p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => (hT p).2.1
  have hSp' : ∏ p, B.μSp' p = B.Gam1 * ∏ p, B.μSppp' p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => (hT p).2.2
  have a1 : 0 < ∏ p, B.localVolumeAtPlace p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2
  have a2 : 0 < ∏ p, B.μKp p := prod_pos fun p _ => (hp p).2.2.2.2.2.1
  have a3 : 0 < ∏ p, B.μKppp p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.1
  have a4 : 0 < ∏ p, B.μSppp p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.1
  have a5 : 0 < ∏ p, B.μSppp' p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.1
  unfold MassData.MM MassData.unitLevelVolume MassData.μK MassData.μKpp MassData.μSpp MassData.μSpp' MassData.μKnat MassData.μS MassData.μS'
  rw [hM, hMo, hKn, hSp, hSp']
  constructor <;> field_simp <;> ring

theorem jacobian_natural_measure_constant : JacobianConstant := by
  intro P _ B hP hJ hNu
  have hU := unit_level_volume_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  rw [hJ, hNu]
  field_simp

theorem form_signature_bound : SigBound := by
  intro P _ B hP hF hK hMs hD hA hJ hNu hI
  have hP0 := hP
  have hU := unit_level_volume_pos hP
  have hμK := pos_μK hP
  have hMM := pos_MM hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨hKV, hKt⟩ := hK
  have hc0 : 0 < B.c0 := by unfold MassData.c0; exact div_pos (mul_pos xvN xvH) xpi
  have hc0' : 0 < B.c0' := by unfold MassData.c0'; exact div_pos (mul_pos xvN' xvH') xpi'
  have he1 : 0 ≤ B.e1 := xsd.trans hD
  have hAA : 0 < B.AA := by
    unfold MassData.AA; exact div_pos (mul_pos (mul_pos xB xC) (div_pos hMM xZZ)) hμK
  have hJc := jacobian_natural_measure_constant P B hP0 hJ hNu
  have hIntN : B.IntN ≤ B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * (1 / B.deg) := by
    rw [hJc]
    exact mul_le_mul_of_nonneg_left hI (mul_nonneg (div_nonneg xZZ.le hU.le) (inv_nonneg.mpr xC.le))
  have hKt2 : B.KtopV ≤ (1 + B.δ) * B.IntN / (B.c0 * B.c0') := by
    rw [le_div_iff₀ (mul_pos hc0 hc0')]
    calc B.KtopV * (B.c0 * B.c0') = B.Smod := by unfold MassData.Smod; ring
      _ ≤ _ := hA
  have hEA : 0 ≤ B.e1 * B.AA := mul_nonneg he1 hAA.le
  calc B.Sig = B.ρ0 * B.KV := hF
    _ ≤ B.ρ0 * (B.e1 * B.n0c * B.KtopV) := by
        apply mul_le_mul_of_nonneg_left _ xr.le
        calc B.KV ≤ B.supdens * B.n0c * B.KtopV := hKV
          _ ≤ B.e1 * B.n0c * B.KtopV :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD xn0.le) hKt
    _ = B.e1 * B.AA * B.KtopV := by rw [← hMs]; ring
    _ ≤ B.e1 * B.AA * ((1 + B.δ) * B.IntN / (B.c0 * B.c0')) :=
        mul_le_mul_of_nonneg_left hKt2 hEA
    _ ≤ B.e1 * B.AA * ((1 + B.δ) * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * (1 / B.deg)) /
          (B.c0 * B.c0')) := by
        apply mul_le_mul_of_nonneg_left _ hEA
        apply div_le_div_of_nonneg_right _ (mul_pos hc0 hc0').le
        exact mul_le_mul_of_nonneg_left hIntN (by linarith)
    _ = _ := by
        unfold MassData.AA
        have := hc0.ne'; have := hc0'.ne'
        field_simp

theorem mass_formula_constant_one : MainTheorem := by
  intro P _ B hP h2A hF hK hMs hD hA hJ hNu hI hV hL hM hC hO hT hIx
  have hSB := form_signature_bound P B hP hF hK hMs hD hA hJ hNu hI
  obtain ⟨_, cd, cc, _, cd', cc'⟩ := column_identity P B hP hV hL hM hC
  obtain ⟨hLP, _⟩ := local_ratio_product P B hP hO hT hIx
  have htt := pos_tt hP
  have hG1 := gamma_product_pos hP
  have hμK := pos_μK hP
  have hKpp := pos_μKpp hP
  have hSpp := pos_μSpp hP
  have hSpp' := pos_μSpp' hP
  have hU := unit_level_volume_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hGS : B.GS = B.tt * B.Gam1 * B.Sig := by
    unfold MassData.GS; rw [hF, cd]; field_simp
  have key : B.tt * B.Gam1 * ((1 + B.δ) * B.e1 * (B.c0 * B.c0')⁻¹ * B.volB * (B.MM / B.unitLevelVolume) /
      (B.μK * B.deg)) = (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar) := by
    have e1 : B.MM / B.unitLevelVolume = B.μKpp / (B.Gam1 * B.μSpp * B.μSpp') * B.μK := by
      rw [← hLP]; field_simp
    have e2 : (B.c0)⁻¹ = B.d * B.μSpp / B.volHa := by rw [← cc, one_div]
    have e3 : (B.c0')⁻¹ = B.d' * B.μSpp' / B.volHa' := by rw [← cc', one_div]
    have e4 : B.volB = B.volHa * B.volHa' / B.volG := by rw [eq_div_iff xG.ne']; exact hV.1
    unfold MassData.Dstar
    rw [mul_inv, e1, e2, e3, e4]
    field_simp
  refine ⟨hGS, ?_, ?_⟩
  · rw [hGS, ← key]
    exact mul_le_mul_of_nonneg_left hSB (mul_pos htt hG1).le
  · calc B.Kgs2 ≤ B.tt * B.Gam1 * B.Sig := h2A
      _ ≤ _ := by
        rw [← key]
        exact mul_le_mul_of_nonneg_left hSB (mul_pos htt hG1).le

end Formalism.FourierDecayAlt.P
end

section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Blocks

variable {A : Type} {r k : ℕ}

variable [CommRing A]

variable {P : Matrix (Fin k) (Fin k) A → Prop}

theorem uni_unit {n : ℕ} {u : Matrix (Fin n) (Fin n) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [isUpUni_det A hu]; exact isUnit_one

end Blocks

end Formalism.FourierDecayAlt.P.S3x1




namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count

theorem card_lt_pairs (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  have h : ∀ j : Fin n, ∑ i : Fin n, (if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have e : Finset.filter (fun i : Fin n => i < j) Finset.univ = Finset.Iio j := by ext i; simp
    rw [e, Fin.card_Iio]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

variable {A : Type} [CommRing A]

def uniEquiv (n : ℕ) : {u : Matrix (Fin n) (Fin n) A // IsUpUni u} ≃ ({p : Fin n × Fin n // p.1 < p.2} → A) where
  toFun u := fun p => u.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    constructor
    · intro i j hij
      have hij' : j < i := hij
      simp [not_lt.2 hij'.le, hij'.ne']
    · intro a; simp⟩
  left_inv u := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h]
    · subst h; simp [u.2.2 i]
    · have : u.1 i j = 0 := u.2.1 h
      simp [not_lt.2 h.le, h.ne', this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h' : i < j := h
    simp [h']

theorem card_uni (K : Type) [Field K] [Fintype K] (n : ℕ) :
    Nat.card {u : Matrix (Fin n) (Fin n) K // IsUpUni u} = Fintype.card K ^ (n * (n - 1) / 2) := by
  rw [Nat.card_congr (uniEquiv n), Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]

noncomputable def upUniGEquiv (n : ℕ) : upUniG A n ≃ {u : Matrix (Fin n) (Fin n) A // IsUpUni u} where
  toFun g := ⟨g.1.1, g.2⟩
  invFun u := ⟨Matrix.GeneralLinearGroup.mk'' u.1 (uni_unit u.2), u.2⟩
  left_inv g := Subtype.ext (Units.ext rfl)
  right_inv u := rfl

variable {r k : ℕ}

def mk (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A) :
    Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks a (Matrix.fromCols b c) 0 (Matrix.fromBlocks m e 0 f)

section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
end mk

end Count

end Formalism.FourierDecayAlt.P.S3x1

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count2

variable {A : Type} [CommRing A] {r k : ℕ}

theorem prod_gl (q k : ℕ) : ∏ i : Fin k, (q ^ k - q ^ (i : ℕ)) =
    q ^ (k * (k - 1) / 2) * ∏ i ∈ Icc 1 k, (q ^ i - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ k - q ^ i) k, ← Finset.sum_range_id,
    ← Finset.prod_pow_eq_pow_sum]
  have h1 : ∏ i ∈ Icc 1 k, (q ^ i - 1) = ∏ i ∈ range k, (q ^ (k - i) - 1) := by
    refine Finset.prod_nbij' (fun i => k - i) (fun i => k - i) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      have : k - (k - a) = a := by omega
      rw [this]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ k := (Finset.mem_range.1 hi).le
  rw [Nat.mul_sub, ← pow_add, Nat.add_sub_cancel' hi', mul_one]

end Count2

end Formalism.FourierDecayAlt.P.S3x1





open Formalism.FourierDecayAlt.P.S3x1 in
theorem Formalism.FourierDecayAlt.P.gamma_factor_product : Formalism.FourierDecayAlt.S3.GammaProduct := by
  intro K _ _ k
  rw [Matrix.card_GL_field, Nat.card_congr (upUniGEquiv k), card_uni, prod_gl]

end

section

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem smoothLog_sc (c : Cut) (ε : ℝ) (m : ℕ) : SmoothLog (c.sc ε m) := by
  unfold SmoothLog Cut.sc
  exact (c.smooth.comp (Real.contDiff_exp.div_const ε)).pow m






theorem thetaForm : ThetaForm := by
  intro ε σ hε v
  unfold th
  have h1 : Real.exp v / (Real.exp v + ε) = (1 + ε * Real.exp (-v))⁻¹ := by
    rw [Real.exp_neg]; have := Real.exp_pos v; field_simp
  have h2 : 0 ≤ 1 + ε * Real.exp (-v) := by positivity
  rw [h1, Real.inv_rpow h2, Real.rpow_neg h2]

theorem thetaSmooth : ThetaSmooth := by
  intro ε σ hε
  unfold SmoothLog
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (contDiff_const.mul (Real.contDiff_exp.comp contDiff_neg))
  · intro u; positivity

theorem thetaBound : ThetaBound := by
  intro hC σ ε hσ hε p x hx
  unfold ld
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  have h := hC σ ε hσ hε p (Real.log x)
  rwa [← thetaForm ε σ hε (Real.log x), Real.exp_log hx] at h

theorem iterDeriv_const' (p : ℕ) (k t : ℝ) : iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
  cases p with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']

theorem cutBound : CutBound := by
  intro c m p hm
  set h : ℝ → ℝ := fun t => c.χ (Real.exp t) ^ m with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := (c.smooth.comp Real.contDiff_exp).pow m
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log (1/2) → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have : Real.exp s ≤ 1/2 := by
        have := Real.exp_lt_exp.mpr hs
        rw [Real.exp_log (by norm_num)] at this; exact this.le
      simp only [hh, c.zero _ this]
      exact zero_pow (by omega)
    rw [this.iteratedDeriv_eq p, iterDeriv_const']; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, c.one _ this]
    rw [this.iteratedDeriv_eq p, iterDeriv_const']
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log (1/2)) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  have hbd : ∀ t, |iteratedDeriv p h t| ≤ max C0 1 := by
    intro t
    rcases lt_or_ge t (Real.log (1/2)) with h1 | h1
    · rw [hlow t h1]; simp
    · rcases lt_or_ge 0 t with h2 | h2
      · rw [hhigh t h2]; split_ifs <;> simp
      · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)
  have key : ∀ ε x : ℝ, 0 < ε → ld p (c.sc ε m) x = iteratedDeriv p h (Real.log x - Real.log ε) := by
    intro ε x hε
    unfold ld
    have : (fun u : ℝ => c.sc ε m (Real.exp u)) = fun u : ℝ => h (u - Real.log ε) := by
      funext u; simp only [hh, Cut.sc]; rw [Real.exp_sub, Real.exp_log hε]
    rw [this, iteratedDeriv_comp_sub_const]
  refine ⟨max C0 1, fun ε x hε hx => ?_⟩
  rw [key ε x hε]
  refine ⟨hbd _, fun hlt => hlow _ ?_, fun hlt => hhigh _ ?_⟩
  · rw [← Real.log_div hx.ne' hε.ne']
    refine Real.log_lt_log (by positivity) ?_
    rw [div_lt_iff₀ hε]; linarith
  · have := Real.log_lt_log hε hlt; linarith

end Formalism.FourierDecayAlt.P.LEx1
end
