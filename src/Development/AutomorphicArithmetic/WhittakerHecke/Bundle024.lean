module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle019
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.IdeleNormEmbeddingNegOneReal
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle002
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re (x : A ℚ) : |re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

private theorem re_mul (x y : A ℚ) : re (x * y) = re x * re y := by
  simp [re]

private theorem re_add (x y : A ℚ) : re (x + y) = re x + re y := by
  simp [re]

private theorem re_congr {x y : A ℚ} (h : x.1 = y.1) : re x = re y := by
  unfold re
  have : TR.pInf ℚ x = TR.pInf ℚ y := by
    change (TR.infEq ℚ).symm x.1 = (TR.infEq ℚ).symm y.1
    rw [h]
  rw [this]

private theorem re_one : re (1 : A ℚ) = 1 := by
  simp [re]

private theorem row_sq {k : G1 ℚ} (hk : InfOrth k) :
    re (k 1 0) ^ 2 + re (k 1 1) ^ 2 = 1 := by
  have h := re_congr (hk 1 1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  rw [re_add, re_mul, re_mul, re_one] at h
  nlinarith [h]

private theorem abs_re_le_infPart (x : Fin 2 → A ℚ) (j : Fin 2) : |re (x j)| ≤ ‖infPartPi x‖ := by
  rw [abs_re]
  exact (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ _).trans
    (norm_le_pi_norm (infPartPi x) j)

private theorem abs_re_le {k : G1 ℚ} (hk : InfOrth k) (z : A ℚ) :
    |re z| ≤ 2 * ‖infPartPi fun j => z * row k j‖ := by
  set N := ‖infPartPi fun j => z * row k j‖ with hN
  have h0 : |re z| * |re (k 1 0)| ≤ N := by
    have h : |re (z * k 1 0)| ≤ N := abs_re_le_infPart (fun j => z * row k j) 0
    rwa [re_mul, abs_mul] at h
  have h1 : |re z| * |re (k 1 1)| ≤ N := by
    have h : |re (z * k 1 1)| ≤ N := abs_re_le_infPart (fun j => z * row k j) 1
    rwa [re_mul, abs_mul] at h
  have hs := row_sq hk
  have hz := abs_nonneg (re z)
  have ha := abs_nonneg (re (k 1 0))
  have hb := abs_nonneg (re (k 1 1))
  have hs' : |re (k 1 0)| ^ 2 + |re (k 1 1)| ^ 2 = 1 := by simpa [sq_abs] using hs
  by_contra hc
  push_neg at hc
  have hlt : |re (k 1 0)| + |re (k 1 1)| ≥ 1 := by nlinarith
  nlinarith

private theorem fin_eq {k : G1 ℚ} (z : A ℚ) :
    z.2 = (z * row k 0).2 * (-(k 0 1).2) + (z * row k 1).2 * (k 0 0).2 := by
  have hd := congrArg Prod.snd k.det_coe
  rw [Matrix.det_fin_two] at hd
  have hd' : (k 0 0).2 * (k 1 1).2 - (k 0 1).2 * (k 1 0).2 = 1 := hd
  change z.2 = (z.2 * (k 1 0).2) * (-(k 0 1).2) + (z.2 * (k 1 1).2) * (k 0 0).2
  linear_combination (-z.2) * hd'

theorem UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded :
    ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ e : ℝ, 1 < e → ∃ C : ℝ≥0, ∀ k ∈ KK ℚ,
        ∫⁻ z : IdeleGroup ℚ, ‖Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j‖ₑ * ENNReal.ofReal (ab z ^ e) ∂(ideleMeasure ℚ) ≤ C := by
  intro Φ hΦ e he
  obtain ⟨M, hM⟩ := exists_nat_gt e
  obtain ⟨C₀, hC₀, L, hL, hmaj⟩ := GroundTheory.Automorphic.GJGlobal.exists_majorant_pi hΦ M
  set O : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) := ↑(integralFiniteAdeles (𝓞 ℚ) ℚ) with hO
  have hOc : IsCompact O := isCompact_integralFiniteAdeles ℚ
  set K' : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ =>
      p.1 0 * p.2.1 + p.1 1 * p.2.2) '' (L ×ˢ (O ×ˢ O)) with hK'
  have hK'c : IsCompact K' := (hL.prod (hOc.prod hOc)).image (by fun_prop)
  have hI := UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top K' hK'c e he M hM
  set I : ℝ≥0∞ := ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K' then
    ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ M)⁻¹ * ab y ^ e) else 0) ∂(ideleMeasure ℚ) with hIdef
  refine ⟨(ENNReal.ofReal (C₀ * 2 ^ M) * I).toNNReal, fun k hk => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne), hIdef,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  have hab : 0 ≤ ab z ^ e := by
    have : 0 < ab z := (IdeleGroup.ideleModule ℚ z).2
    positivity
  set x : Fin 2 → A ℚ := fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j with hx
  have hm := hmaj x
  by_cases hxL : finPartPi x ∈ L
  · rw [Set.indicator_of_mem hxL, mul_one] at hm
    have hmem : ((z : (A ℚ)ˣ) : A ℚ).2 ∈ K' := by
      refine ⟨(finPartPi x, -(k 0 1).2, (k 0 0).2), ⟨hxL, ?_, ?_⟩, (fin_eq _).symm⟩
      · exact Subring.neg_mem _ (mem_integralFiniteAdeles.2 fun v => hk.2 v 0 1)
      · exact mem_integralFiniteAdeles.2 fun v => hk.2 v 0 0
    rw [if_pos hmem, ← ENNReal.ofReal_mul (by positivity)]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle := abs_re_le hk.1 ((z : (A ℚ)ˣ) : A ℚ)
    set N := ‖infPartPi x‖ with hN
    have hN0 : 0 ≤ N := norm_nonneg _
    have hpow : (1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M ≤ 2 ^ M * (1 + N) ^ M := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) M
    have hinv : ((1 + N) ^ M)⁻¹ ≤ 2 ^ M * ((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹ := by
      rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv, inv_mul_le_iff₀ (by positivity)]
      exact hpow
    calc ‖Φ x‖ * ab z ^ e ≤ (C₀ * ((1 + N) ^ M)⁻¹) * ab z ^ e :=
          mul_le_mul_of_nonneg_right hm hab
      _ ≤ (C₀ * (2 ^ M * ((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹)) * ab z ^ e :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hC₀) hab
      _ = C₀ * 2 ^ M * (((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹ * ab z ^ e) := by ring
  · rw [Set.indicator_of_notMem hxL, mul_zero] at hm
    have h0 : Φ x = 0 := norm_le_zero_iff.1 hm
    simp [h0]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.whittaker_unipotent_translate_of_infinite_component_zero :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ), Continuous φ → (∀ γ g, φ (ratGL E 2 γ * g) = φ g) → ∀ x : A ℚ, x.1 = 0 → ∀ (y : (A ℚ)ˣ) (X : GL (Fin 2) (Cinf E)), Wo D (fun g => φ (g * nu D x)) (em E (aE y) * infGL E 2 X) = ψ (-((y : A ℚ) * x)) * Wo D φ (em E (aE y) * infGL E 2 X) := by
  intro E _ _ _ D φ _ hL x hx y X
  have hfst : (AdeleBaseChange.adeleMap ℚ E x).1 = 0 := by
    obtain ⟨c1, c2⟩ := x
    obtain rfl : c1 = 0 := hx
    exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))
  have h0 : pInf E (D.mkE 0 x) = 0 := by
    have h1 : (D.mkE 0 x).1 = 0 := by
      have e : D.mkE 0 x = AdeleBaseChange.adeleMap ℚ E x * rt D.θ := by
        simp only [Dat.mkE, map_zero, zero_add]
      rw [e]
      change (AdeleBaseChange.adeleMap ℚ E x).1 * _ = 0
      rw [hfst, zero_mul]
    change (infEq E).symm (D.mkE 0 x).1 = 0
    rw [h1]
    exact map_zero _
  have hk : GeneralLinearGroup.map (pInf E) (Xg.nu D x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change pInf E ((!![1, D.mkE 0 x; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    fin_cases i <;> fin_cases j <;> simp [h0]
  have hc : infGL E 2 X * Xg.nu D x = Xg.nu D x * infGL E 2 X := by
    have e := infGL_mul_finGL (Xg.nu D x)
    rw [hk, map_one, one_mul] at e
    rw [← e]
    exact infGL_comm X _
  rw [Nz.Wo_right, mul_assoc, hc, ← mul_assoc, Xg.nu, Nz.em_conj, mul_assoc, Nz.Wo_shift D hL]
  rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma eq_one_of_mul'' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private noncomputable def ef (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (A ℚ)ˣ := (IdeleGroup.prodEquiv ℚ).symm (1, x)

private lemma ef_fst (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ((ef x : (A ℚ)ˣ) : A ℚ).1 = 1 := rfl

private lemma inv_mul_at (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : H.P ℚ) :
    Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) *
      Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
  rw [← map_mul]
  have h := congrArg (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v) (Units.inv_mul x)
  have h' : ((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
      (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
  rw [h', map_one]

private lemma natCast_ne (L : ℕ) (hL : 0 < L) (v : H.P ℚ) : (L : H.Kv v) ≠ 0 := by
  exact_mod_cast hL.ne'

private lemma v_natCast_of_not_bad (L : ℕ) (v : H.P ℚ) (h : ¬ Bad L v) : Valued.v (L : H.Kv v) = 1 := by
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (L : 𝓞 ℚ)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h] at h2
  exact_mod_cast h2

private lemma finite_bad (L : ℕ) (hL : 0 < L) : {v : H.P ℚ | Bad L v}.Finite := by
  have hne : Ideal.span {(L : 𝓞 ℚ)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hL.ne'
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

private lemma nhds_cong (L : ℕ) (hL : 0 < L) (v : H.P ℚ) :
    {x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ | Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ Valued.v (L : H.Kv v)} ∈
      𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
  have hB : IsOpen {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} := by
    have : {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} =
        {y | Valued.v.restrict y ≤ Valued.v.restrict (L : H.Kv v)} := by
      ext y
      simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff]
    rw [this]
    exact Valued.isOpen_closedBall _ (by simp [natCast_ne L hL v])
  have he : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v := RestrictedProduct.continuous_eval v
  have hf : Continuous fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 :=
    (he.comp Units.continuous_val).sub continuous_const
  refine (hB.preimage hf).mem_nhds ?_
  have h0 : ((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 = 0 := sub_self _
  change Valued.v (((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ _
  rw [h0, map_zero]
  exact zero_le'

theorem UpperTheory.finiteIdele_congruenceVolume_pos :
    ∀ L : ℕ, 0 < L → 0 < cT L := by
  intro L hL
  set S : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (fun u => (IdeleGroup.prodEquiv ℚ).symm (1, u)) ⁻¹' TT L with hS
  have hcT : cT L = (finiteIdeleMeasure ℚ S).toReal := rfl
  have hsub : S ⊆ (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    intro x hx
    have hu : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := fun v => hx.1.2 v
    refine (mem_finiteIntegralUnits ℚ).2 fun v => ?_
    have hi := inv_mul_at x v
    rw [hu v, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hu v).le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  have hnhds : S ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    have h1 : (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
      (isOpen_finiteIntegralUnits ℚ).mem_nhds (one_mem _)
    have h2 := (Filter.biInter_mem (finite_bad L hL)).2 fun v (_ : Bad L v) => nhds_cong L hL v
    filter_upwards [h1, h2] with x hx hc
    obtain hxi := (mem_finiteIntegralUnits ℚ).1 hx
    have hle : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 := fun v =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).1
    have hle' : ∀ v : H.P ℚ, Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).2
    refine ⟨⟨ef_fst x, fun v => ?_⟩, fun v => ?_⟩
    · exact eq_one_of_mul'' (hle v) (hle' v) (by rw [mul_comm]; exact inv_mul_at x v)
    · have hcp : H.cp v ((ef x : (A ℚ)ˣ) : A ℚ) - 1 = (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 := rfl
      change Valued.v (H.cp v (((ef x : (A ℚ)ˣ) : A ℚ) - 1)) ≤ _
      rw [map_sub, map_one, hcp]
      by_cases hb : Bad L v
      · exact Set.mem_iInter₂.1 hc v hb
      · rw [v_natCast_of_not_bad L v hb]
        refine (Valuation.map_sub _ _ _).trans (max_le (hle v) ?_)
        rw [map_one]
  rw [hcT]
  refine ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds _ hnhds).ne' ?_
  refine ((measure_mono hsub).trans_lt ?_).ne
  rw [finiteIdeleMeasure_finiteIntegralUnits]
  exact ENNReal.one_lt_top
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem ex_idele (u : ∀ v : H.P ℚ, (H.Kv v)ˣ) (S : Finset (H.P ℚ)) :
    ∃ ζ : (A ℚ)ˣ, (ζ : A ℚ).1 = 1 ∧ ∀ v, H.cp v (ζ : A ℚ) = if v ∈ S then (u v : H.Kv v) else 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, rfl, fun v => by simp⟩
  | insert w S hw ih =>
    obtain ⟨ζ, h1, h2⟩ := ih
    obtain ⟨g1, g2⟩ := localIdele_isSupportedAt ℚ w (u w)
    refine ⟨H.idl w (u w) * ζ, ?_, fun v => ?_⟩
    · show ((localIdele ℚ w (u w) : (A ℚ)ˣ) : A ℚ).1 * (ζ : A ℚ).1 = 1
      rw [h1, mul_one]
      funext x
      exact g1 x
    · rw [Units.val_mul, map_mul, h2 v]
      by_cases hv : v = w
      · subst hv
        have e : H.cp v ((H.idl v (u v) : (A ℚ)ˣ) : A ℚ) = u v := localIdele_snd_self ℚ v (u v)
        rw [e, if_neg hw, if_pos (Finset.mem_insert_self _ _), mul_one]
      · have e : H.cp v ((H.idl w (u w) : (A ℚ)ˣ) : A ℚ) = 1 := g2 v hv
        rw [e, one_mul]
        simp [hv]

private theorem val_bad {N : ℕ} {v : H.P ℚ} (h : Bad N v) : Valued.v (N : H.Kv v) < 1 := by
  have e : (N : H.Kv v) = FinitePlace.embedding v (algebraMap (𝓞 ℚ) ℚ (N : 𝓞 ℚ)) := by simp
  rw [e]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 ℚ) ℚ (N : 𝓞 ℚ))
  refine lt_of_eq_of_lt this ?_
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).2 h

private theorem val_unit {N : ℕ} {k : G1 ℚ} (hk : k ∈ KK ℚ) (hs : k ∈ SS N) {v : H.P ℚ} (h : Bad N v) :
    Valued.v (H.cp v (k 1 1)) = 1 := by
  have hi : ∀ i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun i j => hk.2 v i j
  have hd := k.det_coe
  rw [Matrix.det_fin_two] at hd
  have h1 : H.cp v (k 0 0) * H.cp v (k 1 1) = 1 + H.cp v (k 0 1) * H.cp v (k 1 0) := by
    have := congrArg (H.cp v) hd
    rw [map_sub, map_mul, map_mul, map_one] at this
    exact (sub_eq_iff_eq_add.1 this)
  have h2 : Valued.v (H.cp v (k 0 1) * H.cp v (k 1 0)) < 1 := by
    rw [map_mul]
    calc _ ≤ 1 * Valued.v (H.cp v (k 1 0)) := mul_le_mul_left (hi 0 1) _
      _ < 1 := by rw [one_mul]; exact lt_of_le_of_lt (hs v) (val_bad h)
  have h3 : Valued.v (H.cp v (k 0 0)) * Valued.v (H.cp v (k 1 1)) = 1 := by
    rw [← map_mul, h1]
    exact Valuation.map_one_add_of_lt _ h2
  refine le_antisymm (hi 1 1) ?_
  calc 1 = _ := h3.symm
    _ ≤ 1 * Valued.v (H.cp v (k 1 1)) := mul_le_mul_left (hi 0 0) _
    _ = _ := one_mul _

theorem UpperTheory.exists_idele_correcting_lowerRight_entry :
    ∀ N : ℕ, 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∃ ζ : (A ℚ)ˣ, ζ ∈ UU ∧ ∀ v : H.P ℚ, (Bad N v → Dv N v ((ζ : A ℚ) * k 1 1 - 1)) ∧ (¬ Bad N v → H.cp v (ζ : A ℚ) = 1) := by
  intro N hN k hk hs
  have hfin : {v : H.P ℚ | Bad N v}.Finite := by
    have h0 : Ideal.span {(N : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hN.ne'
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hne : ∀ v, Bad N v → H.cp v (k 1 1) ≠ 0 := fun v hv h0 => by
    have := val_unit hk hs hv
    rw [h0, map_zero] at this
    exact zero_ne_one this
  obtain ⟨ζ, h1, h2⟩ := ex_idele (fun v => if h : Bad N v then (Units.mk0 _ (hne v h))⁻¹ else 1) hfin.toFinset
  have hb : ∀ v, Bad N v → H.cp v (ζ : A ℚ) = (H.cp v (k 1 1))⁻¹ := fun v hv => by
    rw [h2 v, if_pos (hfin.mem_toFinset.2 hv), dite_eq_left hv]
    simp
  have hg : ∀ v, ¬ Bad N v → H.cp v (ζ : A ℚ) = 1 := fun v hv => by
    rw [h2 v, if_neg (fun h => hv (hfin.mem_toFinset.1 h))]
  refine ⟨ζ, ⟨h1, fun v => ?_⟩, fun v => ⟨fun hv => ?_, hg v⟩⟩
  · by_cases hv : Bad N v
    · rw [hb v hv, map_inv₀, val_unit hk hs hv, inv_one]
    · rw [hg v hv, map_one]
  · unfold Dv
    rw [map_sub, map_mul, map_one, hb v hv, inv_mul_cancel₀ (hne v hv), sub_self, map_zero]
    exact zero_le
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem cp_iy (v : H.P ℚ) (r : ℝ) : H.cp v ((iy r : (A ℚ)ˣ) : A ℚ) = 1 := by
  unfold iy
  split_ifs
  · simp
  · change pLoc ℚ v ((1 : Af ℚ) - 0 + 0) = 1
    rw [sub_zero, add_zero, map_one]

private theorem cp_pin (v : H.P ℚ) (n : ℕ) (h : ¬ normV v ∣ n) :
    H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) = 1 := by
  unfold pin
  refine finprod_induction (fun x : (A ℚ)ˣ => H.cp v (x : A ℚ) = 1) (by simp) ?_ ?_
  · intro x y hx hy
    rw [Units.val_mul, map_mul, hx, hy, one_mul]
  · intro v'
    by_cases hv : v = v'
    · subst hv
      rw [Nat.factorization_eq_zero_of_not_dvd h]
      simp
    · have : H.cp v ((pv v' : (A ℚ)ˣ) : A ℚ) = 1 := by
        classical
        exact Pi.mulSingle_eq_of_ne hv _
      rw [Units.val_pow_eq_pow_val, map_pow, this, one_pow]

private theorem cp_rot (v : H.P ℚ) (t : ℝ) :
    Matrix.GeneralLinearGroup.map (H.cp v) (rot t) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h := congrArg (fun y : GL (Fin 2) (Af ℚ) => pLoc ℚ v (y.val i j)) (TR.pFin_infGL (E := ℚ) (a := 2) _ :
    Matrix.GeneralLinearGroup.map (pFin ℚ) (rot t) = 1)
  refine h.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

private theorem cp_aE (v : H.P ℚ) (a : (A ℚ)ˣ) (h : H.cp v (a : A ℚ) = 1) :
    Matrix.GeneralLinearGroup.map (H.cp v) (aE a) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change H.cp v ((aE a).val i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE, h]

theorem UpperTheory.kAt_diag_ideleOfNat_mul_rotation_of_not_dvd :
    ∀ (E : Type) [Field E] [NumberField E] (v : H.P ℚ) (n : ℕ) (r t : ℝ), 0 < n → ¬ normV v ∣ n → ∀ w : H.P E, w.under (𝓞 ℚ) = v →
          H.KAt w (em E (aE (iy r * pin n) * rot t)) := by
  intro E _ _ v n r t _ h w hw
  have hx : Matrix.GeneralLinearGroup.map (H.cp v) (aE (iy r * pin n) * rot t) = 1 := by
    rw [map_mul, cp_rot, cp_aE v _ (by rw [Units.val_mul, map_mul, cp_iy, cp_pin v n h, one_mul]), one_mul]
  generalize aE (iy r * pin n) * rot t = x at hx
  subst hw
  have : Matrix.GeneralLinearGroup.map (H.cp w) (em E x) = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have e : H.cp (w.under (𝓞 ℚ)) (x.val i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j :=
      congrArg (fun y : GL (Fin 2) _ => y.val i j) hx
    change GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w (H.cp (w.under (𝓞 ℚ)) (x.val i j)) = (1 : Matrix (Fin 2) (Fin 2) _) i j
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)
    · exact map_zero (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)
  unfold H.KAt
  rw [this]
  exact one_mem _
end
