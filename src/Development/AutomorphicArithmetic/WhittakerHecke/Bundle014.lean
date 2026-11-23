module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
import GroundTheory.GlobalFields.TateThesis.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import GroundTheory.GlobalFields.IdeleGroups.Rational
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
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private lemma inv_mem_UU' {t : (A ℚ)ˣ} (ht : t ∈ UU) : t⁻¹ ∈ UU := by
  refine ⟨?_, fun v => ?_⟩
  · have h : (t : A ℚ).1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ).1 = 1 := congrArg Prod.fst (Units.mul_inv t)
    rw [ht.1, one_mul] at h
    exact h
  · have hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have := congrArg Valued.v hm
    rwa [map_mul, ht.2 v, one_mul, map_one] at this

private lemma cD_mem_KK {t : (A ℚ)ˣ} (ht : t ∈ UU) {k : G1 ℚ} (hk : k ∈ KK ℚ) : cD t k ∈ KK ℚ := by
  have hi := inv_mem_UU' ht
  have fm : ∀ a b : A ℚ, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have fa : ∀ a b : A ℚ, (a + b).1 = a.1 + b.1 := fun _ _ => rfl
  have c00 : (cD t k) 0 0 = k 0 0 := rfl
  have c01 : (cD t k) 0 1 = k 0 1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ) := rfl
  have c10 : (cD t k) 1 0 = (t : A ℚ) * k 1 0 := rfl
  have c11 : (cD t k) 1 1 = k 1 1 := rfl
  have e1 : ∀ i j, ((cD t k) i j).1 = (k i j).1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact congrArg Prod.fst c00
    · show ((cD t k) 0 1).1 = (k 0 1).1
      rw [c01, fm, hi.1, mul_one]
    · show ((cD t k) 1 0).1 = (k 1 0).1
      rw [c10, fm, ht.1, one_mul]
    · exact congrArg Prod.fst c11
  refine ⟨fun i j => ?_, fun v i j => ?_⟩
  · have h := hk.1 i j
    rw [← h]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    have e3 : ∀ a b c d a' b' c' d' : A ℚ, a.1 = a'.1 → b.1 = b'.1 → c.1 = c'.1 → d.1 = d'.1 →
        (a * b + c * d).1 = (a' * b' + c' * d').1 := by
      intro a b c d a' b' c' d' h1 h2 h3 h4
      rw [fa, fa, fm, fm, fm, fm, h1, h2, h3, h4]
    exact e3 _ _ _ _ _ _ _ _ (e1 _ _) (e1 _ _) (e1 _ _) (e1 _ _)
  · have ti : ((t : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (ht.2 v).le
    have tj : (((t⁻¹ : (A ℚ)ˣ) : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (hi.2 v).le
    fin_cases i <;> fin_cases j
    · exact hk.2 v 0 0
    · show ((cD t k) 0 1).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c01]
      exact mul_mem (hk.2 v 0 1) tj
    · show ((cD t k) 1 0).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c10]
      exact mul_mem ti (hk.2 v 1 0)
    · exact hk.2 v 1 1

theorem UpperTheory.maximalCompact_measure_map_conjDiag_eq :
    ∀ (M₀ : Meas ℚ) (t : IdeleGroup ℚ), t ∈ UU → M₀.κ.map (cD t) = M₀.κ := by
  intro m t ht
  haveI := m.prob
  have hm : Measurable (cD t : G1 ℚ → G1 ℚ) := (M.continuous_cD t).measurable
  have hae : ∀ᵐ y ∂m.κ, y ∈ KK ℚ := by
    rw [ae_iff]
    exact m.supp
  have right : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (x * k) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_right k hk]
    rw [lintegral_map hf (measurable_mul_const k)]
  have left : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (k * x) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_left k hk]
    rw [lintegral_map hf (measurable_const_mul k)]
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf hm]
  have hF : Measurable (fun p : G1 ℚ × G1 ℚ => f (p.1 * cD t p.2)) :=
    hf.comp (measurable_fst.mul (hm.comp measurable_snd))
  have hA : ∫⁻ y, ∫⁻ x, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    have h : ∀ᵐ y ∂m.κ, ∫⁻ x, f (x * cD t y) ∂m.κ = ∫⁻ x, f x ∂m.κ :=
      hae.mono fun y hy => right f hf _ (cD_mem_KK ht hy)
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  have hB : ∫⁻ x, ∫⁻ y, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
    have h : ∀ᵐ x ∂m.κ, ∫⁻ y, f (x * cD t y) ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
      refine hae.mono fun x hx => ?_
      have hk : cD t⁻¹ x ∈ KK ℚ := cD_mem_KK (inv_mem_UU' ht) hx
      have ex : x = cD t (cD t⁻¹ x) := by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      have e : ∀ y, f (x * cD t y) = (f ∘ cD t) (cD t⁻¹ x * y) := by
        intro y
        rw [Function.comp_apply, M.cD_mul, ← ex]
      simp only [e]
      exact left (f ∘ cD t) (hf.comp hm) _ hk
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  rw [← hB, ← hA]
  exact lintegral_lintegral_swap hF.aemeasurable
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private lemma eq_one_of_mul' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma mem_UU_iff' (t : IdeleGroup ℚ) :
    t ∈ UU ↔ IdeleGroup.toInfinite ℚ t = 1 ∧ IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ := by
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Units.ext h1, (mem_finiteIntegralUnits ℚ).2 fun v => ?_⟩
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rintro ⟨h1, h2⟩
    refine ⟨congrArg Units.val h1, fun v => ?_⟩
    obtain ⟨ha, hb⟩ := (mem_finiteIntegralUnits ℚ).1 h2 v
    exact eq_one_of_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) (by rw [mul_comm]; exact hinv v)

private lemma ofFinite_toFinite' {t : IdeleGroup ℚ} (h : IdeleGroup.toInfinite ℚ t = 1) :
    IdeleGroup.ofFinite (IdeleGroup.toFinite ℚ t) = t := by
  refine (IdeleGroup.prodEquiv ℚ).injective (Prod.ext ?_ ?_)
  · change IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite _) = IdeleGroup.toInfinite ℚ t
    rw [IdeleGroup.toInfinite_ofFinite, h]
  · change IdeleGroup.toFinite ℚ (IdeleGroup.ofFinite _) = IdeleGroup.toFinite ℚ t
    rw [IdeleGroup.toFinite_ofFinite]

private lemma ab_ofFinite' {z : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hz : z ∈ finiteIntegralUnits ℚ) : ab (IdeleGroup.ofFinite z : IdeleGroup ℚ) = 1 := by
  have hmem : (IdeleGroup.ofFinite z : IdeleGroup ℚ) ∈ IdeleGroup.standardOpenSubgroup ℚ := hz
  have hinf : IdeleGroup.infiniteModule (IdeleGroup.ofFinite z : IdeleGroup ℚ) = 1 := by
    have e : ((IdeleGroup.ofFinite z : IdeleGroup ℚ) : NumberField.AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
      change ((IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite z) : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = 1
      rw [IdeleGroup.toInfinite_ofFinite, Units.val_one]
    simp only [IdeleGroup.infiniteModule, e]
    exact Finset.prod_eq_one fun w _ => by
      rw [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]
  unfold ab
  rw [IdeleGroup.ideleModule_apply, hinf, IdeleGroup.finiteModule_eq_one_of_mem hmem, one_mul]

theorem UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one :
    IsCompact UU ∧ ∀ u ∈ UU, ab u = 1 := by
  have hset : (UU : Set (IdeleGroup ℚ)) =
      (fun z => (IdeleGroup.ofFinite z : IdeleGroup ℚ)) '' (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    ext t
    constructor
    · intro ht
      obtain ⟨h1, h2⟩ := (mem_UU_iff' t).1 ht
      exact ⟨_, h2, ofFinite_toFinite' h1⟩
    · rintro ⟨z, hz, rfl⟩
      refine (mem_UU_iff' _).2 ⟨IdeleGroup.toInfinite_ofFinite _, ?_⟩
      change IdeleGroup.toFinite ℚ (IdeleGroup.ofFinite z) ∈ _
      rwa [IdeleGroup.toFinite_ofFinite]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [hset]
    exact (isCompact_finiteIntegralUnits ℚ).image IdeleGroup.continuous_ofFinite
  · obtain ⟨h1, h2⟩ := (mem_UU_iff' u).1 hu
    rw [← ofFinite_toFinite' h1]
    exact ab_ofFinite' h2
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem cinf_sq {E : Type} [Field E] (y : (Cinf E)ˣ) : ∃ r : (Cinf E)ˣ, r ^ 2 = y := by
  have hy : ∀ w, y.val w ≠ 0 := fun w h => by
    have := congrFun y.mul_inv w
    simp [h] at this
  choose z hz using fun w => IsAlgClosed.exists_pow_nat_eq (y.val w) (n := 2) (by norm_num)
  have hz0 : ∀ w, z w ≠ 0 := fun w h => hy w (by rw [← hz w, h]; simp)
  refine ⟨⟨z, fun w => (z w)⁻¹, funext fun w => mul_inv_cancel₀ (hz0 w), funext fun w => inv_mul_cancel₀ (hz0 w)⟩, Units.ext (funext fun w => ?_)⟩
  exact hz w

private theorem pInf_infId {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r : (Cinf E)ˣ) :
    Units.map (pInf E).toMonoidHom (infId E r) = r := by
  have h : ∀ x, pInf E (GlobalTheory.CuspRep.sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  refine Units.ext ?_
  change pInf E (1 - GlobalTheory.CuspRep.sInf E 1 + GlobalTheory.CuspRep.sInf E r.val) = r.val
  simp [h]

private theorem dM_fin {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : (A E)ˣ)
    (ht : pInf E (t : A E) = 1) : ∃ k, dM t = finGL E 2 k := by
  refine ⟨GeneralLinearGroup.map (pFin E) (dM t), ?_⟩
  have h : GeneralLinearGroup.map (pInf E) (dM t) = 1 := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht]
  conv_lhs => rw [← infGL_mul_finGL (dM t), h, map_one, one_mul]

theorem UpperTheory.cuspSubspace_translate_eq_smul_special_translate :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ), CenN P ω → ∀ f ∈ P.V, ∀ x : GL (Fin 2) (A E), ∃ (c : ℂ) (f' : Sm E 2) (h : G1 E), f' ∈ P.V ∧ ∀ g, f.1 (g * x) = c * f'.1 (g * gl h) := by
  intro E _ _ _ P ω hω f hf x
  obtain ⟨g0, hg0⟩ := exists_gl_mul_dM x
  obtain ⟨r, hr⟩ := cinf_sq (Units.map (pInf E).toMonoidHom (GeneralLinearGroup.det x))
  obtain ⟨s, hs⟩ : ∃ s : (A E)ˣ, Units.map (pInf E).toMonoidHom s = r := ⟨infId E r, pInf_infId r⟩
  obtain ⟨t, ht⟩ : ∃ t : (A E)ˣ, GeneralLinearGroup.det x = s ^ 2 * t := ⟨(s ^ 2)⁻¹ * GeneralLinearGroup.det x, by group⟩
  have ht1 : pInf E (t : A E) = 1 := by
    have h1 : Units.map (pInf E).toMonoidHom t = 1 := by
      have h2 := congrArg (Units.map (pInf E).toMonoidHom) ht
      rw [map_mul, map_pow, hs, hr] at h2
      exact (mul_eq_left.1 h2.symm)
    exact congrArg Units.val h1
  obtain ⟨k, hk⟩ := dM_fin t ht1
  refine ⟨((ω.1 (ideleNorm ℚ E s) : ℂˣ) : ℂ), act (.fin k) f, g0 * (mD s)⁻¹, P.stable (.fin k) f hf, fun g => ?_⟩
  have hx : x = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (gl (g0 * (mD s)⁻¹) * dM t) := by
    have e : dM (s ^ 2) = (gl (mD s))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
      rw [← gl_mD_mul_dM_sq, inv_mul_cancel_left]
    rw [gl_mul, gl_inv]
    conv_lhs => rw [hg0, ht, dM_mul, e]
    rw [_root_.UpperTheory.ConvolutionTheory.R2.scalar_comm s (gl g0 * (gl (mD s))⁻¹ * dM t), mul_assoc (gl (mD s))⁻¹, _root_.UpperTheory.ConvolutionTheory.R2.scalar_comm s (dM t)]
    simp only [mul_assoc]
  have hg : g * x = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (g * gl (g0 * (mD s)⁻¹) * finGL E 2 k) := by
    rw [hx, hk, ← mul_assoc g, ← _root_.UpperTheory.ConvolutionTheory.R2.scalar_comm s g, mul_assoc, mul_assoc]
  rw [hg, hω f hf]
  rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private lemma eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma ab_pos_eq {p : IdeleGroup ℚ} (hp : p ∈ RationalIdeles.positiveSubgroup) :
    ab p = (RationalIdeles.realPart p : ℝ) := by
  obtain ⟨h1, h2⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  have hw := RationalIdeles.isReal_infinitePlace (default : InfinitePlace ℚ)
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    simp [InfinitePlace.mult, hw]
  have hn : ‖(p : AdeleRing (𝓞 ℚ) ℚ).1 default‖ = (RationalIdeles.realPart p : ℝ) := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _), ← RationalIdeles.realEquiv_apply, ← RationalIdeles.coe_realPart, Real.norm_eq_abs, abs_of_pos h2]
  unfold ab
  rw [IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one, IdeleGroup.infiniteModule,
    Fintype.prod_subsingleton _ (default : InfinitePlace ℚ), hmult, pow_one, hn]

theorem UpperTheory.rat_idele_eq_diagonal_mul_unit_of_abs_eq_one :
    ∀ a : IdeleGroup ℚ, ab a = 1 → ∃ (r : ℚˣ), ∃ u ∈ UU, a = IdeleGroup.diagonal ℚ r * u := by
  intro a ha
  obtain ⟨⟨r, p⟩, hp⟩ := RationalIdeles.mulMap_bijective.2 a
  rw [RationalIdeles.mulMap_apply] at hp
  have hp' : a = IdeleGroup.diagonal ℚ r * (p : IdeleGroup ℚ) := hp.symm
  have hab : ab (p : IdeleGroup ℚ) = 1 := by
    rw [hp', ab_mul, ab_diagonal, one_mul] at ha
    exact ha
  obtain ⟨h1, -⟩ := RationalIdeles.mem_positiveSubgroup.1 p.2
  have hre : RationalIdeles.realEquiv ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
    rw [← RationalIdeles.coe_realPart, ← ab_pos_eq p.2, hab]
  have hone : ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 :=
    RationalIdeles.realEquiv.injective (hre.trans (map_one _).symm)
  refine ⟨r, p, ⟨hone, fun v => ?_⟩, hp'⟩
  obtain ⟨ha', hb'⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v
  have hm := IdeleGroup.finite_mul_inv (p : IdeleGroup ℚ) v
  have hmv := congrArg Valued.v hm
  rw [map_mul, map_one] at hmv
  exact eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha')
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb') hmv
end
