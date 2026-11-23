module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private noncomputable def cu (y : ℝ) (h : y ≠ 0) : (TR.Rinf ℚ)ˣ :=
  ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩

private theorem iy_eq {y : ℝ} (h : y ≠ 0) : iy y = TR.infId ℚ (cu y h) := dif_neg h

private theorem nrm_unit {v : H.P ℚ} {x : H.Kv v} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one :
    (∀ y y' : ℝ, y ≠ 0 → y' ≠ 0 → iy (y * y') = iy y * iy y') ∧ (∀ y : ℝ, y ≠ 0 → ab (iy y) = |y|) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) ∧ ∀ u ∈ UU, ab u = 1 := by
  refine ⟨fun y y' hy hy' => ?_, fun y hy => ?_, ?_, fun u hu => ?_⟩
  · rw [iy_eq (mul_ne_zero hy hy'), iy_eq hy, iy_eq hy', ← map_mul]
    congr 1
    exact Units.ext rfl
  · rw [iy_eq hy]
    show (IdeleGroup.ideleModule ℚ (TR.infId ℚ (cu y hy)) : ℝ) = |y|
    rw [GlobalTheory.HenQ.DetSplit.ideleModule_infId]
    simp [cu]
  · have hu : Continuous fun t : ℝ => cu (Real.exp t) (Real.exp_ne_zero t) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => Real.continuous_exp.inv₀ Real.exp_ne_zero
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (cu (Real.exp t) (Real.exp_ne_zero t)) :=
      funext fun t => iy_eq (Real.exp_ne_zero t)
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
  · show (IdeleGroup.ideleModule ℚ u : ℝ) = 1
    rw [IdeleGroup.ideleModule_eq]
    have h1 : ((u : A ℚ)).1 = 1 := hu.1
    have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖((u : A ℚ)).2 v‖ = 1 :=
      finprod_eq_one_of_forall_eq_one fun v => nrm_unit (hu.2 v)
    rw [h1, h2, mul_one]
    exact Finset.prod_eq_one fun w _ => by
      rw [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.exists_bound_cuspForm_of_unitary_centralCharacter :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ), CenN P ω → Unit1 ω →
        ∀ f ∈ P.V, ∃ B : ℝ, ∀ g, ‖f.1 g‖ ≤ B := by
  intro E _ _ _ P ω hc hu f hf
  obtain ⟨φ, rfl⟩ := LinearMap.mem_range.mp (UpperTheory.V.Cm.mem_range_ofCusp.2 (P.cusp f hf))
  obtain ⟨B₀, hB₀⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ.2
  refine ⟨B₀, fun g => ?_⟩
  let u : (A E)ˣ := posIdeleHom E (rpowHom ((((2 : ℕ) : ℝ) * Module.finrank ℚ E))⁻¹ (detModule E 2 g))
  have e : Matrix.GeneralLinearGroup.scalar (Fin 2) u = centralSection E 2 (detModule E 2 g) := Units.ext rfl
  have h2 : (centralSection E 2 (detModule E 2 g))⁻¹ * g ∈ normOneGL (K := E) (n := 2) := by
    rw [mem_normOneGL_iff_detModule, map_mul, map_inv, detModule_centralSection two_pos, inv_mul_cancel]
  have h3 := hc _ hf u ((centralSection E 2 (detModule E 2 g))⁻¹ * g)
  rw [e, mul_inv_cancel_left] at h3
  rw [show (UpperTheory.V.Cm.ofCusp E 2 φ).1 g = _ from h3, norm_mul, hu, one_mul]
  exact hB₀ _ h2
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem volume_fundamental_domain_two : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 :=
  GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain

private theorem cont_nE {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
  UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))

private theorem int_Wo {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) {f : GL (Fin 2) (A E) → ℂ}
    (hf : Continuous f) (h : GL (Fin 2) (A E)) :
    IntegrableOn (fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
  have hg : Continuous fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1) :=
    (hf.comp ((cont_nE D).mul continuous_const)).mul
      (UpperTheory.ConvolutionTheory.R2.Pp.cont_ψ.comp (continuous_apply 1))
  obtain ⟨C, hC, hs⟩ := UpperTheory.ConvolutionTheory.R2.Pp.exists_cpt (F := ℚ)
  have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
  have hsub : FS2 ℚ ⊆ Set.univ.pi fun _ : Fin 2 => C := Set.pi_mono fun _ _ => hs
  unfold adeleMeasurePi
  exact (hg.continuousOn.integrableOn_compact hK).mono_set hsub

theorem UpperTheory.whittakerPeriod_add_smul_and_norm_le :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E),
        (∀ f f' : GL (Fin 2) (A E) → ℂ, Continuous f → Continuous f' → ∀ h, Wo D (f + f') h = Wo D f h + Wo D f' h) ∧
        (∀ (c : ℂ) (f : GL (Fin 2) (A E) → ℂ) h, Wo D (c • f) h = c * Wo D f h) ∧
        ∀ (f : GL (Fin 2) (A E) → ℂ) (B : ℝ) h, (∀ g, ‖f g‖ ≤ B) → ‖Wo D f h‖ ≤ B := by
  intro E _ _ D
  refine ⟨fun f f' hf hf' h => ?_, fun c f h => ?_, fun f B h hB => ?_⟩
  · unfold Wo
    rw [← integral_add (int_Wo D hf h) (int_Wo D hf' h)]
    simp only [Pi.add_apply, add_mul]
  · unfold Wo
    rw [← integral_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · have := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasurePi (ι := Fin 2) ℚ) (s := FS2 ℚ)
      (f := fun u => f (nE D u * h) * ψ (u 1)) (C := B) (by rw [volume_fundamental_domain_two]; exact ENNReal.one_lt_top)
      fun u _ => by rw [norm_mul, UpperTheory.ConvolutionTheory.R2.Pp.norm_ψ, mul_one]; exact hB _
    rwa [measureReal_def, volume_fundamental_domain_two, ENNReal.toReal_one, mul_one] at this
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.whittaker_sum_mul_eq_sum_mul_whittaker :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ι : Type) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin 2) (A E) → ℂ), (∀ i, Continuous (φ i)) → (∀ i, ∃ B : ℝ, ∀ g, ‖φ i g‖ ≤ B) → ∀ h : GL (Fin 2) (A E), Wo D (fun g => ∑ i ∈ s, c i * φ i g) h = ∑ i ∈ s, c i * Wo D (φ i) h := by
  intro E _ _ D ι s c φ hc hb h
  haveI : IsFiniteMeasure ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) := ⟨by
    rw [Measure.restrict_apply_univ]
    have h1 : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 :=
      GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain
    rw [h1]
    exact ENNReal.one_lt_top⟩
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have hn : Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
    UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))
  have hi : ∀ i, Integrable (fun u : Fin 2 → A ℚ => φ i (nE D u * h) * ψ (u 1))
      ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) := by
    intro i
    obtain ⟨B, hB⟩ := hb i
    refine Integrable.of_bound (C := B)
      (((hc i).comp (hn.mul continuous_const)).mul
        (hψ.comp (continuous_apply 1))).aestronglyMeasurable ?_
    refine ae_of_all _ fun u => ?_
    rw [norm_mul, show ‖ψ (u 1)‖ = 1 from Circle.norm_coe _, mul_one]
    exact hB _
  have e : ∀ u : Fin 2 → A ℚ, (∑ i ∈ s, c i * φ i (nE D u * h)) * ψ (u 1) =
      ∑ i ∈ s, c i * (φ i (nE D u * h) * ψ (u 1)) := fun u => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  simp only [Wo, e]
  rw [integral_finsetSum _ fun i _ => (hi i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem cover : ∃ C : Set (Fin 2 → A ℚ), IsCompact C ∧ FS2 ℚ ⊆ C := by
  obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
    ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  exact ⟨Set.univ.pi fun _ : Fin 2 => C, isCompact_univ_pi fun _ => hC, fun x hx i hi => hEC (hx i hi)⟩

private theorem cont_nE' {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous fun u : Fin 2 → A ℚ => nE D u :=
  continuous_gl.comp (continuous_nU.comp ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
    ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))

private theorem deriv_at {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (f : Sm E 2)
    (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2) (x : GL (Fin 2) (A E)) (c0 : c 0 = 1)
    (cadd : ∀ s t, c (s + t) = c s * c t) (cd : HasDerivAt (fun t => toL (c t).val) X 0) (t : ℝ) :
    HasDerivAt (fun τ => f.1 (x * infGL E 2 (c τ))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) t := by
  have h := hasDerivAt_curve f (x * infGL E 2 (c t)) c X c0 cd
  have h2 : HasDerivAt (fun s => f.1 (x * infGL E 2 (c t) * infGL E 2 (c s))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) (t - t) := by
    rw [sub_self]; exact h
  have h3 := HasDerivAt.comp_sub_const t t h2
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  have e : c τ = c t * c (τ - t) := by rw [← cadd]; congr 1; ring
  simp only [e, map_mul, mul_assoc]

theorem UpperTheory.hasDerivAt_whittakerPeriod_oneParameter :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2) (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2)
        (g : GL (Fin 2) (A E)), c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 →
        Continuous f.1 → Continuous (lie E 2 X f).1 → (∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B) →
        HasDerivAt (fun t : ℝ => Wo D f.1 (g * infGL E 2 (c t))) (Wo D (lie E 2 X f).1 g) 0 := by
  intro E _ _ _ D f c X g c0 cadd cd hf hl ⟨B, hB⟩
  obtain ⟨C, hC, hsub⟩ := cover
  have hfin : adeleMeasurePi ℚ (FS2 ℚ) < ⊤ := (measure_mono hsub).trans_lt hC.measure_lt_top
  haveI : IsFiniteMeasure ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := ⟨by simpa using hfin⟩
  have hn := cont_nE' D
  have hψ : Continuous fun u : Fin 2 → A ℚ => ψ (u 1) := continuous_ψ.comp (continuous_apply 1)
  have hF : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => f.1 (nE D u * h) * ψ (u 1) :=
    fun h => (hf.comp (hn.mul continuous_const)).mul hψ
  have hF' : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => (lie E 2 X f).1 (nE D u * h) * ψ (u 1) :=
    fun h => (hl.comp (hn.mul continuous_const)).mul hψ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (adeleMeasurePi ℚ).restrict (FS2 ℚ)) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t u => f.1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (F' := fun t u => (lie E 2 X f).1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (bound := fun _ => B) Filter.univ_mem
    (Eventually.of_forall fun t => (hF _).aestronglyMeasurable)
    (((hF _).continuousOn.integrableOn_compact hC).mono_set hsub)
    (hF' _).aestronglyMeasurable
    (ae_of_all _ fun u t _ => by rw [norm_mul, norm_ψ, mul_one]; exact hB _)
    (integrable_const _)
    (ae_of_all _ fun u t _ => by
      have h := deriv_at f c X (nE D u * g) c0 cadd cd t
      simp only [mul_assoc] at h
      exact h.mul_const (ψ (u 1)))
  have h2 := key.2
  simp only [c0, map_one, mul_one] at h2
  exact h2
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re' (x : A ℚ) : |UpperTheory.ConvolutionTheory.RankTwoDescent.re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

private theorem re_mul' (a b : A ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (a * b) = UpperTheory.ConvolutionTheory.RankTwoDescent.re a * UpperTheory.ConvolutionTheory.RankTwoDescent.re b := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, map_mul, Pi.mul_apply]

private theorem re_add' (a b : A ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (a + b) = UpperTheory.ConvolutionTheory.RankTwoDescent.re a + UpperTheory.ConvolutionTheory.RankTwoDescent.re b := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, map_add (f := _), Pi.add_apply]

private theorem pInf_id' (u : (TR.Rinf ℚ)ˣ) : TR.pInf ℚ (TR.infId ℚ u).val = u.val := by
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ _) = _
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  simp [h]

private theorem re_iy' {s : ℝ} (hs : s ≠ 0) : UpperTheory.ConvolutionTheory.RankTwoDescent.re (UpperTheory.ConvolutionTheory.RankTwoDescent.iy s : A ℚ) = s := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, UpperTheory.ConvolutionTheory.RankTwoDescent.iy, dite_eq_right hs, pInf_id']

private theorem snd_iy' {s : ℝ} (hs : s ≠ 0) : (UpperTheory.ConvolutionTheory.RankTwoDescent.iy s : A ℚ).2 = 1 := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.iy, dite_eq_right hs]
  change (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 0 + 0 = 1
  simp

theorem UpperTheory.schwartzBruhat_translate_decay_bound :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ N : ℕ,
        ∃ (B κ : ℝ) (L : Set (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ)), 0 ≤ B ∧ 0 < κ ∧ κ ≤ 1 ∧ IsCompact L ∧
          ∀ (t : ℝ), ∀ k ∈ C, ∀ y : Fin 2 → A ℚ,
            ‖Φ fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * (y ᵥ* k.val) j‖ ≤
                B * ((1 + κ * Real.exp t * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|)) ^ N)⁻¹ ∧
              (Φ (fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * (y ᵥ* k.val) j) ≠ 0 → (fun j => (y j).2) ∈ L) := by
  intro Φ hΦ C hC N
  obtain ⟨C0, hC0, L0, hL0, hmaj⟩ := GroundTheory.Automorphic.GJGlobal.exists_majorant_pi hΦ N
  have hinv : Continuous fun k : GL (Fin 2) (A ℚ) => (k⁻¹).val :=
    Units.continuous_val.comp continuous_inv
  have hent : ∀ i j, Continuous fun k : GL (Fin 2) (A ℚ) => (k⁻¹).val i j :=
    fun i j => hinv.matrix_elem i j
  have hnorm : ∀ i j, Continuous fun k : GL (Fin 2) (A ℚ) =>
      ‖((k⁻¹).val i j).1 Rat.infinitePlace‖ := fun i j =>
    (((continuous_apply Rat.infinitePlace).comp continuous_fst).comp (hent i j)).norm
  obtain ⟨B1, hB1⟩ := hC.exists_bound_of_continuousOn
    (f := fun k : GL (Fin 2) (A ℚ) => ∑ i, ∑ j, ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => hnorm i j).continuousOn
  have hBk0 : 0 ≤ max B1 0 := le_max_right _ _
  have hBk : ∀ k ∈ C, ∀ i j, |UpperTheory.ConvolutionTheory.RankTwoDescent.re ((k⁻¹).val i j)| ≤ max B1 0 := by
    intro k hk i j
    rw [abs_re']
    have h1 := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB1 k hk))
    refine le_trans ?_ (h1.trans (le_max_left _ _))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  generalize max B1 0 = Bk at hBk0 hBk
  have hpos : 0 < 1 + 4 * Bk := by linarith
  let f : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × GL (Fin 2) (A ℚ) → Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ :=
    fun p j => p.1 0 * ((p.2⁻¹).val 0 j).2 + p.1 1 * ((p.2⁻¹).val 1 j).2
  have hf : Continuous f := by
    refine continuous_pi fun j => ?_
    exact (((continuous_apply 0).comp continuous_fst).mul
        (continuous_snd.comp ((hent 0 j).comp continuous_snd))).add
      (((continuous_apply 1).comp continuous_fst).mul
        (continuous_snd.comp ((hent 1 j).comp continuous_snd)))
  refine ⟨C0, 1 / (1 + 4 * Bk), f '' (L0 ×ˢ C), hC0, by positivity,
    (div_le_one hpos).2 (by linarith), (hL0.prod hC).image hf, fun t k hk y => ?_⟩
  have het : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hyz : ∀ j, y j = (y ᵥ* k.val) 0 * (k⁻¹).val 0 j + (y ᵥ* k.val) 1 * (k⁻¹).val 1 j := by
    intro j
    have h : (y ᵥ* k.val) ᵥ* (k⁻¹).val = y := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    conv_lhs => rw [← h]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  generalize hz : y ᵥ* k.val = z at hyz ⊢
  generalize hx : (fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * z j) = x
  have hxj : ∀ j, x j = (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * z j := fun j => by rw [← hx]
  have hxT : ∀ j, Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z j)| ≤ ‖infPartPi x‖ := by
    intro j
    have e : Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z j)| = |UpperTheory.ConvolutionTheory.RankTwoDescent.re (x j)| := by
      rw [hxj, re_mul', re_iy' het, abs_mul, abs_of_pos (Real.exp_pos t)]
    rw [e, abs_re']
    exact (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ _).trans
      (norm_le_pi_norm (infPartPi x) j)
  have hyb : ∀ j, |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y j)| ≤
      Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|) := by
    intro j
    rw [hyz j, re_add', re_mul', re_mul']
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, mul_add, mul_comm Bk, mul_comm Bk]
    exact add_le_add (mul_le_mul_of_nonneg_left (hBk k hk 0 j) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hBk k hk 1 j) (abs_nonneg _))
  have hT : 0 ≤ ‖infPartPi x‖ := norm_nonneg _
  have hkey : 1 / (1 + 4 * Bk) * Real.exp t *
      (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) ≤ ‖infPartPi x‖ := by
    have hS : Real.exp t * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) ≤
        4 * Bk * ‖infPartPi x‖ := by
      have h0 := mul_le_mul_of_nonneg_left (hyb 0) (Real.exp_pos t).le
      have h1 := mul_le_mul_of_nonneg_left (hyb 1) (Real.exp_pos t).le
      have h2 : Real.exp t * (Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|)) ≤
          Bk * (‖infPartPi x‖ + ‖infPartPi x‖) := by
        rw [show Real.exp t * (Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|)) =
          Bk * (Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|) by ring]
        exact mul_le_mul_of_nonneg_left (add_le_add (hxT 0) (hxT 1)) hBk0
      nlinarith
    rw [mul_assoc, one_div, inv_mul_le_iff₀ hpos]
    nlinarith
  have hm := hmaj x
  constructor
  · by_cases hmem : finPartPi x ∈ L0
    · rw [Set.indicator_of_mem hmem, mul_one] at hm
      refine hm.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      have hb : 0 ≤ 1 / (1 + 4 * Bk) * Real.exp t *
          (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) := by positivity
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) N)
    · rw [Set.indicator_of_notMem hmem, mul_zero] at hm
      exact hm.trans (by positivity)
  · intro hne
    have hmem : finPartPi x ∈ L0 := by
      by_contra hmem
      rw [Set.indicator_of_notMem hmem, mul_zero] at hm
      exact hne (norm_le_zero_iff.1 hm)
    refine ⟨(finPartPi x, k), ⟨hmem, hk⟩, ?_⟩
    have hfin : ∀ j, finPartPi x j = (z j).2 := by
      intro j
      change (x j).2 = _
      rw [hxj]
      change (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ).2 * (z j).2 = _
      rw [snd_iy' het, one_mul]
    funext j
    simp only [f, hfin]
    rw [hyz j]
    rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem rt_infGL_lie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) =
      lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z))
    (Units.inv_mul_cancel_right (y.val * X) y).symm

private theorem lie_rt_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (X : Matrix (Fin a) (Fin a) (Cinf E)) (h : GL (Fin a) (A E)) :
    ∃ Y : Lie E a, lie E a (toL X) * rt E a h = rt E a h * lie E a Y := by
  set y := Matrix.GeneralLinearGroup.map (pInf E) h with hy
  set κ := Matrix.GeneralLinearGroup.map (pFin E) h with hκ
  have hh : h = infGL E a y * finGL E a κ := (infGL_mul_finGL h).symm
  refine ⟨toL ((y⁻¹).val * X * y.val), ?_⟩
  have e : y.val * ((y⁻¹).val * X * y.val) * (y⁻¹).val = X := by
    simp [Matrix.mul_assoc]
  have key := rt_infGL_lie y ((y⁻¹).val * X * y.val)
  rw [e] at key
  conv_lhs => rw [hh, map_mul, ← mul_assoc, ← key, mul_assoc, lie_rt_fin, ← mul_assoc]
  rw [← map_mul, ← hh]

theorem UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (X : Lie E 2) (φ : GL (Fin 2) (A E) → ℂ), φ ∈ Tr P → ∃ f : Sm E 2, f.1 = φ ∧ (lie E 2 X f).1 ∈ Tr P := by
  intro E _ _ _ P X φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨f, hf, h, rfl⟩ := hφ
    obtain ⟨Y, hY⟩ := lie_rt_eq (a := 2) (E := E) X h
    refine ⟨rt E 2 h ⟨f.1, f.2⟩, rfl, ?_⟩
    have e : lie E 2 X (rt E 2 h f) = rt E 2 h (lie E 2 Y f) := LinearMap.congr_fun hY f
    have hm : lie E 2 Y f ∈ P.V := P.stable (.lie Y) f hf
    refine Submodule.subset_span ⟨_, hm, h, ?_⟩
    rw [show (⟨f.1, f.2⟩ : Sm E 2) = f from rfl, e]
    rfl
  | zero => exact ⟨0, rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨fa, rfl, ha⟩ := ha
    obtain ⟨fb, rfl, hb⟩ := hb
    refine ⟨fa + fb, rfl, ?_⟩
    rw [map_add (f := _)]
    exact (Tr P).add_mem ha hb
  | smul c a _ ha =>
    obtain ⟨fa, rfl, ha⟩ := ha
    refine ⟨c • fa, rfl, ?_⟩
    rw [map_smul]
    exact (Tr P).smul_mem c ha
end
