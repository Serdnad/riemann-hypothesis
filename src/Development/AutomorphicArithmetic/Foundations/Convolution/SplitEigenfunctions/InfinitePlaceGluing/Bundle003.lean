module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle002
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle016
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle013
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle014
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle017
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle031
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle023
public import Development.AutomorphicArithmetic.WhittakerHecke.ThetaSeriesPoissonFunctionalEquation
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle021
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle030
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle018
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle015
public import Development.AutomorphicArithmetic.WhittakerHecke.LieActionPreservesRightInvarianceFiniteAdelic
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle026
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

private theorem thetaPhi (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2))
    (C C' : Set (GL (Fin 2) (A ℚ))) (hC : IsCompact C) (hC' : IsCompact C') (n : ℕ) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ g : G1 ℚ, ∀ k ∈ C, ∀ k' ∈ C',
      ‖φ (em E (gl g * k)) * ThR Φ t (gl g * k')‖ ≤ B * Real.exp (-((n : ℝ) * t)) := by
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red ℚ
  have hK : IsCompact (KK ℚ) := (UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).2
  have cpt : ∀ S : Set (GL (Fin 2) (A ℚ)), IsCompact S →
      IsCompact ((fun p : G1 ℚ × GL (Fin 2) (A ℚ) => gl p.1 * p.2) '' (KK ℚ ×ˢ S)) := fun S hS =>
    (hK.prod hS).image ((UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_fst).mul continuous_snd)
  obtain ⟨r, B₁, h₁⟩ := UpperTheory.norm_thetaSeries_siegelSet_le_exp Φ hΦ _ (cpt C' hC') c hc n
  obtain ⟨B₂, h₂⟩ := UpperTheory.norm_admissible_baseChange_siegelSet_le D ω φ hφ _ (cpt C hC) c hc r
  refine ⟨B₂ * B₁, fun t ht g k hk k' hk' => ?_⟩
  obtain ⟨γ, b, a, κ, hκ, hg, hca⟩ := hred g
  have ea : ∀ h : GL (Fin 2) (A ℚ), gl (nU b * mD a * κ) * h = gl (nU b * mD a) * (gl κ * h) := fun h => by
    have hm : gl (nU b * mD a * κ) = gl (nU b * mD a) * gl κ := map_mul _ _ _
    rw [hm, mul_assoc]
  have e1 : φ (em E (gl g * k)) = φ (em E (gl (nU b * mD a) * (gl κ * k))) := by
    rw [← ea, ← hg, UpperTheory.automorphicForm_baseChange_ratSL2_mul_invariant D ω φ hφ]
  have e2 : ThR Φ t (gl g * k') = ThR Φ t (gl (nU b * mD a) * (gl κ * k')) := by
    rw [← ea, ← hg, UpperTheory.thetaSeries_ratSL2_mul_invariant]
  have p₂ := h₂ b a _ ⟨(κ, k), ⟨hκ, hk⟩, rfl⟩ hca
  have p₁ := h₁ t ht b a _ ⟨(κ, k'), ⟨hκ, hk'⟩, rfl⟩ hca
  have hab : 0 < ab a := UpperTheory.ConvolutionTheory.R2.M.ab_pos a
  rw [e1, e2, norm_mul]
  calc _ ≤ (B₂ * (ab a)⁻¹ ^ r) * (B₁ * Real.exp (-((n : ℝ) * t)) * ab a ^ r) :=
        mul_le_mul p₂ p₁ (norm_nonneg _) ((norm_nonneg _).trans p₂)
    _ = B₂ * B₁ * Real.exp (-((n : ℝ) * t)) := by
        rw [inv_pow]; field_simp

private theorem measPhi (ω : HChar ℚ) (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ) {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (h : X → GL (Fin 2) (A ℚ)) (hh : Continuous h) : Measurable fun x => φ (em E (h x)) :=
  (hφ.cont.comp ((UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).1.comp hh)).measurable

private theorem irMeas (D : Dat ℚ E) (ω χ : HChar ℚ) (M : Meas ℚ) (U : UMeas) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) : StronglyMeasurable (Ir M U χ φ Φ) := by
  haveI := U.prob
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  have hdM := (UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).2.1
  have hc : Continuous fun p : (ℝ × IdeleGroup ℚ) × G1 ℚ => gl p.2 * dM p.1.2 :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hdM.comp (continuous_snd.comp continuous_fst))
  have h1 : StronglyMeasurable fun p : (ℝ × IdeleGroup ℚ) × G1 ℚ =>
      φ (em E (gl p.2 * dM p.1.2)) * ThR Φ p.1.1 (gl p.2 * dM p.1.2) :=
    ((measPhi ω D φ hφ _ hc).mul (UpperTheory.measurable_thetaSeries_comp_continuous Φ hΦ _ _ (continuous_fst.comp continuous_fst) hc)).stronglyMeasurable
  have h2 := h1.integral_prod_right' (ν := M.μ.restrict M.D)
  have hχ : StronglyMeasurable fun x : ℝ × IdeleGroup ℚ => ((χ.1 x.2 : ℂˣ) : ℂ) :=
    (Units.continuous_val.comp (χ.2.1.comp continuous_snd)).stronglyMeasurable
  exact (hχ.mul h2).integral_prod_right' (ν := U.υ)

private theorem irDecay (D : Dat ℚ E) (ω χ : HChar ℚ) (M : Meas ℚ) (U : UMeas) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (hP : Per M U χ φ = 0)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) (n : ℕ) :
    ∃ B : ℝ, ∀ t, ‖Ir M U χ φ Φ t‖ ≤ B * Real.exp (-((n : ℝ) * |t|)) := by
  haveI := U.prob
  obtain ⟨hUc, hU1⟩ := UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one
  have hdM := (UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).2.1
  obtain ⟨Ψ, hΨ, hpois⟩ := UpperTheory.thetaSeries_poisson_functional_equation Φ hΦ
  set C : Set (GL (Fin 2) (A ℚ)) := (fun u : (A ℚ)ˣ => dM u) '' UU with hCdef
  set C' : Set (GL (Fin 2) (A ℚ)) := (fun u : (A ℚ)ˣ => (gl (wW ℚ))⁻¹ * dM u⁻¹) '' UU with hC'def
  have hC : IsCompact C := hUc.image hdM
  have hc' : Continuous fun u : (A ℚ)ˣ => (gl (wW ℚ))⁻¹ * dM u⁻¹ := continuous_const.mul (hdM.comp continuous_inv)
  have hC' : IsCompact C' := hUc.image hc'
  obtain ⟨Bp, hBp⟩ := thetaPhi D ω φ hφ Φ hΦ C C hC hC n
  obtain ⟨Bm, hBm⟩ := thetaPhi D ω φ hφ Ψ hΨ C C' hC hC' (n + 2)
  set V : ℝ := M.μ.real M.D with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  obtain ⟨Bφ, hBφ⟩ := hφ.bdd
  have hcu : Continuous fun p : IdeleGroup ℚ × G1 ℚ => gl p.2 * dM p.1 :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hdM.comp continuous_fst)
  have hcu' : Continuous fun p : IdeleGroup ℚ × G1 ℚ => gl p.2 * ((gl (wW ℚ))⁻¹ * dM p.1⁻¹) :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hc'.comp continuous_fst)
  have mφ : Measurable fun p : IdeleGroup ℚ × G1 ℚ => φ (em E (gl p.2 * dM p.1)) := measPhi ω D φ hφ _ hcu
  refine ⟨(|Bp| + |Bm|) * V, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  ·
    have hb : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u)‖ ≤ Bp * Real.exp (-((n : ℝ) * t)) :=
      fun u hu g => hBp t ht g _ ⟨u, hu, rfl⟩ _ ⟨u, hu, rfl⟩
    have hm : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) => φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u)) :=
      mφ.mul (UpperTheory.measurable_thetaSeries_comp_continuous Φ hΦ _ _ continuous_const hcu)
    have := (UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm hb).2.2
    rw [abs_of_nonneg ht]
    refine le_trans this ?_
    have hex := Real.exp_pos (-((n : ℝ) * t))
    have : Bp ≤ |Bp| + |Bm| := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    calc Bp * Real.exp (-((n : ℝ) * t)) * V ≤ (|Bp| + |Bm|) * Real.exp (-((n : ℝ) * t)) * V := by gcongr
      _ = _ := by ring
  ·
    set e : ℂ := (Real.exp (-(2 * t)) : ℂ) with he
    set c₀ : ℂ := -Φ 0 + e * Ψ 0 with hc₀
    have hb1 : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u))‖ ≤ Bφ := fun _ _ _ => hBφ _
    have hb2 : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹))‖ ≤
        Bm * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) :=
      fun u hu g => hBm (-t) (by linarith) g _ ⟨u, hu, rfl⟩ _ ⟨u, hu, rfl⟩
    have hm1 : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) => φ (em E (gl g * dM u))) := mφ
    have hm2 : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) =>
        φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹))) :=
      mφ.mul (UpperTheory.measurable_thetaSeries_comp_continuous Ψ hΨ _ _ continuous_const hcu')
    obtain ⟨i1, j1, -⟩ := UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm1 hb1
    obtain ⟨i2, j2, n2⟩ := UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm2 hb2
    have hae : ∀ᵐ u ∂U.υ, u ∈ UU := by
      have := U.supp
      exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun u hu => by simpa using hu
    have key : Ir M U χ φ Φ t = c₀ * Per M U χ φ + e * ∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D,
        φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) ∂M.μ ∂U.υ := by
      unfold Per
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul _) (j2.const_mul _)]
      unfold Ir
      refine integral_congr_ae (hae.mono fun u hu => ?_)
      have hin : ∫ g in M.D, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) ∂M.μ =
          c₀ * (∫ g in M.D, φ (em E (gl g * dM u)) ∂M.μ) + e * ∫ g in M.D,
            φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) ∂M.μ := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((i1 u hu).const_mul _) ((i2 u hu).const_mul _)]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        simp only []
        rw [hpois t g u (hU1 u hu)]
        ring
      simp only []
      rw [hin]
      ring
    rw [key, hP, mul_zero, zero_add, norm_mul, he, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, abs_of_neg ht]
    refine (mul_le_mul_of_nonneg_left n2 (Real.exp_pos _).le).trans ?_
    have hex : Real.exp (-(2 * t)) * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) = Real.exp (-((n : ℝ) * -t)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have : Bm ≤ |Bp| + |Bm| := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    have hpos := Real.exp_pos (-((n : ℝ) * -t))
    calc Real.exp (-(2 * t)) * (Bm * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) * V)
        = Bm * (Real.exp (-(2 * t)) * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t)))) * V := by ring
      _ = Bm * Real.exp (-((n : ℝ) * -t)) * V := by rw [hex]
      _ ≤ (|Bp| + |Bm|) * Real.exp (-((n : ℝ) * -t)) * V := by gcongr
      _ = _ := by ring

theorem ent_of :
    Ent := by
  intro E _ _ _ D P ω χ _ hω hχ M U φ hφ hP Φ hΦ
  have hχ1 : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := fun a => by
    have h := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hχ a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one] at h
    rw [show ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1 from hω a, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  exact UpperTheory.differentiable_integral_exp_mul_of_rapid_decay _ (irMeas D ω χ M U φ hφ Φ hΦ).aestronglyMeasurable fun n => irDecay D ω χ M U φ hφ hχ1 hP Φ hΦ n

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.SH

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem re_iy (y : ℝ) (hy : y ≠ 0) : re ((iy y : (A ℚ)ˣ) : A ℚ) = y := by
  have h : iy y = TR.infId ℚ ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ hy, funext fun _ => inv_mul_cancel₀ hy⟩ := dif_neg hy
  have h2 : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  rw [h, re]
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ (fun _ => y)) _ = y
  simp [h2]

private def Q (D : Dat ℚ E) (L N : ℕ) (f : Sm E 2) (X : Lie E 2) : Prop :=
  (∀ (y : (A ℚ)ˣ) x, Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x) ≠ 0 → ∀ v, Bad N v → Dv L v ((y : A ℚ) - 1)) ∧
  ∀ t ∈ UU, (∀ v, Dv L v ((t : A ℚ) - 1)) → ∀ (y : (A ℚ)ˣ) x,
    Wo D (lie E 2 X f).1 (em E (aE (y * t)) * infGL E 2 x) = Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x)

private theorem eig_smul {w : H.P E} {B : Multiset ℂˣ} {f : GL (Fin 2) (A E) → ℂ} (c : ℂ)
    (h : UpperTheory.V.Af.Smo.EigAt w B f) : UpperTheory.V.Af.Smo.EigAt w B (c • f) := fun g => by
  have h0 := h g
  refine ⟨h0.card, fun g' k hk => ?_, fun ϖ hϖ j hj g' => ?_⟩
  · simpa using congrArg (c * ·) (h0.inv g' k hk)
  · have h1 := h0.eig ϖ hϖ j hj g'
    simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_left_comm, ← h1, ← smul_eq_mul, smul_finsum]
    exact finsum_congr fun x => by rw [smul_eq_mul, mul_left_comm]

private theorem gd_smul {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {f : Sm E 2} {X : Lie E 2} {c : ℂ}
    (hG : Gd D P L N f.1) (hm : (lie E 2 X f).1 ∈ Tr P) (hQ : Q D L N f X) :
    Gd D P L N (c • (lie E 2 X f).1) := by
  have hs : ∀ h, Wo D (c • (lie E 2 X f).1) h = c * Wo D (lie E 2 X f).1 h := fun h => (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).2.1 c _ h
  refine ⟨hG.pos, hG.dvd, hG.same, (Tr P).smul_mem c hm, hG.pl, fun w hw => ?_, fun k hk g => ?_, fun y x hne => ?_, fun t ht hL y x => ?_⟩
  · obtain ⟨h1, B, h2, h3⟩ := hG.fix w hw
    refine ⟨fun g k hk => ?_, B, h2, eig_smul c (UpperTheory.lie_action_preserves_satake_eigen_at_place E w B f X h3)⟩
    simpa using congrArg (c * ·) (UpperTheory.lie_action_preserves_fixed_at_place E w f X h1 g k hk)
  · have := UpperTheory.lie_action_preserves_right_invariance_finite_adelic E k hk.1 f X (hG.lev k hk) g
    simpa using congrArg (c * ·) this
  · rw [hs] at hne
    exact hQ.1 y x (right_ne_zero_of_mul hne)
  · rw [hs, hs, hQ.2 t ht hL y x]

private theorem q_cv {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {f : Sm E 2} (k : GL (Fin 2) (A E))
    (hG : Gd D P L N f.1) (hc : Continuous f.1) (hX : Continuous (lie E 2 (toL (XB D k)) f).1)
    (hB : ∃ B : ℝ, ∀ g, ‖(lie E 2 (toL (XB D k)) f).1 g‖ ≤ B) : Q D L N f (toL (XB D k)) := by
  obtain ⟨h0, hadd, hd, -⟩ := UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D k
  have key : ∀ g, HasDerivAt (fun t : ℝ => Wo D f.1 (g * infGL E 2 (cv D k t)))
      (Wo D (lie E 2 (toL (XB D k)) f).1 g) 0 := fun g =>
    UpperTheory.hasDerivAt_whittakerPeriod_oneParameter E D f (cv D k) _ g h0 hadd hd hc hX hB
  refine ⟨fun y x hne v hv => ?_, fun t ht hL y x => ?_⟩
  · by_contra hcon
    have hz : (fun s : ℝ => Wo D f.1 (em E (aE y) * infGL E 2 x * infGL E 2 (cv D k s))) = fun _ => 0 := funext fun s => by
      by_contra h1
      rw [mul_assoc, ← map_mul] at h1
      exact hcon (hG.supp y _ h1 v hv)
    have h2 := key (em E (aE y) * infGL E 2 x)
    rw [hz] at h2
    exact hne (h2.unique (hasDerivAt_const _ _))
  · have h1 := key (em E (aE (y * t)) * infGL E 2 x)
    have h2 := key (em E (aE y) * infGL E 2 x)
    have e : (fun s : ℝ => Wo D f.1 (em E (aE (y * t)) * infGL E 2 x * infGL E 2 (cv D k s))) =
        fun s : ℝ => Wo D f.1 (em E (aE y) * infGL E 2 x * infGL E 2 (cv D k s)) := funext fun s => by
      rw [mul_assoc, mul_assoc, ← map_mul, hG.tor t ht hL y]
    rw [e] at h1
    exact h1.unique h2

private theorem lieDerivative_linear (f : Sm E 2) (a b c : ℝ) (X Y Z : Lie E 2) :
    (lie E 2 (a • X + b • Y + c • Z) f).1 = (a : ℂ) • (lie E 2 X f).1 + (b : ℂ) • (lie E 2 Y f).1 + (c : ℂ) • (lie E 2 Z f).1 := by
  rw [map_add (f := _), map_add (f := _), map_smul, map_smul, map_smul]
  funext g
  simp

private theorem whittaker_lieDerivative_linear {D : Dat ℚ E} {f : Sm E 2} (hc : ∀ X, Continuous (lie E 2 X f).1) (a b c : ℝ) (X Y Z : Lie E 2)
    (h : GL (Fin 2) (A E)) :
    Wo D (lie E 2 (a • X + b • Y + c • Z) f).1 h = a * Wo D (lie E 2 X f).1 h + b * Wo D (lie E 2 Y f).1 h + c * Wo D (lie E 2 Z f).1 h := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  rw [lieDerivative_linear, h1 _ _ (((hc X).const_smul _).add ((hc Y).const_smul _)) ((hc Z).const_smul _),
    h1 _ _ ((hc X).const_smul _) ((hc Y).const_smul _), h2, h2, h2]

private theorem quadraticCondition_linear {D : Dat ℚ E} {L N : ℕ} {f : Sm E 2} (hc : ∀ X, Continuous (lie E 2 X f).1) (a b c : ℝ) {X Y Z : Lie E 2}
    (hX : Q D L N f X) (hY : Q D L N f Y) (hZ : Q D L N f Z) : Q D L N f (a • X + b • Y + c • Z) := by
  refine ⟨fun y x hne v hv => ?_, fun t ht hL y x => ?_⟩
  · rw [whittaker_lieDerivative_linear hc] at hne
    by_contra hcon
    have h1 : Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hX.1 y x h v hv)
    have h2 : Wo D (lie E 2 Y f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hY.1 y x h v hv)
    have h3 : Wo D (lie E 2 Z f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hZ.1 y x h v hv)
    exact hne (by rw [h1, h2, h3]; ring)
  · rw [whittaker_lieDerivative_linear hc, whittaker_lieDerivative_linear hc, hX.2 t ht hL y x, hY.2 t ht hL y x, hZ.2 t ht hL y x]

private theorem xb_dec (D : Dat ℚ E) (t : ℝ) :
    toL (XB D (em E (rot t))) = (Real.cos t ^ 2) • toL (XB D (em E (rot 0))) + (Real.sin t ^ 2) • toL (XB D (em E (rot (Real.pi / 2)))) +
      (Real.cos t * Real.sin t) • ((2 : ℝ) • toL (XB D (em E (rot (Real.pi / 4)))) + (-1 : ℝ) • toL (XB D (em E (rot 0))) +
        (-1 : ℝ) • toL (XB D (em E (rot (Real.pi / 2))))) := by
  have c4 : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have s4 : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have m4 : Real.cos (Real.pi / 4) * Real.sin (Real.pi / 4) = 1 / 2 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four, ← pow_two, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D t, UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D 0, UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D (Real.pi / 2), UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D (Real.pi / 4), c4, s4, m4]
  simp only [Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]
  funext i j w
  fin_cases i <;> fin_cases j <;> simp <;> ring

end UpperTheory.ConvolutionTheory.RankTwoDescent.SH

open UpperTheory.ConvolutionTheory.RankTwoDescent.SH in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.shift_of :
    TrAdm → Shift := by
  intro hT E _ _ _ D P ω χ hC hU hχ L N φ hG
  have adm := hT E D P ω χ hC hU hχ
  obtain ⟨f, rfl, -⟩ := UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates E P 0 φ hG.mem
  have hmem : ∀ X, (lie E 2 X f).1 ∈ Tr P := fun X => by
    obtain ⟨f', hf', hm⟩ := UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates E P X f.1 hG.mem
    rwa [show f' = f from Subtype.ext hf'] at hm
  have hc : ∀ X, Continuous (lie E 2 X f).1 := fun X => (adm _ (hmem X)).cont
  have hb : ∀ X, ∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B := fun X => (adm _ (hmem X)).bdd
  have hf0 := adm _ hG.mem
  have hq : ∀ k, Q D L N f (toL (XB D k)) := fun k => q_cv k hG hf0.cont (hc _) (hb _)
  set b0 : Lie E 2 := toL (XB D (em E (rot 0))) with hb0
  set b1 : Lie E 2 := toL (XB D (em E (rot (Real.pi / 2)))) with hb1
  set b2 : Lie E 2 := toL (XB D (em E (rot (Real.pi / 4)))) with hb2
  set b3 : Lie E 2 := (2 : ℝ) • b2 + (-1 : ℝ) • b0 + (-1 : ℝ) • b1 with hb3
  have hq3 : Q D L N f b3 := quadraticCondition_linear hc _ _ _ (hq _) (hq _) (hq _)
  set κ : ℂ := (2 * Real.pi * Complex.I)⁻¹ with hκ
  have hκ0 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨κ • (lie E 2 b1 f).1, κ • (lie E 2 b3 f).1, κ • (lie E 2 b0 f).1, gd_smul hG (hmem _) (hq _), gd_smul hG (hmem _) hq3,
    gd_smul hG (hmem _) (hq _), fun y t hy => ?_⟩
  obtain ⟨-, h2, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  have e := UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul E D f ⟨hf0.cont, hf0.left⟩ (fun X => ⟨hc X, hb X⟩) (iy y) (em E (rot t))
  rw [xb_dec D t, whittaker_lieDerivative_linear hc, re_iy y hy, ← map_mul] at e
  rw [h2, h2, h2]
  have e' : (y : ℂ) * Wo D f.1 (em E (aE (iy y) * rot t)) = κ * ((2 * Real.pi * Complex.I * (y : ℂ)) * Wo D f.1 (em E (aE (iy y) * rot t))) := by
    rw [hκ]; field_simp
  rw [e', ← e, hκ]
  push_cast
  ring

end
end
