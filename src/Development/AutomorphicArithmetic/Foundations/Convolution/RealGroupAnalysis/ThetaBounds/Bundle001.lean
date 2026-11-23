module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Aesop.Main
import GroundTheory.AutomorphicForms.Bundle012
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

set_option synthInstance.maxSize 1000

private theorem wt_eq_comp {F : Type} [Field F] [NumberField F]
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) :
    wt (F := F) K N =
      (fun p : (Fin 4 → mixedEmbedding.mixedSpace F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) =>
        ((1 + ‖p.1‖) ^ N)⁻¹ * K.indicator (fun _ => (1 : ℝ)) p.2) ∘ splitEquivPi F (Fin 4) := by
  funext v
  by_cases h : finPartPi v ∈ K
  · simp [wt, splitEquivPi_apply, h]
  · simp [wt, splitEquivPi_apply, h]

theorem UpperTheory.ConvolutionTheory.R2.Ff.wtInt :
    ∀ (F : Type) [Field F] [NumberField F], WtInt F := by
  intro F _ _
  refine ⟨Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1, fun K hK => ?_⟩
  rw [wt_eq_comp, measurePreserving_splitEquivPi.integrable_comp_emb
    (splitEquivPi F (Fin 4)).measurableEmbedding]
  refine Integrable.mul_prod (f := fun x : Fin 4 → mixedEmbedding.mixedSpace F => ((1 + ‖x‖) ^ (Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1))⁻¹)
    (g := fun y => K.indicator (fun _ => (1 : ℝ)) y) ?_ ?_
  · have h := integrable_one_add_norm (E := Fin 4 → mixedEmbedding.mixedSpace F)
      (μ := mixedMeasurePi F) (r := ((Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1 : ℕ) : ℝ))
      (by push_cast; linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    have hx : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
    simp only [Real.rpow_neg hx, Real.rpow_natCast]
  · exact (integrable_indicator_iff hK.measurableSet).2
      (integrableOn_const hK.measure_lt_top.ne)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem pInf_sInf (x : TR.Rinf F) : TR.pInf F (TR.sInf F x) = x :=
  (TR.infEq F).symm_apply_apply x

private theorem pFin_sInf (x : TR.Rinf F) : pFin F (TR.sInf F x) = 0 := rfl

private noncomputable def cU (w : InfinitePlace F) (t : ℝ) : GL (Fin 2) (TR.Rinf F) :=
  ⟨!![1, Pi.single w t; 0, 1], !![1, Pi.single w (-t); 0, 1],
    by
      ext i j v
      fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h],
    by
      ext i j v
      fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h]⟩

private theorem cU_val (w : InfinitePlace F) (t : ℝ) : (cU w t).val = !![1, Pi.single w t; 0, 1] := rfl

private theorem cU_add (w : InfinitePlace F) (s t : ℝ) : cU w (s + t) = cU w s * cU w t := by
  refine Units.ext ?_
  rw [Units.val_mul, cU_val, cU_val, cU_val]
  ext i j v
  fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h, add_comm]

private theorem cU_der (w : InfinitePlace F) :
    HasDerivAt (fun t => TR.toL (cU w t).val) (TR.toL (Matrix.single 0 1 (Pi.single w 1))) 0 := by
  have e : (fun t => TR.toL (cU w t).val) =
      fun t : ℝ => TR.toL (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) + t • TR.toL (Matrix.single 0 1 (Pi.single w 1)) := by
    funext t
    ext i j v
    fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [cU_val, Matrix.single_apply, Pi.single_apply, h]
  rw [e]
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (TR.toL (Matrix.single 0 1 (Pi.single w 1)) : TR.Lie F 2)).const_add
    (TR.toL (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) : TR.Lie F 2)
  simpa only [id, one_smul] using h

private theorem unipotent_placeEmbed_gl (w : InfinitePlace F) (t : ℝ) : gl (nU (Fo.at1 w t)) = TR.infGL F 2 (cU w t) := by
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext ?_
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [cU_val, Fo.at1, nU, gl, Matrix.SpecialLinearGroup.toGL, pInf_sInf]
  · rw [TR.pFin_infGL]
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Fo.at1, nU, gl, Matrix.SpecialLinearGroup.toGL, pFin_sInf]

private theorem character_placeEmbed_exp (w : InfinitePlace F) (t : ℝ) (q : A F) :
    ψ (Fo.at1 w t * q) = Complex.exp (Fo.cc * ((t : ℂ) * Fo.cw w q)) := by
  rw [(UpperTheory.ConvolutionTheory.R2.C.splitA F).2]
  have h2 : (Fo.at1 w t * q).2 = 0 := by
    change (0 : FiniteAdeleRing (𝓞 F) F) * q.2 = 0
    exact zero_mul _
  rw [h2, AddChar.map_zero_eq_one, Circle.coe_one, mul_one, Finset.prod_eq_single w]
  · simp [Fo.at1, Fo.cc, Fo.cw, pInf_sInf]
  · intro v _ hv
    simp [Fo.at1, pInf_sInf, hv]
  · simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.curveE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), CurveE O W := by
  intro F E _ _ _ _ _ _ _ D O W w
  refine ⟨fun t => nU (Fo.at1 w t), cU w, ⟨cU_add w, cU_der w⟩, unipotent_placeEmbed_gl w, fun φ t v => ?_⟩
  have he : (O.e D.δ w φ).1 v = Fo.cc * Fo.cw w (q4 D.δ v) * φ.1 v := by
    have a : ∀ i j (χ : S4 F), (O.x w i (O.x w j χ)).1 v = Fo.cw w (v i) * (Fo.cw w (v j) * χ.1 v) := fun i j χ => by
      rw [O.x_apply, O.x_apply]
    simp only [Fo.Ops.e, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
    change Fo.cc * (((O.x w 2 (O.x w 2 φ)).1 v - Fo.cw w (rt D.δ) * (O.x w 3 (O.x w 3 φ)).1 v) - (O.x w 1 (O.x w 0 φ)).1 v) = _
    rw [a, a, a]
    simp only [Fo.cw, q4, map_sub, map_mul, map_pow, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    push_cast
    ring
  have e1 : (fun s => (W.Om (nU (Fo.at1 w s)) φ).1 v) =
      fun s : ℝ => Complex.exp (Fo.cc * ((s : ℂ) * Fo.cw w (q4 D.δ v))) * φ.1 v := by
    funext s
    rw [W.Om_n, character_placeEmbed_exp]
  simp only []
  rw [e1, W.Om_n, character_placeEmbed_exp, he]
  have h0 : HasDerivAt (fun s : ℝ => Fo.cc * ((s : ℂ) * Fo.cw w (q4 D.δ v))) (Fo.cc * Fo.cw w (q4 D.δ v)) t := by
    simpa using (((hasDerivAt_id t).ofReal_comp).mul_const (Fo.cw w (q4 D.δ v))).const_mul Fo.cc
  rw [← mul_assoc (Complex.exp _)]
  exact h0.cexp.mul_const (φ.1 v)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.rtInv :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], RtInv F := by
  intro F _ _ _ M u hu k
  haveI := M.haar
  haveI := M.right
  have hmp : MeasurePreserving (· * k) M.μ M.μ := measurePreserving_mul_right M.μ k
  have hemb : MeasurableEmbedding (· * k : G1 F → G1 F) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam F) ((Equiv.mulRight k) '' M.D) M.μ := by
    refine M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam F) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 F → G1 F) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D := by
    ext x; simp
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq M.fund hinv
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private lemma infiniteProjection_placeEmbed (w : InfinitePlace F) (t : ℝ) : TR.pInf F (Fo.at1 w t) = Pi.single w t := by
  change (TR.infEq F).symm (TR.infEq F (Pi.single w t)) = _
  exact RingEquiv.symm_apply_apply _ _

private lemma placeEmbedReal_zero (w : InfinitePlace F) : Fo.at1 w 0 = 0 := by
  simp [Fo.at1]

private lemma placeEmbedReal_finitePart (w : InfinitePlace F) (t : ℝ) : (Fo.at1 w t).2 = 0 := rfl

private lemma shift_zero (w : InfinitePlace F) (i : Fin 4) (v : V4 F) :
    v + Pi.single i (Fo.at1 w 0) = v := by
  simp [placeEmbedReal_zero]

private lemma finPart_shift (w : InfinitePlace F) (i : Fin 4) (v : V4 F) (t : ℝ) :
    finPartPi (v + Pi.single i (Fo.at1 w t)) = finPartPi v := by
  funext j
  by_cases h : j = i
  · subst h
    simp only [finPartPi, Pi.add_apply, Pi.single_eq_same]
    change (v j).2 + (Fo.at1 w t).2 = (v j).2
    rw [placeEmbedReal_finitePart, add_zero]
  · simp [finPartPi, Pi.single_eq_of_ne h]

private lemma coord_shift (w w' : InfinitePlace F) (i j : Fin 4) (v : V4 F) (t : ℝ) :
    ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ) =
      ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) := by
  by_cases h : j = i
  · subst h
    by_cases h' : w' = w
    · subst h'
      simp [map_add (f := _), infiniteProjection_placeEmbed]
    · simp [map_add (f := _), infiniteProjection_placeEmbed, h', Pi.single_eq_of_ne h']
  · simp [h, Pi.single_eq_of_ne h]

private lemma lin_der (a c : ℂ) : HasDerivAt (fun t : ℝ => a + c * (t : ℂ)) c 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).const_add a
  simpa using h

private lemma coord_mem (j : Fin 4) (w : InfinitePlace F) :
    (fun v : V4 F => ((TR.pInf F (v j) w : ℝ) : ℂ)) ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) :=
  Algebra.subset_adjoin ⟨j, w, rfl⟩

private lemma poly_der (w : InfinitePlace F) (i : Fin 4) {p : V4 F → ℂ}
    (hp : p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F)) :
    ∃ p' ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v,
      HasDerivAt (fun t : ℝ => p (v + Pi.single i (Fo.at1 w t))) (p' v) 0 := by
  unfold UpperTheory.ConvolutionTheory.R2.polyFn at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, w', rfl⟩ := hx
    refine ⟨algebraMap ℂ _ (if j = i ∧ w' = w then 1 else 0), Subalgebra.algebraMap_mem _ _, fun v => ?_⟩
    have e : (fun t : ℝ => ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ)) =
        fun t : ℝ => ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) :=
      funext fun t => coord_shift w w' i j v t
    rw [e]
    exact lin_der _ _
  | algebraMap r =>
    exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | mul x y hxa hya hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    refine ⟨x' * y + x * y', add_mem (mul_mem hxm hya) (mul_mem hxa hym), fun v => ?_⟩
    have h := (hx v).mul (hy v)
    simp only [shift_zero] at h
    exact h

private noncomputable def Qf (δ : F) (v : V4 F) : ℂ :=
  ((∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w : ℝ) : ℂ)

private lemma Qf_mem (δ : F) : Qf δ ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) := by
  have e : Qf δ = ∑ w, ((fun v : V4 F => ((TR.pInf F (v 0) w : ℝ) : ℂ)) ^ 2 +
      (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ^ 2 +
      algebraMap ℂ (V4 F → ℂ) 2 * ((fun v : V4 F => ((TR.pInf F (v 2) w : ℝ) : ℂ)) ^ 2 -
        algebraMap ℂ (V4 F → ℂ) ((TR.pInf F (rt δ) w : ℝ) : ℂ) *
          (fun v : V4 F => ((TR.pInf F (v 3) w : ℝ) : ℂ)) ^ 2)) := by
    funext v
    have h2 : ∀ x, TR.pInf F (2 : A F) x = 2 := fun x => by
      rw [map_ofNat]; rfl
    simp [Qf, Finset.sum_apply, map_add (f := _), map_mul, map_sub, map_pow, h2]
  rw [e]
  refine sum_mem fun w _ => ?_
  exact add_mem (add_mem (pow_mem (coord_mem 0 w) 2) (pow_mem (coord_mem 1 w) 2))
    (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (pow_mem (coord_mem 2 w) 2)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (coord_mem 3 w) 2))))

private lemma gauss_der (δ : F) (w : InfinitePlace F) (i : Fin 4) :
    ∃ q ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v, HasDerivAt
      (fun t : ℝ => UpperTheory.ConvolutionTheory.R2.gauss δ (v + Pi.single i (Fo.at1 w t)))
      (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v) 0 := by
  obtain ⟨q, hq, hd⟩ := poly_der w i (Qf_mem δ)
  refine ⟨algebraMap ℂ _ (-(Real.pi : ℂ)) * q, mul_mem (Subalgebra.algebraMap_mem _ _) hq, fun v => ?_⟩
  have h := ((hd v).const_mul (-(Real.pi : ℂ))).cexp
  simp only [shift_zero] at h
  exact h

private def Gen (δ : F) : Set (V4 F → ℂ) :=
  {φ : V4 F → ℂ | ∃ p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
    φ = fun v => p v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v)}

private lemma cw_coord_mul_mem_span_gen_of_mem (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    (fun v => Fo.cw w (v i) * f v) ∈ Submodule.span ℂ (Gen δ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨(fun v : V4 F => ((TR.pInf F (v i) w : ℝ) : ℂ)) * p,
      mul_mem (coord_mem i w) hp, g, hg, ?_⟩
    funext v
    simp [Fo.cw, mul_assoc]
  | zero =>
    have : (fun v : V4 F => Fo.cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
      funext v; simp
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun v : V4 F => Fo.cw w (v i) * (x + y) v) =
        (fun v => Fo.cw w (v i) * x v) + fun v => Fo.cw w (v i) * y v := by
      funext v; simp [mul_add]
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    have : (fun v : V4 F => Fo.cw w (v i) * (c • x) v) = c • fun v => Fo.cw w (v i) * x v := by
      funext v; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ hx

private lemma span_d (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    ∃ f' ∈ Submodule.span ℂ (Gen δ), ∀ v,
      HasDerivAt (fun t : ℝ => f (v + Pi.single i (Fo.at1 w t))) (f' v) 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    obtain ⟨p', hp', hdp⟩ := poly_der w i hp
    obtain ⟨q, hq, hdq⟩ := gauss_der δ w i
    refine ⟨fun v => (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v),
      Submodule.subset_span ⟨p' + p * q, add_mem hp' (mul_mem hp hq), g, hg, rfl⟩, fun v => ?_⟩
    have h := ((hdp v).mul (hdq v)).mul_const (g (finPartPi v))
    simp only [shift_zero] at h
    simp only [finPart_shift]
    have e : (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v) =
        (p' v * UpperTheory.ConvolutionTheory.R2.gauss δ v + p v * (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v)) * g (finPartPi v) := by
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    rw [e]
    exact h
  | zero => exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | smul c x _ hx =>
    obtain ⟨x', hxm, hx⟩ := hx
    exact ⟨c • x', Submodule.smul_mem _ _ hxm, fun v => (hx v).const_mul c⟩

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.opsFock :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), OpsFock D O := by
  intro F E _ _ _ _ _ _ _ D O w i φ hφ
  have hs : φ.1 ∈ Submodule.span ℂ (Gen D.δ) := hφ
  refine ⟨?_, ?_⟩
  · have e : (O.x w i φ).1 = fun v => Fo.cw w (v i) * φ.1 v := funext fun v => O.x_apply w i φ v
    change (O.x w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact cw_coord_mul_mem_span_gen_of_mem D.δ w i hs
  · obtain ⟨f', hf', hd⟩ := span_d D.δ w i hs
    have e : (O.d w i φ).1 = f' := funext fun v => (O.d_spec w i φ v).unique (hd v)
    change (O.d w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact hf'
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem ht_le {E : Type} [Field E] [NumberField E] (y : GL (Fin 2) (Cinf E)) :
    ‖toL y.val‖ ≤ GlobalTheory.CuspRep.height y ∧ ‖toL (y⁻¹).val‖ ≤ GlobalTheory.CuspRep.height y := by
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  refine ⟨?_, ?_⟩ <;> first | (unfold GlobalTheory.CuspRep.height; linarith) | fail "height"

private theorem norm_matrix_mul_le_two {E : Type} [Field E] [NumberField E]
    (x x' : Matrix (Fin 2) (Fin 2) (Cinf E)) : ‖toL (x * x')‖ ≤ 2 * ‖toL x‖ * ‖toL x'‖ := by
  have h0 : 0 ≤ 2 * ‖toL x‖ * ‖toL x'‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
    (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  have e1 : ∀ a b, ‖x a b w‖ ≤ ‖toL x‖ := fun a b =>
    (norm_le_pi_norm (x a b) w).trans ((norm_le_pi_norm (toL x a) b).trans (norm_le_pi_norm (toL x) a))
  have e2 : ∀ a b, ‖x' a b w‖ ≤ ‖toL x'‖ := fun a b =>
    (norm_le_pi_norm (x' a b) w).trans ((norm_le_pi_norm (toL x' a) b).trans (norm_le_pi_norm (toL x') a))
  have e : toL (x * x') i j w = x i 0 w * x' 0 j w + x i 1 w * x' 1 j w := by
    show (x * x') i j w = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  have p : ∀ k, ‖x i k w * x' k j w‖ ≤ ‖toL x‖ * ‖toL x'‖ := fun k => by
    rw [norm_mul]
    exact mul_le_mul (e1 _ _) (e2 _ _) (norm_nonneg _) (norm_nonneg _)
  have := norm_add_le (x i 0 w * x' 0 j w) (x i 1 w * x' 1 j w)
  linarith [p 0, p 1]

private theorem cont_toL {E : Type} [Field E] [NumberField E] :
    Continuous fun x : Matrix (Fin 2) (Fin 2) (Cinf E) => toL x :=
  continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j

theorem UpperTheory.ConvolutionTheory.R2.Ff.htLe :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], HtLe E := by
  intro E _ _ _
  refine ⟨?_, fun y => ⟨?_, ?_, fun y' => ?_⟩⟩
  · unfold Ht
    have c1 : Continuous fun y : GL (Fin 2) (Cinf E) => toL y.val := cont_toL.comp Units.continuous_val
    have c2 : Continuous fun y : GL (Fin 2) (Cinf E) => toL (y⁻¹).val :=
      cont_toL.comp (Units.continuous_val.comp continuous_inv)
    exact (continuous_const.add c1.norm).add c2.norm
  · have n1 := norm_nonneg (toL y.val)
    have n2 := norm_nonneg (toL (y⁻¹).val)
    unfold Ht
    linarith
  · have h := ht_le y
    have h1 := GlobalTheory.CuspRep.one_le_height y
    unfold Ht
    linarith [h.1, h.2]
  · have n1 := norm_nonneg (toL y.val)
    have n2 := norm_nonneg (toL (y⁻¹).val)
    have n3 := norm_nonneg (toL y'.val)
    have n4 := norm_nonneg (toL (y'⁻¹).val)
    have m1 := norm_matrix_mul_le_two y.val y'.val
    have m2 := norm_matrix_mul_le_two (y'⁻¹).val (y⁻¹).val
    have e1 : (y * y').val = y.val * y'.val := rfl
    have e2 : ((y * y')⁻¹).val = (y'⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
    unfold Ht
    rw [e1, e2]
    nlinarith [mul_nonneg n1 n3, mul_nonneg n1 n4, mul_nonneg n2 n3, mul_nonneg n2 n4]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.transl :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F), Transl W M := by
  intro F E _ _ _ _ _ _ _ D W M f φ h h₀
  have hnu : nu F (h * h₀) = nu F h * nu F h₀ := by
    simp only [nu, map_mul]
  unfold lift
  refine congrArg (fun u : G1 F → ℂ => ∫ g in M.D, u g ∂M.μ) (funext fun g => ?_)
  simp only [hnu, dM_mul, map_mul, Module.End.mul_apply, mul_assoc]
end
