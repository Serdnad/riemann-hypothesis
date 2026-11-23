module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem infPartPi_add' {F : Type} [Field F] [NumberField F] (x y : V4 F) :
    infPartPi (x + y) = infPartPi x + infPartPi y := by
  funext j
  simp only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x j).1 (y j).1

private theorem placeEmbedReal_add {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (s t : ℝ) :
    at1 w (s + t) = at1 w s + at1 w t := by
  simp only [at1, Pi.single_add, map_add (f := _)]

private theorem continuous_placeEmbedReal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) :
    Continuous (at1 w : ℝ → A F) := by
  have h : Continuous fun t : ℝ => (Pi.single w t : TR.Rinf F) := by
    refine continuous_pi fun u => ?_
    by_cases hu : u = w
    · subst hu; simp only [Pi.single_eq_same]; exact continuous_id
    · simpa [Pi.single_eq_of_ne hu] using continuous_const
  exact ((TR.continuous_infEq F).comp h).prodMk continuous_const

private theorem inf_line {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4)
    (v : V4 F) (t : ℝ) :
    infPartPi (v + Pi.single i (at1 w t)) = infPartPi v + t • infPartPi (Pi.single i (at1 w 1) : V4 F) := by
  let L : ℝ →+ (Fin 4 → mixedEmbedding.mixedSpace F) :=
    { toFun := fun t => infPartPi (Pi.single i (at1 w t) : V4 F)
      map_zero' := by
        have h0 : at1 w (0 : ℝ) = (0 : A F) := by simp [at1]
        rw [h0, Pi.single_zero]
        funext j
        simp only [infPartPi, Pi.zero_apply, homeomorphMixedSpace_apply]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_add' := fun s t => by
        rw [placeEmbedReal_add, Pi.single_add, infPartPi_add'] }
  have hL : Continuous L := by
    refine continuous_infPartPi.comp (continuous_pi fun j => ?_)
    by_cases hj : j = i
    · subst hj; simpa using continuous_placeEmbedReal w
    · simpa [Pi.single_eq_of_ne hj] using continuous_const
  have h := map_real_smul L hL t (1 : ℝ)
  rw [infPartPi_add']
  have e : t • (1 : ℝ) = t := by simp
  rw [e] at h
  exact congrArg (infPartPi v + ·) h

private theorem fin_line {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4)
    (v : V4 F) (t : ℝ) : finPartPi (v + Pi.single i (at1 w t)) = finPartPi v := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [finPartPi, Pi.add_apply, Pi.single_eq_same]
    change (v j).2 + 0 = (v j).2
    exact add_zero _
  · simp [finPartPi, Pi.single_eq_of_ne hj]

theorem UpperTheory.ConvolutionTheory.R2.Fo.dEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) →
    ∃ φ' ∈ schwartzBruhatPi (K := F) (ι := Fin 4), ∀ v, HasDerivAt (fun t : ℝ => φ (v + Pi.single i (at1 w t))) (φ' v) 0 := by
  intro F _ _ _ w i φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    set e := infPartPi (Pi.single i (at1 w 1) : V4 F) with he
    refine ⟨schwartzBruhatTensorPi (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (Fin 4 → mixedEmbedding.mixedSpace F) ℂ) e f) g,
      schwartzBruhatTensorPi_mem _ hg, fun v => ?_⟩
    have hfun : (fun t : ℝ => schwartzBruhatTensorPi f g (v + Pi.single i (at1 w t))) =
        fun t : ℝ => f (infPartPi v + t • e) * g (finPartPi v) := by
      funext t
      simp only [schwartzBruhatTensorPi, inf_line, fin_line, he]
    rw [hfun]
    have hline : HasDerivAt (fun t : ℝ => infPartPi v + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add (infPartPi v)
    have hf : HasFDerivAt (f : (Fin 4 → mixedEmbedding.mixedSpace F) → ℂ) (fderiv ℝ f (infPartPi v))
        (infPartPi v + (0 : ℝ) • e) :=
      by
        rw [zero_smul, add_zero]
        exact (f.differentiableAt).hasFDerivAt
    have hc := (hf.comp_hasDerivAt (0 : ℝ) hline).mul_const (g (finPartPi v))
    simpa [schwartzBruhatTensorPi, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hc
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun v => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add G H _ _ hG hH =>
    obtain ⟨a, ha, ha'⟩ := hG
    obtain ⟨b, hb, hb'⟩ := hH
    exact ⟨a + b, Submodule.add_mem _ ha hb, fun v => (ha' v).add (hb' v)⟩
  | smul c G _ hG =>
    obtain ⟨a, ha, ha'⟩ := hG
    exact ⟨c • a, Submodule.smul_mem _ c ha, fun v => (ha' v).const_mul c⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Fo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

private theorem continuous_coordE (τ : E →+* ℂ) : Continuous (coord τ) :=
  AddMonoidHomClass.continuous_of_bound (coord τ) 1 fun x => by
    simpa using FieldIso.norm_coord_le τ x

private theorem continuous_infEqE_symm : Continuous (GlobalTheory.CuspRep.infEq E).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)

private theorem continuous_infEqF_symm : Continuous (TR.infEq F).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem cw_rt (w : InfinitePlace F) (k : F) :
    cw w (rt k) = w.embedding k := by
  have h : TR.pInf F (rt k) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) k := by
    change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
      ((algebraMap F (A F) k).1 w) = _
    rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) (WithAbs.toAbs _ k)
  rw [cw, h, InfinitePlace.embedding_of_isReal_apply]

private theorem embedding_pl (τ : E →+* ℂ) (k : F) :
    (pl F τ).embedding k = τ (algebraMap F E k) := by
  have h : (pl F τ).IsReal := IsTotallyReal.isReal _
  have h' := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 h)
  exact RingHom.congr_fun h' k

private theorem cw_rt_pl (τ : E →+* ℂ) (k : F) : cw (pl F τ) (rt k) = τ (algebraMap F E k) := by
  rw [cw_rt, embedding_pl]

private theorem coord_adeleMap (τ : E →+* ℂ) (a : A F) :
    coord τ (pInf E (AdeleBaseChange.adeleMap F E a)) = cw (pl F τ) a := by
  have key : (fun b : InfiniteAdeleRing F =>
        coord τ ((GlobalTheory.CuspRep.infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) b))) =
      fun b => (((TR.infEq F).symm b (pl F τ) : ℝ) : ℂ) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      ((continuous_coordE τ).comp (continuous_infEqE_symm.comp
        GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap))
      (Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_infEqF_symm)) (funext fun k => ?_)
    have h1 := cw_rt_pl (E := E) τ k
    have h2 := coord_algebraMap τ (algebraMap F E k)
    simp only [Function.comp_apply]
    rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap]
    exact h2.trans h1.symm
  exact congrFun key a.1

end UpperTheory.ConvolutionTheory.R2.Fo

open UpperTheory.ConvolutionTheory.R2.Fo in
theorem UpperTheory.ConvolutionTheory.R2.Fo.coordMk :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), (∀ (τ : E →+* ℂ) u t, coord τ (pInf E (D.mkE u t)) = cw (pl F τ) u + τ D.θ * cw (pl F τ) t) ∧
    (∀ τ : E →+* ℂ, τ D.θ ^ 2 = cw (pl F τ) (rt D.δ) ∧ starRingEnd ℂ (τ D.θ) = -τ D.θ ∧ τ D.θ ≠ 0) ∧
    (∀ w, cw w (rt D.δ) ≠ 0) ∧ ∀ w, ∃ τ : E →+* ℂ, pl F τ = w := by
  intro F E _ _ _ _ _ _ _ D
  have hneg : ∀ w : InfinitePlace F, ∃ r : ℝ, r < 0 ∧ cw w (rt D.δ) = r := fun w =>
    ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) D.δ, D.neg _, by
      rw [cw_rt, InfinitePlace.embedding_of_isReal_apply]⟩
  have hsq : ∀ τ : E →+* ℂ, τ D.θ ^ 2 = cw (pl F τ) (rt D.δ) := fun τ => by
    rw [cw_rt_pl, ← map_pow, D.sq]
  refine ⟨fun τ u t => ?_, fun τ => ⟨hsq τ, ?_, ?_⟩, fun w => ?_, fun w => ?_⟩
  · rw [Dat.mkE, map_add (f := _), map_add (f := _), map_mul, map_mul, coord_adeleMap, coord_adeleMap, coord_algebraMap, mul_comm (cw _ t)]
  · obtain ⟨r, hr, e⟩ := hneg (pl F τ)
    have h := (hsq τ).trans e
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
    have h0 : (τ D.θ).re = 0 := by
      by_contra hc
      have : (τ D.θ).im = 0 := by
        have : (τ D.θ).re * (τ D.θ).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hc
      rw [this] at hre
      nlinarith [mul_self_nonneg (τ D.θ).re]
    apply Complex.ext <;> simp [h0]
  · intro h0
    obtain ⟨r, hr, e⟩ := hneg (pl F τ)
    have h := (hsq τ).trans e
    rw [h0] at h
    have : (r : ℂ) = 0 := by simpa using h.symm
    exact hr.ne (by exact_mod_cast this)
  · obtain ⟨r, hr, e⟩ := hneg w
    rw [e]
    exact_mod_cast hr.ne
  · obtain ⟨W, hW⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
    refine ⟨W.embedding, ?_⟩
    rw [← hW]
    change InfinitePlace.mk (W.embedding.comp (algebraMap F E)) = W.comap (algebraMap F E)
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]

end
end
