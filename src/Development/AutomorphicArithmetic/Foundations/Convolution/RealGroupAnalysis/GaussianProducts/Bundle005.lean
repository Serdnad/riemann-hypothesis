module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle004
public import GroundTheory.GlobalFields.TateThesis.Bundle001
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle005
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.LocalFields.PadicLogSeries
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
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private noncomputable def scaleEquiv (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) (hc : ∀ p, c p ≠ 0) :
    (Fin 4 → NumberField.mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin 4 × InfinitePlace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => WithLp.toLp 2 fun p => c p * (x p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩
      map_add' := fun x y => by ext p; simp [mul_add]
      map_smul' := fun a x => by ext p; simp; ring
      invFun := fun y i => (fun w => (c (i, w.1))⁻¹ * y (i, w.1), fun _ => 0)
      left_inv := fun x => by
        funext i
        refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
        · simp [hc]
        · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)
      right_inv := fun y => by ext p; simp [hc] }

private theorem coord_infPart {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (v : Fin 4 → A F) (i : Fin 4) (w : InfinitePlace F) :
    (infPartPi v i).1 ⟨w, IsTotallyReal.isReal w⟩ = TR.pInf F (v i) w := by
  simp only [infPartPi, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  change _ = InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((v i).1 w)
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]

private theorem poly_temperate {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {p : V4 F → ℂ} (hp : p ∈ polyFn (F := F)) :
    ∃ f : (Fin 4 → NumberField.mixedEmbedding.mixedSpace F) → ℂ, f.HasTemperateGrowth ∧
      ∀ X, p X = f (infPartPi X) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨i, w, rfl⟩ := hp
    let l : (Fin 4 → NumberField.mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsReal} => ℝ)
        ⟨w, IsTotallyReal.isReal w⟩).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.proj (R := ℝ) i))
    refine ⟨fun x => ((l x : ℝ) : ℂ), Complex.ofRealCLM.hasTemperateGrowth.comp l.hasTemperateGrowth, fun X => ?_⟩
    change _ = (((infPartPi X i).1 ⟨w, IsTotallyReal.isReal w⟩ : ℝ) : ℂ)
    rw [coord_infPart]
  | algebraMap r =>
    exact ⟨fun _ => r, Function.HasTemperateGrowth.const r, fun X => rfl⟩
  | add p q _ _ hp hq =>
    obtain ⟨f, hf, hfp⟩ := hp
    obtain ⟨g, hg, hgq⟩ := hq
    exact ⟨fun x => f x + g x, hf.add hg, fun X => by simp [hfp, hgq]⟩
  | mul p q _ _ hp hq =>
    obtain ⟨f, hf, hfp⟩ := hp
    obtain ⟨g, hg, hgq⟩ := hq
    exact ⟨fun x => f x * g x, hf.mul hg, fun X => by simp [hfp, hgq]⟩

private theorem gauss_schwartz {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ φ : F →+* ℝ, φ δ < 0) {t : ℝ} (ht : 0 < t) :
    ∃ s : SchwartzMap (Fin 4 → NumberField.mixedEmbedding.mixedSpace F) ℂ,
      ∀ X, Complex.exp (-(t : ℂ) * (qInf δ X : ℝ)) = s (infPartPi X) := by
  let a : Fin 4 × InfinitePlace F → ℝ := fun p =>
    t / Real.pi * ![1, 1, 2, -2 * InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal p.2) δ] p.1
  have htp : 0 < t / Real.pi := div_pos ht Real.pi_pos
  have ha : ∀ p, 0 < a p := by
    rintro ⟨i, w⟩
    have := hδ (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    refine mul_pos htp ?_
    fin_cases i <;> simp <;> linarith
  have hc : ∀ p, √(a p) ≠ 0 := fun p => (Real.sqrt_pos.2 (ha p)).ne'
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv F (fun p => √(a p)) hc)
      (gaussianSchwartz (EuclideanSpace ℝ (Fin 4 × InfinitePlace F))), fun X => ?_⟩
  have hn : ‖scaleEquiv F (fun p => √(a p)) hc (infPartPi X)‖ ^ 2 = t / Real.pi * qInf δ X := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm, qInf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h : ∀ i, (scaleEquiv F (fun p => √(a p)) hc (infPartPi X)) (i, w) ^ 2 = a (i, w) * TR.pInf F (X i) w ^ 2 := by
      intro i
      change (√(a (i, w)) * (infPartPi X i).1 ⟨w, IsTotallyReal.isReal w⟩) ^ 2 = _
      rw [coord_infPart, mul_pow, Real.sq_sqrt (ha _).le]
    have hd : TR.pInf F (rt δ) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ :=
      congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap F δ) w
    simp only [Fin.sum_univ_four, h, map_add (f := _), map_mul, map_pow, map_sub, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, map_ofNat, Pi.ofNat_apply, hd]
    simp [a]
    ring
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply, hn]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have he : -Real.pi * (t / Real.pi * qInf δ X) = -t * qInf δ X := by
    field_simp
  rw [he]
  push_cast
  rfl

theorem UpperTheory.ConvolutionTheory.R2.G.pgMem :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ e : F →+* ℝ, e δ < 0) → ∀ t : ℝ, 0 < t → ∀ p ∈ polyFn (F := F), ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
    (fun v => p v * Complex.exp (-(t : ℂ) * (qInf δ v : ℝ)) * g (finPartPi v)) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  intro F _ _ _ δ hδ t ht p hp g hg
  obtain ⟨f, hf, hfp⟩ := poly_temperate hp
  obtain ⟨s, hs⟩ := gauss_schwartz δ hδ ht
  have h := schwartzBruhatTensorPi_mem (SchwartzMap.smulLeftCLM ℂ f s) hg
  convert h using 1
  funext v
  simp only [schwartzBruhatTensorPi, SchwartzMap.smulLeftCLM_apply_apply hf, smul_eq_mul]
  rw [hfp v, hs v]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors


open GroundTheory.Automorphic.FourierWhittaker in
private noncomputable def latE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) :
    vecLattice F (Fin 2) ≃ AdeleRing.principalSubgroup (𝓞 E) E where
  toFun g := ⟨D.coE.symm g.1, by
    obtain ⟨_, ξ, rfl⟩ := g
    refine ⟨algebraMap F E (ξ 0) + algebraMap F E (ξ 1) * D.θ, ?_⟩
    exact (D.mkE_rt (ξ 0) (ξ 1)).symm⟩
  invFun y := ⟨D.coE y.1, by
    obtain ⟨_, z, rfl⟩ := y
    exact mem_vecLattice.2 ⟨fun i => D.b.repr z i, funext fun i => (D.co_rt z i).symm⟩⟩
  left_inv g := Subtype.ext (D.coE.apply_symm_apply g.1)
  right_inv y := Subtype.ext (D.coE.symm_apply_apply y.1)

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.ConvolutionTheory.R2.G.cuspE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (Φ : GL (Fin 2) (A E) → ℂ), (∀ γ h, Φ (ratGL E 2 γ * h) = Φ h) →
    (∀ h, ∫ u in FS2 F, Φ (nE D u * h) ∂(adeleMeasurePi F) = 0) → GlobalTheory.CuspRep.IsCuspidal Φ := by
  intro F E _ _ _ _ _ D Φ hl h0
  refine cuspOf E Φ hl fun h => ?_
  let β : (Fin 2 → A F) ≃ₜ+ A E := D.coE.symm
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (adeleMeasurePi F (ι := Fin 2)).IsAddHaarMeasure := inferInstanceAs (Measure.pi fun _ : Fin 2 => adeleMeasure F).IsAddHaarMeasure
  haveI : ((adeleMeasurePi F (ι := Fin 2)).map m).IsAddHaarMeasure := β.isAddHaarMeasure_map (adeleMeasurePi F)
  have hF : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 F) ((adeleMeasurePi F (ι := Fin 2)).map m) :=
    (isAddFundamentalDomain_vecDomain (K := F) (ι := Fin 2)).image_of_equiv m.toEquiv
      (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving (latE D).symm
      fun y x => by
        change β (D.coE y.1 + x) = y.1 + β x
        rw [map_add (f := _)]
        congr 1
        exact D.coE.symm_apply_apply y.1
  have hF' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 F) (adeleMeasure E) :=
    hF.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hper : ∀ (g : AdeleRing.principalSubgroup (𝓞 E) E) (x : A E),
      Φ (gl (nU (g +ᵥ x)) * h) = Φ (gl (nU x) * h) := by
    rintro ⟨_, k, rfl⟩ x
    obtain ⟨γ, hγ⟩ := Pp.rat_n k
    change Φ (gl (nU (rt k + x)) * h) = _
    rw [Pp.n_add, ← hγ, mul_assoc, hl]
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 E) E) := (latE D).symm.injective.countable
  have h1 := (isAddFundamentalDomain_fundamentalSet E).setIntegral_eq hF' (f := fun x => Φ (gl (nU x) * h)) hper
  rw [h1, Measure.isAddLeftInvariant_eq_smul (adeleMeasure E) ((adeleMeasurePi F (ι := Fin 2)).map m), Measure.restrict_smul,
    integral_smul_nnreal_measure, m.measurableEmbedding.setIntegral_map, m.injective.preimage_image]
  have h3 : ∫ u in FS2 F, Φ (gl (nU (m u)) * h) ∂(adeleMeasurePi F) = 0 := h0 h
  rw [h3, smul_zero]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem td_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

private theorem td_fin (F : Type) [Field F] [NumberField F] :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) :=
    fun v => td_adic v
  refine ⟨isTotallyDisconnected_of_image (f := fun (x : FiniteAdeleRing (𝓞 F) F) v => x v)
    (continuous_pi fun v => RestrictedProduct.continuous_eval v).continuousOn
    (fun x y h => Subtype.ext (funext fun v => congrFun h v))
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem basis_fin (F : Type) [Field F] [NumberField F] :
    TopologicalSpace.IsTopologicalBasis
      {T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) | IsCompact T ∧ IsOpen T} := by
  haveI := td_fin F
  have hb : TopologicalSpace.IsTopologicalBasis
      {s : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun T hT => hT.2) ?_
  intro x U hx hU
  obtain ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCU⟩ := hb.exists_subset_of_mem_open hxK isOpen_interior
  exact ⟨C, ⟨hKc.of_isClosed_subset hC.isClosed (hCU.trans interior_subset), hC.isOpen⟩, hxC,
    hCU.trans (interior_subset.trans hKU)⟩

section
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

private theorem cont_symm : Continuous (TR.infEq F).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem cont_pInf : Continuous (TR.pInf F) := (cont_symm F).comp continuous_fst

private noncomputable def xc (v : Fin 2 → A F) : Fin 2 × InfinitePlace F → ℝ := fun p => TR.pInf F (v p.1) p.2

private noncomputable def ec (y : (Fin 2 × InfinitePlace F → ℝ) × (Fin 2 → FiniteAdeleRing (𝓞 F) F)) :
    Fin 2 → A F :=
  fun i => ((TR.infEq F (fun w => y.1 (i, w)), y.2 i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

private theorem cont_xc : Continuous (xc F) :=
  continuous_pi fun p => (continuous_apply p.2).comp ((cont_pInf F).comp (continuous_apply p.1))

private theorem cont_fin : Continuous (finPartPi : (Fin 2 → A F) → Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

private theorem cont_ec : Continuous (ec F) := by
  refine continuous_pi fun i => ?_
  exact ((TR.continuous_infEq F).comp (continuous_pi fun w =>
    (continuous_apply (i, w)).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

private theorem ec_xc (v : Fin 2 → A F) : ec F (xc F v, finPartPi v) = v := by
  funext i
  refine TR.ad_ext ?_ rfl
  exact (TR.infEq F).symm_apply_apply _

private theorem poly_mem (t : Fin 2 × InfinitePlace F → ℝ) (n : ℕ) :
    (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ) ^ n) ∈ polyOn F (Fin 2) := by
  have h : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ))
      = ∑ p, (t p : ℂ) • (fun v : Fin 2 → A F => ((TR.pInf F (v p.1) p.2 : ℝ) : ℂ)) := by
    funext v
    simp [Finset.sum_apply, xc]
  have h1 : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ)) ∈ polyOn F (Fin 2) := by
    rw [h]
    refine Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ ?_ _
    exact Algebra.subset_adjoin (show _ ∈ {g : (Fin 2 → A F) → ℂ | ∃ i w, g = fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)} from ⟨p.1, p.2, rfl⟩)
  exact Subalgebra.pow_mem _ h1 n

private theorem sum_xc (v : Fin 2 → A F) : ∑ p, |xc F v p| = sz v := by
  rw [Fintype.sum_prod_type]; rfl

end

theorem UpperTheory.ConvolutionTheory.R2.G.momAdel :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : Ω → Fin 2 → A F) (ρ : Ω → ℂ), Measurable r →
    (∀ R : ℝ, Integrable (fun ω => ((Real.exp (R * sz (r ω)) : ℝ) : ℂ) * ρ ω) ν) →
    (∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T → ∫ ω, p (r ω) * T.indicator 1 (finPartPi (r ω)) * ρ ω ∂ν = 0) →
    ∀ q : (Fin 2 → A F) → ℂ, Measurable q → (∀ x, ‖q x‖ ≤ 1) → ∫ ω, q (r ω) * ρ ω ∂ν = 0 := by
  intro F _ _ _ Ω _ ν r ρ hr hint hmom q hq hq1
  have hρ : Integrable ρ ν := by simpa using hint 0
  have hX : Measurable fun ω => xc F (r ω) := (cont_xc F).measurable.comp hr
  have hs : Measurable fun ω => (finPartPi (r ω) : Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
    (cont_fin F).measurable.comp hr
  have hT : ∀ (T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)) (S : Set (Fin 2 × InfinitePlace F → ℝ)),
      MeasurableSet S → IsCompact T → IsOpen T →
      ∫ ω, S.indicator 1 (xc F (r ω)) * (T.indicator 1 (finPartPi (r ω)) * ρ ω) ∂ν = 0 := by
    intro T S hS hTc hTo
    have hi : Measurable fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) :=
      (measurable_one.indicator hTo.measurableSet).comp hs
    have hib : ∀ ω, ‖T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω))‖ ≤ 1 := by
      intro ω
      by_cases h : finPartPi (r ω) ∈ T <;> simp [h]
    have hI : ∀ g : Ω → ℂ, Integrable g ν →
        Integrable (fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) * g ω) ν :=
      fun g hg => hg.bdd_mul hi.aestronglyMeasurable (Eventually.of_forall hib)
    refine charZero Ω _ ν _ _ hX (hI ρ hρ) ?_ S hS
    refine momChar Ω _ ν _ _ hX (fun R => ?_) (fun n t => ?_)
    · simp only [sum_xc]
      refine (hI _ (hint R)).congr (Eventually.of_forall fun ω => ?_)
      simp only
      ring
    · have := hmom _ (poly_mem F t n) T hTc hTo
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      ring
  have hQ : Measurable fun y => q (ec F y) := hq.comp (cont_ec F).measurable
  have := prodExt Ω _ _ ν (fun ω => xc F (r ω)) (fun ω => finPartPi (r ω)) ρ (basis_fin F) hX hs hρ
    (fun S T hS hTc hTo => hT T S hS hTc hTo) _ hQ (fun y => hq1 _)
  simpa only [ec_xc] using this
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors


open scoped Pointwise in
private theorem lint_add {F : Type} [Field F] [NumberField F] {h : A F → ℝ≥0∞}
    (hh : ∀ (k : F) x, h (rt k + x) = h x) (a : A F) :
    ∫⁻ b in fundamentalSet F, h (b + a) ∂(adeleMeasure F) = ∫⁻ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  have hD := isAddFundamentalDomain_fundamentalSet F
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
    refine (Set.countable_range (fun ξ : F => (rt ξ : A F))).mono ?_ |>.to_subtype
    rintro _ ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩
  have hT := hD.vadd_of_comm a
  have hp := measurePreserving_add_right (adeleMeasure F) a
  have e : (fun b : A F => b + a) ⁻¹' (a +ᵥ fundamentalSet F) = fundamentalSet F := by
    ext x
    simp [Set.mem_vadd_set, add_comm]
  have h1 := hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight a).measurableEmbedding h (a +ᵥ fundamentalSet F)
  rw [e] at h1
  rw [h1]
  refine hT.setLIntegral_eq hD h ?_
  rintro ⟨_, k, rfl⟩ x
  exact hh k x

theorem UpperTheory.ConvolutionTheory.R2.G.lamRight :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (u : G1 F → ℂ), NInv u → ∀ (c : ℂ) (g₀ : G1 F), abelian₂ M (fun g => c * u (g * g₀)) = ‖c‖ₑ * abelian₂ M u := by
  intro F _ _ _ M₀ u hu c g₀
  have hnU : Measurable (nU : A F → G1 F) := M.continuous_nU.measurable
  set U : G1 F → ℝ≥0∞ := fun g => ∫⁻ b in fundamentalSet F, ‖u (nU b * g)‖ₑ ∂(adeleMeasure F) with hUdef
  have hUm : Measurable U :=
    Measurable.lintegral_prod_right' (ν := (adeleMeasure F).restrict (fundamentalSet F))
      (f := fun q : G1 F × A F => ‖u (nU q.2 * q.1)‖ₑ)
      (hu.1.comp ((hnU.comp measurable_snd).mul measurable_fst)).enorm
  have hUi : ∀ b g, U (nU b * g) = U g := by
    intro a g
    have := lint_add (F := F) (h := fun b => ‖u (nU b * g)‖ₑ) (fun k x => by
      simp only [M.nU_add, mul_assoc, hu.2]) a
    simp only [hUdef]
    rw [← this]
    simp only [M.nU_add, mul_assoc]
  have hc : ‖c‖ₑ ≠ ⊤ := enorm_ne_top
  have hJ := M.lintegral_unipotent_quotient_right_invariant F M₀ U hUm hUi g₀
  have hL : abelian₂ M₀ (fun g => c * u (g * g₀)) = ‖c‖ₑ * M.J0 M₀ (fun g => U (g * g₀)) := by
    simp only [abelian₂, M.J0]
    rw [← lintegral_const_mul' _ _ hc]
    refine lintegral_congr fun p => ?_
    have : ∫⁻ b in fundamentalSet F, ‖c * u (nU b * (mD p.1 * p.2) * g₀)‖ₑ ∂(adeleMeasure F) =
        ‖c‖ₑ * U (mD p.1 * p.2 * g₀) := by
      simp only [hUdef, enorm_mul, mul_assoc]
      exact lintegral_const_mul' _ _ hc
    rw [this]
    ring
  rw [hL, hJ]
  rfl
end
