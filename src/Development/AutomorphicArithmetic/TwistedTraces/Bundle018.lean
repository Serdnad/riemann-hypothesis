module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle004
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

open scoped InnerProductSpace

private theorem iw_scale {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure]
    (ν : Fin n → ℤ) (T : LL μ →L[ℂ] LL μ) (hT : IsOloc μ w m ((iwCoset w ν).indicator 1) T) :
    T = (((m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w))).toReal : ℝ) : ℂ) • Uiw μ w ν := by
  have hCO : CO (GLnLocal.iwahori (w.adicCompletion K) n) :=
    ⟨GLnLocal.isCompact_iwahori _ n, GLnLocal.isOpen_iwahori _ n⟩
  have h0 : m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) ≠ 0 :=
    (hCO.2.measure_pos m ⟨1, Subgroup.one_mem _⟩).ne'
  have ht : m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) ≠ ⊤ := hCO.1.measure_lt_top.ne
  obtain ⟨d, hd⟩ : ∃ d, d = (m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)))⁻¹ := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := hd ▸ ENNReal.inv_ne_zero.2 ht
  have hdt : d ≠ ⊤ := hd ▸ ENNReal.inv_ne_top.2 h0
  haveI : (d • m).IsHaarMeasure := Measure.IsHaarMeasure.smul m hd0 hdt
  have h1 : (d • m) (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) = 1 := by
    rw [Measure.smul_apply, hd, smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]
  have hop := UpperTheory.ConvolutionTheory.C.hopOloc K n μ w (d • m) (GLnLocal.iwahori (w.adicCompletion K) n)
    (Cartan.diagPow (w.adicCompletion K) n ν) hCO h1
  have hc : (m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨h0, ht⟩
  have hdc : d.toReal = ((m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w))).toReal)⁻¹ := by
    rw [hd, ENNReal.toReal_inv]
  ext1 v
  refine ext_inner_left ℂ fun u => ?_
  have e1 : ⟪u, Uiw μ w ν v⟫_ℂ = d.toReal • ∫ g, (iwCoset w ν).indicator 1 g * ⟪u, rhoL μ w g v⟫_ℂ ∂m := by
    have := hop u v
    rw [integral_smul_measure] at this
    exact this
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, e1, hT u v, hdc, Complex.real_smul, ← mul_assoc,
    Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hc), one_mul]

theorem UpperTheory.Uiw_pow_comp_eq_of_antitone :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)]
        (m : Measure (Gw n w)) [m.IsHaarMeasure] (e : Fin n → ℤ) (j : ℕ) (T T' : LL μ →L[ℂ] LL μ), Antitone e →
        IsOloc μ w m ((iwCoset w 0).indicator 1) T → IsOloc μ w m ((iwCoset w (j • e)).indicator 1) T' →
        (Uiw μ w e ^ j) ∘L T = T' := by
  intro K _ _ n μ _ w _ _ m _ e j T T' he hT hT'
  have h0 : prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion K) n)) = Uiw μ w 0 := by
    have := UpperTheory.ConvolutionTheory.C.uiwPow K n μ w e he 0
    rw [pow_zero, zero_smul] at this
    exact this
  have h1 := UpperTheory.ConvolutionTheory.C.uiwPow K n μ w e he j
  rw [iw_scale μ w m 0 T hT, iw_scale μ w m _ T' hT', ← h0, ← h1]
  ext1 v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open GroundTheory.Automorphic.AutomorphicForm

private theorem adelicSplit {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (u : AdelicGLn.FiniteAdelicGL K n) :
    ∃ (a : Gw n w) (h : AdelicGLn.FiniteAdelicGL K n), u = AdelicGLn.localEmbedding w a * h ∧
      ∀ g : Gw n w, AdelicGLn.localEmbedding w g * h = h * AdelicGLn.localEmbedding w g := by
  obtain ⟨-, h2, -, -, h5⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  refine ⟨finAt w (finEmb K n u), (AdelicGLn.localEmbedding w (finAt w (finEmb K n u)))⁻¹ * u, ?_, ?_⟩
  · rw [mul_inv_cancel_left]
  · refine h5 _ ?_
    have e : finAt w (finEmb K n (AdelicGLn.localEmbedding w (finAt w (finEmb K n u)))) *
        finAt w (finEmb K n ((AdelicGLn.localEmbedding w (finAt w (finEmb K n u)))⁻¹ * u)) =
        finAt w (finEmb K n u) := by
      rw [← finAt_mul, ← map_mul, mul_inv_cancel_left]
    rw [h2] at e
    exact mul_left_cancel (e.trans (mul_one _).symm)

private theorem eqv_translate {L G H S : Type} [Group L] [TopologicalSpace L] [Group G] [TopologicalSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S]
    (τ : Representation ℂ L S) (ρ : UnitaryRep L H) (π : UnitaryRep G H) (D : Submodule ℂ H) (hD : π.IsInvariant D)
    (j : L → G) (hρ : ∀ g v, ρ g v = π (j g) v) (c : G) (hc : ∀ g, c * j g = j g * c) (f : S →ₗ[ℂ] H) (hf : Eqv τ ρ D f)
    (a : L) (y : S) : π (c * j a) (f y) ∈ spanAll τ ρ D := by
  have hE : Eqv τ ρ D (((π c : H →L[ℂ] H) : H →ₗ[ℂ] H) ∘ₗ f) := by
    refine ⟨fun y => hD c _ (hf.mem y), fun g y => ?_⟩
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hf.map, hρ, hρ, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, hc g]
  have hx : π (c * j a) (f y) = (((π c : H →L[ℂ] H) : H →ₗ[ℂ] H) ∘ₗ f) (τ a y) := by
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hf.map, hρ, UnitaryRep.map_mul_apply]
  rw [hx]
  exact Submodule.subset_span ⟨_, hE, _, rfl⟩

private theorem exists_factor {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (x : normOneGL (K := K) (n := n)) :
    ∃ (c : normOneGL (K := K) (n := n)) (a : Gw n w), x = c * MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w a) ∧
      ∀ g : Gw n w, c * MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g) =
        MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g) * c := by
  obtain ⟨A, u, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj x
  obtain ⟨a, h, rfl, hc⟩ := adelicSplit w u
  refine ⟨archProj K n A * MultiplicityOne.finProj K n h, a, ?_, fun g => ?_⟩
  · rw [hc a, map_mul, mul_assoc]
  · rw [mul_assoc, ← map_mul, ← hc g, map_mul, ← mul_assoc, ← mul_assoc,
      MultiplicityOne.finProj_mul_archProj_comm]

private theorem dense_of_invariant {G H S L : Type} [Group G] [TopologicalSpace G] [Group L] [TopologicalSpace L]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S]
    (π : UnitaryRep G H) (W V : Submodule ℂ H) (hV : IsSummandOf π W V) (τ : Representation ℂ L S) (ρ : UnitaryRep L H)
    (f : S →ₗ[ℂ] H) (hf0 : f ≠ 0) (hf : Eqv τ ρ V f) (hinv : π.IsInvariant (spanAll τ ρ V)) :
    V ≤ (spanAll τ ρ V).topologicalClosure := by
  have hle : spanAll τ ρ V ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f', hf', x, rfl⟩
    exact hf'.mem x
  have hCle : (spanAll τ ρ V).topologicalClosure ≤ V :=
    Submodule.topologicalClosure_minimal _ hle hV.closed
  have hne : (spanAll τ ρ V).topologicalClosure ≠ ⊥ := by
    intro hbot
    apply hf0
    refine LinearMap.ext fun x => ?_
    have h1 : f x ∈ (spanAll τ ρ V).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, x, rfl⟩)
    rw [hbot] at h1
    simpa using h1
  rcases hV.irred _ hCle (Submodule.isClosed_topologicalClosure _) hinv.topologicalClosure with h | h
  · exact absurd h hne
  · exact h.ge

private theorem invariant_of_translate {L G H S : Type} [Group L] [TopologicalSpace L] [Group G] [TopologicalSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S]
    (τ : Representation ℂ L S) (ρ : UnitaryRep L H) (π : UnitaryRep G H) (D : Submodule ℂ H)
    (h : ∀ x f, Eqv τ ρ D f → ∀ y, π x (f y) ∈ spanAll τ ρ D) : π.IsInvariant (spanAll τ ρ D) := by
  intro x v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨f', hf', y, rfl⟩ := hv
    exact h x f' hf' y
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private theorem locU_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (g : Gw n w) (v : LL μ) :
    locU μ w g v = rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v := by
  rw [locU_apply]
  rfl

theorem UpperTheory.summand_le_closure_span_local_type_images :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)) (w : Pl K) (σ : SmIrr (Gw n w)), IsSummand μ V → Occurs μ V w σ → V ≤ (spanAll σ.ρ (locU μ w) V).topologicalClosure := by
  intro K _ _ n μ _ V w σ hV hO
  obtain ⟨f, hf0, hfm, hfe⟩ := hO
  have hf : Eqv σ.ρ (locU μ w) V f := ⟨hfm, fun g x => by rw [hfe, locU_apply]⟩
  refine dense_of_invariant (rightRegularRep (rationalGLOne (K := K) (n := n)) μ) (cuspidalL2 μ) V hV σ.ρ (locU μ w) f hf0 hf ?_
  refine invariant_of_translate σ.ρ (locU μ w) _ V fun x f' hf' y => ?_
  obtain ⟨c, a, rfl, hc⟩ := exists_factor w x
  exact eqv_translate σ.ρ (locU μ w) (rightRegularRep (rationalGLOne (K := K) (n := n)) μ) V (IsSummandOf.inv hV)
    (fun g => MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) (locU_eq μ w) c hc f' hf' a y
end
