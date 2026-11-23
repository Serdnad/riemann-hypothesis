module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AvgTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle007
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.FinTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigAdm
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical

theorem UpperTheory.exists_pos_const_prod_localHeckeOperators :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure],
      ∃ κ : ℝ, 0 < κ ∧ ∀ (a : TI K n) (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
        (mw : ∀ i, Measure (Gw n (w i))) (f : ∀ v : Pl K, Gw n v → ℂ) (T : Fin r → LL μ →L[ℂ] LL μ) (g : TG K n),
        Function.Injective w → (∀ i, (mw i).IsHaarMeasure ∧ mw i (GLnLocal.integralGL ((w i).adicCompletion K) n) = 1) →
        (∀ i, Test (f (w i))) →
        (∀ v, v ∉ Set.range w → f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v)).indicator 1) →
        (∀ i, IsOloc μ (w i) (mw i) (f (w i)) (T i)) → (∀ x, g x = PositivityTheory.Rg.Tf.Geo.avg (tensF (onInf a) f) x) →
        RR μ g = (κ : ℂ) • (Oinf μ ν a ∘L (List.ofFn T).prod ∘L prj (sphOff μ (Finset.univ.image w))) := by
  intro K _ _ n hn μ _ ν _
  obtain ⟨m, _, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  refine ⟨m.real (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)), ?_, ?_⟩
  · have ho := AdelicGLn.isOpen_integralFiniteGL K n
    have hc := AdelicGLn.isCompact_integralFiniteGL K n
    exact ENNReal.toReal_pos (ho.measure_pos m ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne
  intro a r w _ _ mw f T g hw hm ht hoff hT hg
  obtain ⟨e, he, -, hO⟩ := UpperTheory.ConvolutionTheory.Tf.finTens K n μ m r w hw f ht hoff
  have hge : g = tens a e := by
    obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.Tf.avgTens K n hn a e (fun g => a (infPart K n g) * e (finPart K n g)) (fun _ => rfl)
    have hΦ : tensF (onInf a) f = fun g => a (infPart K n g) * e (finPart K n g) := by
      funext g
      simp only [tensF, onInf]
      rw [h2 g, he (finPart K n g)]
      congr 1
    refine DFunLike.ext _ _ fun x => ?_
    rw [hg x, hΦ, h1 x]
  have hUS : ∀ h, h ∈ levOn (Finset.univ.image w) (fun _ => (⊥ : Subgroup _)) ↔
      h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) = 1 := by
    intro h
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    change (∀ v, finAt v (finEmb K n h) ∈ if v ∈ Finset.univ.image w then (⊥ : Subgroup _)
      else GLnLocal.integralGL (v.adicCompletion K) n) ↔ _
    constructor
    · intro H
      refine ⟨fun v => ?_, fun i => ?_⟩
      · have := H v
        split_ifs at this with hv
        · rw [Subgroup.mem_bot] at this
          change finAt v (finEmb K n h) ∈ _
          rw [this]
          exact one_mem _
        · exact this
      · have := H (w i)
        rw [if_pos (by simp)] at this
        exact Subgroup.mem_bot.1 this
    · rintro ⟨H1, H2⟩ v
      split_ifs with hv
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
        exact Subgroup.mem_bot.2 (H2 i)
      · exact H1 v
  have hfix : fixF μ (levOn (Finset.univ.image w) (fun _ => (⊥ : Subgroup _))) = sphOff μ (Finset.univ.image w) := by
    rw [UpperTheory.ConvolutionTheory.C.fixLev K n μ (Finset.univ.image w) (fun _ => ⊥)]
    have htop : ∀ v : Pl K, fixL μ v (⊥ : Subgroup (Gw n v)) = ⊤ := by
      intro v
      simp [fixL, fixF, rhoF, Subgroup.map_bot]
      rfl
    simp [htop]
  have hOf := hO mw (fun i => (hm i).1) (fun i => (hm i).2) T hT _ hUS
  rw [hfix] at hOf
  rw [hge, UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ ν m hC a e, hOf, ContinuousLinearMap.comp_smul]
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical

theorem UpperTheory.finiteDimensional_eigenspace_inf_fixed_compactOpen :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (V : Submodule ℂ (LL μ)) (a : TI K n) (x : ℝ) (r : ℕ) (w : Fin r → Pl K), IsSummand μ V → x ≠ 0 → Function.Injective w →
        ∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) →
          FiniteDimensional ℂ ↥((eigIn V (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w)) ⊓ ⨅ i, fixL μ (w i) (U i)) := by
  intro K _ _ n hn μ _ ν _ V a x r w hV hx hw U hCO
  let U' : ∀ v : Pl K, Subgroup (Gw n v) := fun v =>
    if h : ∃ i, w i = v then h.choose_spec ▸ U h.choose else ⊥
  have hU' : ∀ i, U' (w i) = U i := by
    intro i
    have h : ∃ j, w j = w i := ⟨i, rfl⟩
    have key : ∀ (j : Fin r) (e : w j = w i), (e ▸ U j : Subgroup (Gw n (w i))) = U i := by
      intro j e
      obtain rfl := hw e
      rfl
    simp only [U', dif_pos h]
    exact key _ _
  have hCO' : ∀ v ∈ Finset.univ.image w, CO (U' v) := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    rw [hU']
    exact hCO i
  have hfin := UpperTheory.ConvolutionTheory.C.eigAdm K n hn μ ν a x hx (Finset.univ.image w) U' hCO'
  have hVc : V ≤ cuspidalL2 μ := hV.le
  have hle : (eigIn V (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w)) ⊓ ⨅ i, fixL μ (w i) (U i) ≤
      eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w) ⊓
        ⨅ v ∈ Finset.univ.image w, fixL μ v (U' v) := by
    intro u hu
    obtain ⟨⟨he, hs⟩, hf⟩ := hu
    refine ⟨⟨?_, hs⟩, ?_⟩
    · have hmem : ∀ (W : Submodule ℂ (LL μ)) (y : LL μ), y ∈ eigIn W (Oinf μ ν a) x ↔ y ∈ W ∧ Oinf μ ν a y = (x : ℂ) • y := by
        intro W y
        simp [eigIn, Module.End.mem_eigenspace_iff]
      have he' := (hmem V u).1 he
      exact (hmem _ u).2 ⟨hVc he'.1, he'.2⟩
    · have hf' : u ∈ ⨅ i, fixL μ (w i) (U i) := hf
      rw [Submodule.mem_iInf] at hf'
      change u ∈ ⨅ v ∈ Finset.univ.image w, fixL μ v (U' v)
      simp only [Submodule.mem_iInf]
      intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hU']
      exact hf' i
  haveI := hfin
  exact Submodule.finiteDimensional_of_le hle
end
