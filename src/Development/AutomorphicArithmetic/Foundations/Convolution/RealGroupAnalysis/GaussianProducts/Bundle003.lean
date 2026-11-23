module

public import GroundTheory.AutomorphicForms.GL2.GJMatrixFinite
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle025
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
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FiniteFourierHat

variable {F : Type} [Field F] [NumberField F]

private theorem slice_mem {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) (v : Fin 4 → FiniteAdeleRing (𝓞 F) F) :
    (fun s => g (Function.update v 1 s)) ∈ finiteSchwartzBruhat F := by
  obtain ⟨hl, hc⟩ := hg
  have hcont : Continuous fun s : FiniteAdeleRing (𝓞 F) F => Function.update v 1 s :=
    continuous_const.update 1 continuous_id
  refine ⟨hl.comp_continuous hcont, ?_⟩
  refine HasCompactSupport.intro (hc.isCompact.image (continuous_apply 1)) fun s hs => ?_
  by_contra h
  exact hs ⟨Function.update v 1 s, subset_tsupport _ h, by simp⟩

private noncomputable def T (g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : Fin 4 → FiniteAdeleRing (𝓞 F) F) : ℂ :=
  finiteFourier F (fun s => g (Function.update v 1 s)) (-(v 1))

private theorem T_tensor (h : Fin 4 → FiniteAdeleRing (𝓞 F) F → ℂ) :
    T (finiteTensor h) =
      finiteTensor ![h 0, fun x => finiteFourier F (h 1) (-x), h 2, h 3] := by
  funext v
  have hs : ∀ s, finiteTensor h (Function.update v 1 s) * (finiteAdelicChar F (s * -(v 1)) : ℂ) =
      (h 0 (v 0) * h 2 (v 2) * h 3 (v 3)) * (h 1 s * (finiteAdelicChar F (s * -(v 1)) : ℂ)) := by
    intro s
    simp [finiteTensor, Fin.prod_univ_four, Function.update_apply]
    ring
  simp only [T, finiteFourier]
  simp_rw [hs]
  rw [integral_const_mul]
  simp [finiteTensor, Fin.prod_univ_four, finiteFourier]
  ring

private theorem neg_mem {f : FiniteAdeleRing (𝓞 F) F → ℂ} (hf : f ∈ finiteSchwartzBruhat F) :
    (fun x => f (-x)) ∈ finiteSchwartzBruhat F :=
  ⟨hf.1.comp_continuous continuous_neg, hf.2.comp_homeomorph (Homeomorph.neg _)⟩

private theorem T_mem {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    T g ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  have hsub := (finiteSchwartzBruhatPi_eq_span (K := F) (ι := Fin 4)).ge
  rw [finiteSchwartzBruhatPi_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨J, a⟩, rfl⟩ := hf
    rw [T_tensor]
    refine finiteTensor_mem fun i => ?_
    fin_cases i
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
    · exact neg_mem (finiteFourier_mem_finiteSchwartzBruhat
        (cosetIndicator_mem_finiteSchwartzBruhat J _))
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
  | zero =>
    have : T (0 : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by
      funext v
      simp [T, finiteFourier]
    rw [this]
    exact zero_mem _
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    have : T (f₁ + f₂) = T f₁ + T f₂ := by
      funext v
      exact congrFun (finiteFourier_add
        (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₁) v))
        (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₂) v))) _
    rw [this]
    exact add_mem ih₁ ih₂
  | smul c f _ ih =>
    have : T (c • f) = c • T f := by
      funext v
      simp only [T, finiteFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    rw [this]
    exact Submodule.smul_mem _ c ih

end UpperTheory.ConvolutionTheory.R2.G.FiniteFourierHat

theorem UpperTheory.ConvolutionTheory.R2.G.finHat :
    ∀ (F : Type) [Field F] [NumberField F], ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), (∀ v, Integrable (fun s => g (Function.update v 1 s)) (finiteAdeleMeasure F)) ∧
    (fun v => ∫ s, g (Function.update v 1 s) * ((finiteAdelicChar F (-(s * v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F)) ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  intro F _ _ g hg
  refine ⟨fun v => integrable_of_mem_finiteSchwartzBruhat (FiniteFourierHat.slice_mem hg v), ?_⟩
  have he : (fun v => ∫ s, g (Function.update v 1 s) * ((finiteAdelicChar F (-(s * v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F)) = FiniteFourierHat.T g := by
    funext v
    simp only [FiniteFourierHat.T, finiteFourier, mul_neg]
  rw [he]
  exact FiniteFourierHat.T_mem hg
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.prodExt :
    ∀ (Ω X Z : Type) [MeasurableSpace Ω] [MeasurableSpace X] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z] [T2Space Z] (ν : Measure Ω) (r : Ω → X) (s : Ω → Z) (ρ : Ω → ℂ),
    TopologicalSpace.IsTopologicalBasis {T : Set Z | IsCompact T ∧ IsOpen T} → Measurable r → Measurable s → Integrable ρ ν →
    (∀ (S : Set X) (T : Set Z), MeasurableSet S → IsCompact T → IsOpen T → ∫ ω, S.indicator 1 (r ω) * (T.indicator 1 (s ω) * ρ ω) ∂ν = 0) →
    ∀ Q : X × Z → ℂ, Measurable Q → (∀ x, ‖Q x‖ ≤ 1) → ∫ ω, Q (r ω, s ω) * ρ ω ∂ν = 0 := by
  intro Ω X Z _ _ _ _ _ _ _ ν r s ρ hB hr hs hρ H Q hQ hQ1
  have hφ : Measurable (fun ω => (r ω, s ω)) := hr.prodMk hs

  obtain ⟨e, he, heU⟩ : ∃ e : ℕ → Set Z, (∀ n, IsCompact (e n) ∧ IsOpen (e n)) ∧ ⋃ n, e n = Set.univ := by
    obtain ⟨T, hTc, hTs, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable
      {T : Set Z | IsCompact T ∧ IsOpen T} (fun t ht => ht.2)
    have hne : (insert ∅ T).Nonempty := Set.insert_nonempty _ _
    obtain ⟨e, he⟩ := (hTc.insert ∅).exists_eq_range hne
    refine ⟨e, fun n => ?_, ?_⟩
    · have hn : e n ∈ insert ∅ T := he ▸ Set.mem_range_self n
      rcases hn with hn | hn
      · rw [hn]; exact ⟨isCompact_empty, isOpen_empty⟩
      · exact hTs hn
    · rw [← Set.sUnion_range, ← he, Set.sUnion_insert, Set.empty_union, hTU, hB.sUnion_eq]

  have hmass : ∫ ω, ρ ω ∂ν = 0 := by
    have hF : ∀ n, ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν = 0 := by
      intro n
      have hc : IsCompact (Set.accumulate e n) := isCompact_accumulate (fun i => (he i).1) n
      have ho : IsOpen (Set.accumulate e n) := by
        rw [Set.accumulate_def]
        exact isOpen_iUnion (fun i => isOpen_iUnion (fun _ => (he i).2))
      have := H Set.univ (Set.accumulate e n) MeasurableSet.univ hc ho
      simpa using this
    have hlim : Tendsto (fun n => ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν)
        atTop (𝓝 (∫ ω, ρ ω ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
      · intro n
        have hm : MeasurableSet (Set.accumulate e n) :=
          (isCompact_accumulate (fun i => (he i).1) n).isClosed.measurableSet
        exact (((measurable_one.indicator hm).comp hs).aestronglyMeasurable).mul hρ.1
      · intro n
        refine Eventually.of_forall (fun ω => ?_)
        by_cases h : s ω ∈ Set.accumulate e n <;> simp [h]
      · refine Eventually.of_forall (fun ω => ?_)
        have hmem : s ω ∈ ⋃ n, e n := heU ▸ Set.mem_univ _
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hmem
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop n] with m hm
        have : s ω ∈ Set.accumulate e m := Set.mem_accumulate.2 ⟨n, hm, hn⟩
        simp [this]
    have := tendsto_nhds_unique hlim (by simp only [hF]; exact tendsto_const_nhds)
    exact this

  have hgen : (inferInstance : MeasurableSpace (X × Z)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
        {T : Set Z | IsCompact T ∧ IsOpen T}) := by
    have hD : IsCountablySpanning {T : Set Z | IsCompact T ∧ IsOpen T} := ⟨e, he, heU⟩
    have h1 : ‹MeasurableSpace Z› = MeasurableSpace.generateFrom {T : Set Z | IsCompact T ∧ IsOpen T} :=
      (BorelSpace.measurable_eq).trans hB.borel_eq_generateFrom
    have := generateFrom_prod_eq (isCountablySpanning_measurableSet (α := X)) hD
    rw [MeasurableSpace.generateFrom_measurableSet, ← h1] at this
    exact this
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
      {T : Set Z | IsCompact T ∧ IsOpen T}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod
      (fun a ha b hb _ => ⟨ha.1.inter hb.1, ha.2.inter hb.2⟩)
  have hset : ∀ A : Set (X × Z), MeasurableSet A → ∫ ω in (fun ω => (r ω, s ω)) ⁻¹' A, ρ ω ∂ν = 0 := by
    intro A hA
    induction A, hA using MeasurableSpace.induction_on_inter hgen hpi with
    | empty => simp
    | basic t ht =>
      obtain ⟨S, hS, T, hT, rfl⟩ := ht
      have hTm : MeasurableSet T := hT.2.measurableSet
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' (S ×ˢ T)) := hφ (hS.prod hTm)
      rw [← integral_indicator hm, ← H S T hS hT.1 hT.2]
      congr 1
      funext ω
      by_cases h1 : r ω ∈ S <;> by_cases h2 : s ω ∈ T <;> simp [Set.indicator, h1, h2]
    | compl t htm ih =>
      rw [Set.preimage_compl, setIntegral_compl (hφ htm) hρ, ih, hmass, sub_zero]
    | iUnion f hd hm ih =>
      rw [Set.preimage_iUnion, integral_iUnion (fun i => hφ (hm i))
        (fun i j hij => (hd hij).preimage _) hρ.integrableOn]
      simp [ih]

  have hint : ∀ (f : Ω → ℂ) (C : ℝ), Measurable f → (∀ ω, ‖f ω‖ ≤ C) →
      Integrable (fun ω => f ω * ρ ω) ν := fun f C hf hC =>
    hρ.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hC)
  have hsimple : ∀ g : SimpleFunc (X × Z) ℂ, ∫ ω, g (r ω, s ω) * ρ ω ∂ν = 0 := by
    intro g
    induction g using SimpleFunc.induction with
    | const c hA =>
      rename_i A
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' A) := hφ hA
      have h0 := hset A hA
      rw [← integral_indicator hm] at h0
      have : (fun ω => (SimpleFunc.piecewise A hA (SimpleFunc.const _ c) (SimpleFunc.const _ 0)) (r ω, s ω) * ρ ω)
          = fun ω => c * ((fun ω => (r ω, s ω)) ⁻¹' A).indicator ρ ω := by
        funext ω
        by_cases h : (r ω, s ω) ∈ A <;> simp [Set.indicator, h, Set.piecewise]
      rw [this, integral_const_mul, h0, mul_zero]
    | add hd hf hg =>
      rename_i f g
      obtain ⟨Cf, hCf⟩ := f.exists_forall_norm_le
      obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
      have hif := hint (fun ω => f (r ω, s ω)) Cf (f.measurable.comp hφ) (fun ω => hCf _)
      have hig := hint (fun ω => g (r ω, s ω)) Cg (g.measurable.comp hφ) (fun ω => hCg _)
      simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
      rw [integral_add hif hig, hf, hg, add_zero]

  have hSM : StronglyMeasurable Q := hQ.stronglyMeasurable
  have hlim : Tendsto (fun n => ∫ ω, hSM.approxBounded 1 n (r ω, s ω) * ρ ω ∂ν) atTop
      (𝓝 (∫ ω, Q (r ω, s ω) * ρ ω ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
    · intro n
      exact (((hSM.approxBounded 1 n).measurable.comp hφ).aestronglyMeasurable).mul hρ.1
    · intro n
      refine Eventually.of_forall (fun ω => ?_)
      rw [norm_mul]
      have := hSM.norm_approxBounded_le zero_le_one n (r ω, s ω)
      calc _ ≤ 1 * ‖ρ ω‖ := by gcongr
        _ = ‖ρ ω‖ := one_mul _
    · refine Eventually.of_forall (fun ω => ?_)
      exact (hSM.tendsto_approxBounded_of_norm_le (hQ1 _)).mul_const _
  exact tendsto_nhds_unique hlim (by simp only [hsimple]; exact tendsto_const_nhds)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.momChar :
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (X : Ω → ι → ℝ) (ρ : Ω → ℂ), Measurable X →
    (∀ R : ℝ, Integrable (fun ω => ((Real.exp (R * ∑ i, |X ω i|) : ℝ) : ℂ) * ρ ω) ν) →
    (∀ (n : ℕ) (t : ι → ℝ), ∫ ω, ((∑ i, t i * X ω i : ℝ) : ℂ) ^ n * ρ ω ∂ν = 0) →
    ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω ∂ν = 0 := by
  intro Ω ι _ _ ν X ρ hX hint hmom t
  have hym : Measurable (fun ω => ∑ i, t i * X ω i) :=
    Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp hX).const_mul (t i))
  have hρ : Integrable ρ ν := by simpa using hint 0
  have hbound : ∀ ω, |∑ i, t i * X ω i| ≤ (∑ i, |t i|) * ∑ i, |X ω i| := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => |X ω j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
      (abs_nonneg _)
  have hdom : Integrable (fun ω => Real.exp |∑ i, t i * X ω i| * ‖ρ ω‖) ν := by
    refine (hint (∑ i, |t i|)).norm.mono'
      (((Real.measurable_exp.comp (continuous_abs.measurable.comp hym)).aestronglyMeasurable).mul hρ.norm.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    simp only [norm_mul, norm_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [abs_norm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbound ω)) (norm_nonneg (ρ ω))
  have hsum := hasSum_integral_of_dominated_convergence (μ := ν)
    (F := fun (n : ℕ) ω => (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω)
    (f := fun ω => Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω)
    (fun (n : ℕ) ω => |∑ i, t i * X ω i| ^ n / (n.factorial : ℝ) * ‖ρ ω‖)
    (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · have hz : (fun n : ℕ => ∫ ω, (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω ∂ν)
        = fun _ => 0 := by
      funext n
      have : ∀ ω, (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω
          = (Complex.I ^ n / (n.factorial : ℂ)) * (((∑ i, t i * X ω i : ℝ) : ℂ) ^ n * ρ ω) := by
        intro ω; rw [mul_pow]; ring
      simp_rw [this]
      rw [integral_const_mul, hmom n t, mul_zero]
    rw [hz] at hsum
    exact hsum.unique hasSum_zero |>.symm ▸ rfl
  · have hc : Measurable (fun ω => ((∑ i, t i * X ω i : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hym
    exact ((((hc.mul_const Complex.I).pow_const n).div_const _).aestronglyMeasurable).mul hρ.aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_natCast, Real.norm_eq_abs]
  · exact Eventually.of_forall fun ω =>
      (Real.summable_pow_div_factorial _).mul_right _
  · have : (fun ω => ∑' n : ℕ, |∑ i, t i * X ω i| ^ n / (n.factorial : ℝ) * ‖ρ ω‖)
        = fun ω => Real.exp |∑ i, t i * X ω i| * ‖ρ ω‖ := by
      funext ω
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [this]; exact hdom
  · refine Eventually.of_forall fun ω => ?_
    have := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)).mul_right (ρ ω)
    rwa [← Complex.exp_eq_exp_ℂ] at this
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private lemma bdd_int {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (u g : Ω → ℂ)
    (hu : Measurable u) (hb : ∀ ω, ‖u ω‖ ≤ 1) (hg : Integrable g ν) :
    Integrable (fun ω => u ω * g ω) ν := by
  refine Integrable.mono' hg.norm (hu.aestronglyMeasurable.mul hg.1) (ae_of_all _ fun ω => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb ω)

private lemma real_diff {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hGb : ∀ x, ‖G x‖ ≤ 1) :
    ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X)
      - ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X)
      = ∫ ω, G (X ω) * (f ω : ℂ) ∂ν :=
  _root_.UpperTheory.Reformulated.B.Qh3.real_diff ν X f hX hf G hG hGb

private lemma real_case {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (h : ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (f ω : ℂ) ∂ν = 0)
    (S : Set (ι → ℝ)) (hS : MeasurableSet S) :
    ∫ ω, S.indicator 1 (X ω) * (f ω : ℂ) ∂ν = 0 := by
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (-f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hEq : (ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X
      = (ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X := by
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    rw [charFunDual_apply, charFunDual_apply]
    have key := real_diff ν X f hX hf (fun x => Complex.exp ((L x : ℂ) * Complex.I))
      (by fun_prop) (fun x => by rw [Complex.norm_exp_ofReal_mul_I])
    have h0 := h (fun i => L (fun j => if i = j then 1 else 0))
    have hL : ∀ x : ι → ℝ, L x = ∑ i, L (fun j => if i = j then 1 else 0) * x i := by
      intro x
      have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
      simpa [mul_comm] using this
    simp only [← hL] at h0
    rw [h0] at key
    exact sub_eq_zero.mp key
  have key := real_diff ν X f hX hf (S.indicator 1)
    (measurable_one.indicator hS) (fun x => by
      by_cases hx : x ∈ S <;> simp [hx])
  rw [hEq, sub_self] at key
  exact key.symm

theorem UpperTheory.ConvolutionTheory.R2.G.charZero :
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (X : Ω → ι → ℝ) (ρ : Ω → ℂ), Measurable X → Integrable ρ ν →
    (∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω ∂ν = 0) →
    ∀ S : Set (ι → ℝ), MeasurableSet S → ∫ ω, S.indicator 1 (X ω) * ρ ω ∂ν = 0 := by
  intro Ω ι _ _ ν X ρ hX hρ h S hS
  have hconjI : Integrable (fun ω => (starRingEnd ℂ) (ρ ω)) ν := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hρ
  have hE : ∀ t : ι → ℝ, Measurable fun ω =>
      Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) := by
    intro t
    have : ∀ i, Measurable fun ω => X ω i := fun i => (measurable_pi_apply i).comp hX
    fun_prop
  have hEb : ∀ (t : ι → ℝ) (ω : Ω),
      ‖Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro t ω
    rw [Complex.norm_exp_ofReal_mul_I]
  have hc : ∀ t : ι → ℝ,
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω) ∂ν = 0 := by
    intro t
    have h1 := congrArg (starRingEnd ℂ) (h (-t))
    rw [← integral_conj, map_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
    simp
  have hlin : ∀ (a b : ℂ) (t : ι → ℝ),
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω)) ∂ν = 0 := by
    intro a b t
    have e1 := bdd_int ν _ ρ (hE t) (hEb t) hρ
    have e2 := bdd_int ν _ _ (hE t) (hEb t) hconjI
    have : ∀ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω))
        = a * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω)
          + b * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω)) := by
      intro ω; ring
    simp only [this]
    rw [integral_add (e1.const_mul a) (e2.const_mul b), integral_const_mul, integral_const_mul,
      h t, hc t]
    simp
  have hre : Integrable (fun ω => (ρ ω).re) ν := hρ.re
  have him : Integrable (fun ω => (ρ ω).im) ν := hρ.im
  have r1 := real_case ν X (fun ω => (ρ ω).re) hX hre (fun t => by
    rw [← hlin (1 / 2) (1 / 2) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).re : ℂ) = 1 / 2 * ρ ω + 1 / 2 * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.re_eq_add_conj]; ring
    simp only [this]) S hS
  have r2 := real_case ν X (fun ω => (ρ ω).im) hX him (fun t => by
    rw [← hlin (1 / (2 * Complex.I)) (-(1 / (2 * Complex.I))) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).im : ℂ) = 1 / (2 * Complex.I) * ρ ω
        + -(1 / (2 * Complex.I)) * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.im_eq_sub_conj]; ring
    simp only [this]) S hS
  have hind : Measurable fun ω => S.indicator (1 : (ι → ℝ) → ℂ) (X ω) :=
    (measurable_one.indicator hS).comp hX
  have hindb : ∀ ω, ‖S.indicator (1 : (ι → ℝ) → ℂ) (X ω)‖ ≤ 1 := by
    intro ω
    by_cases hx : X ω ∈ S <;> simp [hx]
  have i1 := bdd_int ν _ (fun ω => ((ρ ω).re : ℂ)) hind hindb hre.ofReal
  have i2 := bdd_int ν _ (fun ω => ((ρ ω).im : ℂ)) hind hindb him.ofReal
  have hsplit : ∀ ω, S.indicator 1 (X ω) * ρ ω
      = S.indicator 1 (X ω) * ((ρ ω).re : ℂ)
        + Complex.I * (S.indicator 1 (X ω) * ((ρ ω).im : ℂ)) := by
    intro ω
    conv_lhs => rw [← Complex.re_add_im (ρ ω)]
    ring
  simp only [hsplit]
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, r1, r2]
  simp
end
