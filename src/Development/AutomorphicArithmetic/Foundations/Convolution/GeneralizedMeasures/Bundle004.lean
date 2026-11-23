module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle001
public import Development.AutomorphicArithmetic.AdelicQuotients.ExistsCompactFundamentalSetOfHeightLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HtCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.SphAct
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.GlobalFields.Adele.Topology
import GroundTheory.AutomorphicForms.CuspidalAdmissible
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

namespace UpperTheory.ConvolutionTheory.GM

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]

private theorem sum_smul_apply {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n) (g : normOneGL (K := K) (n := n)) :
    (∑ i ∈ s, c i • f i) g = ∑ i ∈ s, c i * f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, CompactlySupportedContinuousMap.add_apply, ih]
    simp

private theorem rop_add (a b : TG K n) : Rop μ (a + b) = Rop μ a + Rop μ b := by
  have h : UnitaryRep.ccToL1 μ (a + b) = UnitaryRep.ccToL1 μ a + UnitaryRep.ccToL1 μ b := by
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_add]
    rfl
  unfold Rop
  rw [h]
  exact ContinuousLinearMap.map_add _ _ _

private theorem rop_smul (c : ℂ) (a : TG K n) : Rop μ (c • a) = c • Rop μ a := by
  have h : UnitaryRep.ccToL1 μ (c • a) = c • UnitaryRep.ccToL1 μ a := by
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_const_smul]
    rfl
  unfold Rop
  rw [h]
  exact ContinuousLinearMap.map_smul _ _ _

private theorem rop_zero : Rop μ (0 : TG K n) = 0 := by
  simpa using rop_smul (μ := μ) (0 : ℂ) (0 : TG K n)

private theorem rop_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n) :
    Rop μ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Rop μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rop_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, rop_add, rop_smul, ih]

private theorem twK_fin (θ : Twist μ) (f : TG K n) (x : normOneGL (K := K) (n := n)) :
    (Function.support fun γ : Gam K n => f (x⁻¹ * (γ : G1 K n) * θ.e x)).Finite :=
  finite_support_automorphicKernel (Gam K n) f (x, θ.e x)

private theorem twK_sum (θ : Twist μ) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n)
    (x : normOneGL (K := K) (n := n)) : twK θ (∑ i ∈ s, c i • f i) x = ∑ i ∈ s, c i * twK θ (f i) x := by
  unfold twK
  simp only [sum_smul_apply]
  rw [finsum_sum_comm]
  · exact Finset.sum_congr rfl fun i _ => (mul_finsum _ _).symm
  · intro i _
    refine (twK_fin θ (f i) x).subset fun γ hγ h0 => hγ ?_
    simp only [Function.mem_support, not_not] at h0 ⊢
    simp only [Function.mem_support, ne_eq, Decidable.not_not] at *
    rw [h0, mul_zero]

private theorem twK_cont (θ : Twist μ) (f : TG K n) : Continuous (twK θ f) := by
  have h : Continuous fun x : normOneGL (K := K) (n := n) => automorphicKernel (Gam K n) f (x, θ.e x) :=
    (continuous_automorphicKernel (Gam K n) f).comp (continuous_id.prodMk θ.e.continuous)
  exact h

private theorem twK_left (θ : Twist μ) (f : TG K n) {δ : normOneGL (K := K) (n := n)} (hδ : δ ∈ Gam K n)
    (x : normOneGL (K := K) (n := n)) : twK θ f (δ * x) = twK θ f x := by
  have h1 := automorphicKernel_smul_left (Gam K n) f ⟨δ, hδ⟩ x (θ.e (δ * x))
  have h2 := automorphicKernel_smul_right (Gam K n) f ⟨θ.e δ, (θ.mem_gam δ).2 hδ⟩ x (θ.e x)
  have e1 : twK θ f (δ * x) =
      automorphicKernel (Gam K n) f ((⟨δ, hδ⟩ : Gam K n) • x, θ.e (δ * x)) := rfl
  have e2 : θ.e (δ * x) = (⟨θ.e δ, (θ.mem_gam δ).2 hδ⟩ : Gam K n) • θ.e x := by
    rw [map_mul]
    rfl
  rw [e1, h1, e2, h2]
  rfl

private theorem twKQ_mk (θ : Twist μ) (f : TG K n) (x : normOneGL (K := K) (n := n)) :
    twKQ θ f (mk (Gam K n) x) = twK θ f x := by
  obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1
    (show mk (Gam K n) (Quotient.out (mk (Gam K n) x)) = mk (Gam K n) x from Quotient.out_eq _)
  change twK θ f (Quotient.out (mk (Gam K n) x)) = _
  rw [← hγ]
  exact twK_left θ f γ.2 x

private theorem twKQ_int (θ : Twist μ) (f : TG K n) (Z : ℝ) (h : ∀ x, Z < qht x → twK θ f x = 0) :
    Integrable (twKQ θ f) (quotientMeasure (Gam K n) μ) := by
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hc : Continuous (twKQ θ f) :=
    (isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff.2
      ((twK_cont θ f).congr fun x => (twKQ_mk θ f x).symm)
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_of_height_le K n Z
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (twK_cont θ f).continuousOn
  have hm : AEStronglyMeasurable (twKQ θ f) (quotientMeasure (Gam K n) μ) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact hc.aestronglyMeasurable
  refine Integrable.of_bound hm (max M 0) (Eventually.of_forall fun y => ?_)
  change ‖twK θ f (Quotient.out y)‖ ≤ _
  by_cases hz : Z < qht (Quotient.out y)
  · rw [h _ hz, norm_zero]
    exact le_max_right _ _
  · obtain ⟨g, hg, c, hc', e⟩ := hcov _ (not_lt.1 hz)
    rw [e, twK_left θ f hg]
    exact (hM c hc').trans (le_max_left _ _)

end

end UpperTheory.ConvolutionTheory.GM

theorem UpperTheory.ConvolutionTheory.GM.twLin :
    TwLin := by
  intro K _ _ n _ μ _ θ ι s c f Z h
  refine ⟨rop_sum s c f, fun x hx => ?_, ?_⟩
  · rw [twK_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [h i hi x hx, mul_zero]
  · have e : ∀ y, twKQ θ (∑ i ∈ s, c i • f i) y = ∑ i ∈ s, c i * twKQ θ (f i) y :=
      fun y => twK_sum θ s c f _
    unfold twInt
    simp only [e]
    rw [integral_finsetSum _ fun i hi => (twKQ_int θ (f i) Z (h i hi)).const_mul _]
    simp only [integral_const_mul]
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped Pointwise

theorem UpperTheory.ConvolutionTheory.GM.wordHt :
    WordHt := by
  intro K _ _ n hn ν _ a₀ ha₀
  have hT : IsCompact (tsupport (a₀ : archGroup K n → ℂ)) := a₀.hasCompactSupport
  set S : Set (AdelicGLn.AdelicGL K n) := (infEmb K n) '' tsupport (a₀ : archGroup K n → ℂ) with hS
  obtain ⟨Y, hY1, -, hY⟩ := UpperTheory.ConvolutionTheory.Tf.htCompact K n S (hT.image AutomorphicForm.continuous_infEmb)
  have hlet : ∀ (x : Option (Ix K n)) (y : archGroup K n), letter a₀ x y ≠ 0 →
      y ∈ tsupport (a₀ : archGroup K n → ℂ) := by
    intro x y hy
    cases x with
    | none => exact subset_tsupport _ hy
    | some x =>
      obtain ⟨-, -, h2, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n a₀ ha₀
      exact (h2 (zc x.1 x.2)).2 (subset_tsupport _ hy)
  have key : ∀ (wd : List (Option (Ix K n))) (g : archGroup K n), word ν a₀ wd g ≠ 0 →
      infEmb K n g ∈ S ^ (wd.length + 1) := by
    intro wd
    induction wd with
    | nil =>
      intro g hg
      have hg' : a₀ g ≠ 0 := hg
      rw [List.length_nil, zero_add, pow_one]
      exact Set.mem_image_of_mem _ (subset_tsupport _ hg')
    | cons x w ih =>
      intro g hg
      have hc : (∫ y, letter a₀ x y * word ν a₀ w (y⁻¹ * g) ∂ν) ≠ 0 := by
        have := (UpperTheory.ConvolutionTheory.GM.convSpec K n hn ν (letter a₀ x) (word ν a₀ w)).1 g
        rw [← this]
        exact hg
      obtain ⟨y, hy⟩ : ∃ y, letter a₀ x y * word ν a₀ w (y⁻¹ * g) ≠ 0 := by
        by_contra hne
        push_neg at hne
        exact hc (by simp [hne])
      have hy1 := left_ne_zero_of_mul hy
      have hy2 := right_ne_zero_of_mul hy
      have hm := ih _ hy2
      have he : infEmb K n g = infEmb K n y * infEmb K n (y⁻¹ * g) := by
        rw [← map_mul, mul_inv_cancel_left]
      rw [List.length_cons, pow_succ', he]
      exact Set.mul_mem_mul (Set.mem_image_of_mem _ (hlet x y hy1)) hm
  exact ⟨Y, hY1, fun wd g hg => hY _ _ (key wd g hg)⟩
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem hf_cf_self (w : Pl K) (y : GL (Fin n) (w.adicCompletion K)) (x : AdelicGLn.FiniteAdelicGL K n) :
    cf w (AdelicGLn.localEmbedding w y * x) = y * cf w x := by
  unfold cf
  rw [map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]

private theorem hf_cf_ne {w v : Pl K} (hv : v ≠ w) (y : GL (Fin n) (w.adicCompletion K))
    (x : AdelicGLn.FiniteAdelicGL K n) : cf v (AdelicGLn.localEmbedding w y * x) = cf v x := by
  unfold cf
  rw [map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.1 v hv, one_mul]

private theorem hf_cont (w : Pl K) : Continuous (cf (n := n) w) :=
  (continuous_finAt w).comp continuous_finEmb

private theorem hf_ex (w : Pl K) (h : GL (Fin n) (w.adicCompletion K) → ℂ) (hc : Continuous h) (hs : HasCompactSupport h)
    (r : AdelicGLn.FiniteAdelicGL K n → ℂ) (hr : Free w r) (e₀ : TF K n)
    (h₀ : ∀ x, e₀ x = r x * (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x)) :
    ∃ e : TF K n, ∀ x, e x = r x * h (cf w x) := by
  have hl := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
  have key : ∀ x, r x = e₀ (AdelicGLn.localEmbedding w (cf w x)⁻¹ * x) := by
    intro x
    rw [h₀, hf_cf_self, inv_mul_cancel, hr, Set.indicator_of_mem (by exact one_mem _)]
    simp
  have hrc : Continuous r := by
    rw [funext key]
    exact (map_continuous e₀).comp ((hl.comp (hf_cont w).inv).mul continuous_id)
  have h1 : Continuous fun x => r x * h (cf w x) := hrc.mul (hc.comp (hf_cont w))
  have h2 : HasCompactSupport fun x => r x * h (cf w x) := by
    have hK : IsCompact ((fun q : GL (Fin n) (w.adicCompletion K) × AdelicGLn.FiniteAdelicGL K n =>
        AdelicGLn.localEmbedding w q.1 * q.2) '' (tsupport h ×ˢ tsupport e₀)) :=
      (hs.isCompact.prod e₀.hasCompactSupport.isCompact).image ((hl.comp continuous_fst).mul continuous_snd)
    haveI : T2Space (FiniteAdeleRing (𝓞 K) K) := GroundTheory.Global.t2Space_finiteAdeleRing K
    haveI : T2Space (AdelicGLn.FiniteAdelicGL K n) := Units.isEmbedding_embedProduct.t2Space
    refine HasCompactSupport.intro' hK hK.isClosed fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨(cf w x, AdelicGLn.localEmbedding w (cf w x)⁻¹ * x), ⟨subset_tsupport _ (right_ne_zero_of_mul hne),
      subset_tsupport _ ?_⟩, ?_⟩
    · have := left_ne_zero_of_mul hne
      rwa [key] at this
    · simp only [map_inv, mul_inv_cancel_left]
  exact ⟨⟨⟨_, h1⟩, h2⟩, fun _ => rfl⟩

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.GM.heckeFin :
    HeckeFin := by
  intro K _ _ n hn μ _ m _ 𝔞 ev hev T
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ p h _ r _ e₀ e₁ h₀ h₁
    have : e₁ = e₀ := by
      ext x
      rw [h₀, h₁, Finset.prod_empty, Finset.prod_empty]
    rw [this, Finset.prod_empty, map_one, map_one]
    rfl
  | insert w T hw ih =>
    intro hS p h hsph r hr e₀ e₁ h₀ h₁
    have hwm : w ∈ insert w T := Finset.mem_insert_self w T
    have hne : ∀ v ∈ T, v ≠ w := fun v hv hvw => hw (hvw ▸ hv)
    obtain ⟨hlc, hcs, hinv⟩ := (sphEx K n hn w).2.2 (p w) (h w) (hsph w hwm)
    set r' : AdelicGLn.FiniteAdelicGL K n → ℂ := fun x =>
      r x * ∏ v ∈ T, (GLnLocal.integralGL (v.adicCompletion K) n : Set _).indicator 1 (cf v x) with hr'
    have hfree : Free w r' := by
      intro y x
      simp only [hr']
      rw [hr w hwm y x]
      congr 1
      exact Finset.prod_congr rfl fun v hv => by rw [hf_cf_ne (hne v hv)]
    have h₀' : ∀ x, e₀ x = r' x * (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x) := by
      intro x
      rw [h₀, Finset.prod_insert hw]
      simp only [hr']
      ring
    obtain ⟨e, he⟩ := hf_ex w (h w) hlc.continuous hcs r' hfree e₀ h₀'
    obtain ⟨hfix, hstep⟩ := stepFin K n hn μ m w (GLnLocal.integralGL (w.adicCompletion K) n)
      (GLnLocal.isOpen_integralGL _ n) (h w) hcs (fun k hk x => (hinv k hk x).2) r' hfree e₀ e h₀' he
    have hA : Ofin μ m e = ev (map C (atPl w (p w))) ∘L Ofin μ m e₀ := by
      rw [hstep]
      refine ContinuousLinearMap.ext fun u => ?_
      exact sphAct K n hn μ 𝔞 ev hev w (hS w hwm) (p w) (h w) (hsph w hwm) _ (hfix u)
    have hB := ih (fun v hv => hS v (Finset.mem_insert_of_mem hv)) p h
      (fun v hv => hsph v (Finset.mem_insert_of_mem hv)) (fun x => r x * h w (cf w x))
      (fun v hv y x => by
        show r _ * h w _ = r x * h w _
        rw [hr v (Finset.mem_insert_of_mem hv) y x, hf_cf_ne (hne v hv).symm]) e e₁
      (fun x => by
        rw [he]
        simp only [hr']
        ring)
      (fun x => by
        rw [h₁, Finset.prod_insert hw]
        ring)
    rw [hB, hA, Finset.prod_insert hw, mul_comm (atPl w (p w)), map_mul, map_mul]
    rfl
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem gl_cont {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (x : GL (Fin n) k) :
    Continuous (fun p : GL (Fin n) k × GL (Fin n) k => p.1 * x * p.2) :=
  (continuous_fst.mul continuous_const).mul continuous_snd

private theorem iwCoset_eq_image {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    iwCoset w ν = (fun p : GL (Fin n) (w.adicCompletion K) × GL (Fin n) (w.adicCompletion K) =>
        p.1 * Cartan.diagPow (w.adicCompletion K) n ν * p.2) ''
      ((GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) ×ˢ
        (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K)))) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

private theorem iwCoset_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) :
    iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one, mul_one]⟩

private theorem out_mem_iwCoset_iff {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ)
    (c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n) :
    c.out ∈ iwCoset w ν ↔ c ∈ {c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n |
      ∃ k ∈ GLnLocal.iwahori (w.adicCompletion K) n,
        c = QuotientGroup.mk (k * Cartan.diagPow (w.adicCompletion K) n ν)} := by
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, ?_⟩
    rw [← QuotientGroup.out_eq' c, h]
    refine QuotientGroup.eq.mpr ?_
    have : (a * Cartan.diagPow (w.adicCompletion K) n ν * b)⁻¹ * (a * Cartan.diagPow (w.adicCompletion K) n ν) = b⁻¹ := by
      group
    rw [this]
    exact inv_mem hb
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (GLnLocal.iwahori (w.adicCompletion K) n)
      (k * Cartan.diagPow (w.adicCompletion K) n ν)
    exact ⟨k, hk, h, h.2, hh⟩

private theorem iwCoset_ind_hasCompactSupport {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ)
    (hC : IsCompact (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K)))) :
    HasCompactSupport ((iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ)) := by
  have hcomp : IsCompact (iwCoset w ν) := by
    rw [iwCoset_eq_image]
    exact (hC.prod hC).image (gl_cont _)
  exact HasCompactSupport.intro hcomp (fun x hx => Set.indicator_of_notMem hx _)

private theorem iwCoset_ind_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    ∀ k ∈ GLnLocal.iwahori (w.adicCompletion K) n, ∀ x,
      (iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) (x * k) =
        (iwCoset w ν).indicator 1 x := by
  intro k hk x
  have hiff : x * k ∈ iwCoset w ν ↔ x ∈ iwCoset w ν := by
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      refine ⟨a, ha, b * k⁻¹, mul_mem hb (inv_mem hk), ?_⟩
      rw [← mul_assoc, ← h]
      group
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by group⟩
  by_cases hxm : x ∈ iwCoset w ν
  · rw [Set.indicator_of_mem hxm, Set.indicator_of_mem (hiff.2 hxm)]
    rfl
  · rw [Set.indicator_of_notMem hxm, Set.indicator_of_notMem (fun h => hxm (hiff.1 h))]

private theorem iwCoset_sum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (ν : Fin n → ℤ) :
    (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n,
        (iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) c.out • rhoL μ w c.out) =
      ∑ᶠ c ∈ {c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n |
          ∃ k ∈ GLnLocal.iwahori (w.adicCompletion K) n,
            c = QuotientGroup.mk (k * Cartan.diagPow (w.adicCompletion K) n ν)}, rhoL μ w c.out := by
  rw [finsum_mem_def]
  refine finsum_congr fun c => ?_
  by_cases hc : c.out ∈ iwCoset w ν
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem ((out_mem_iwCoset_iff w _ c).1 hc)]
    simp
  · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun h => hc ((out_mem_iwCoset_iff w _ c).2 h))]
    simp

private theorem uiw_comp_of_fix {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (ν : Fin n → ℤ) (T : LL μ →L[ℂ] LL μ)
    (hfix : ∀ u, T u ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion K) n)) :
    (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n,
        (iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) c.out • rhoL μ w c.out) ∘L T =
      Uiw μ w ν ∘L T := by
  rw [iwCoset_sum, Uiw, Hop, ContinuousLinearMap.comp_assoc]
  congr 1
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, prj]
  exact (Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure _ (hfix u))).symm

theorem UpperTheory.ConvolutionTheory.GM.uiwFin :
    UiwFin := by
  intro K _ _ n hn μ _ m _ w ν hν j r hr e₀ e₁ h₀ h₁
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hz : (fun i => ((0 : ℕ) : ℤ) * ν i) = (0 : Fin n → ℤ) := by
      funext i
      simp
    have he : e₁ = e₀ := by
      ext x
      rw [h₀, h₁, hz]
    rw [he, pow_zero]
    rfl
  obtain ⟨-, hpow, hO, hC, -⟩ := UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w ν ν hν hν
  have hx : (fun i => (j : ℤ) * ν i) = j • ν := by
    funext i
    simp
  rw [hx] at h₁
  obtain ⟨hfix, hOf⟩ := UpperTheory.ConvolutionTheory.GM.stepFin K n hn μ m w (GLnLocal.iwahori (w.adicCompletion K) n) hO
    ((iwCoset w (j • ν)).indicator 1) (iwCoset_ind_hasCompactSupport w _ hC) (iwCoset_ind_mul w _) r hr e₀ e₁
    (fun x => by rw [h₀, iwCoset_zero]) h₁
  rw [hOf, hpow j hj]
  exact uiw_comp_of_fix μ w _ _ hfix
end
