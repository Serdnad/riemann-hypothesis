module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle009
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.cont :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)), Continuous η → IsOm δ η Om →
    ∀ φ, Continuous fun p : G1 F × V4 F => (Om p.1 φ).1 p.2 := by
  intro F _ _ δ η Om hη hOm φ
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, v₀⟩
  obtain ⟨b, c, a, k, hb, hc, ha, hk, hev⟩ := near F
  set φ' : S4 F := Om g₀ φ with hφ'
  set φ'' : S4 F := Om (wW F)⁻¹ φ' with hφ''

  let H : G1 F × V4 F → G1 F := fun p => p.1 * g₀⁻¹
  have hH1 : H (g₀, v₀) = 1 := by simp [H]
  have hH : Tendsto H (𝓝 (g₀, v₀)) (𝓝 1) := by
    have : ContinuousAt H (g₀, v₀) := by
      have : Continuous H := continuous_fst.mul continuous_const
      exact this.continuousAt
    simpa [ContinuousAt, hH1] using this

  let f : G1 F × V4 F → ℂ := fun p =>
    ψ (b (H p) * q4 δ p.2) * (((η (a (H p)) : ℂˣ) : ℂ) * ((ab (a (H p)) ^ 2 : ℝ) : ℂ) *
      ft4 δ (fun y => ψ (c (H p) * q4 δ y) * φ''.1 y) (fun i => (a (H p) : A F) * p.2 i))
  have hbH : ContinuousAt (fun p => b (H p)) (g₀, v₀) := by
    show Tendsto (fun p => b (H p)) _ (𝓝 (b (H (g₀, v₀))))
    rw [hH1]
    exact hb.tendsto.comp hH
  have hcH : ContinuousAt (fun p => c (H p)) (g₀, v₀) := by
    show Tendsto (fun p => c (H p)) _ (𝓝 (c (H (g₀, v₀))))
    rw [hH1]
    exact hc.tendsto.comp hH
  have haH : ContinuousAt (fun p => a (H p)) (g₀, v₀) := by
    show Tendsto (fun p => a (H p)) _ (𝓝 (a (H (g₀, v₀))))
    rw [hH1]
    exact ha.tendsto.comp hH
  have hf : ContinuousAt f (g₀, v₀) := by
    have hs : ContinuousAt (fun p : G1 F × V4 F => p.2) (g₀, v₀) := continuous_snd.continuousAt
    have hav : ContinuousAt (fun p => ((a (H p) : (A F)ˣ) : A F)) (g₀, v₀) :=
      Units.continuous_val.continuousAt.comp haH
    have h1 : ContinuousAt (fun p : G1 F × V4 F => ψ (b (H p) * q4 δ p.2)) (g₀, v₀) :=
      continuous_ψ.continuousAt.comp (hbH.mul ((continuous_quaternaryQuadraticForm δ).continuousAt.comp hs))
    have h2 : ContinuousAt (fun p : G1 F × V4 F => ((η (a (H p)) : ℂˣ) : ℂ)) (g₀, v₀) :=
      (Units.continuous_val.comp hη).continuousAt.comp haH
    have h3 : ContinuousAt (fun p : G1 F × V4 F => ((ab (a (H p)) ^ 2 : ℝ) : ℂ)) (g₀, v₀) :=
      Complex.continuous_ofReal.continuousAt.comp ((continuous_ab.continuousAt.comp haH).pow 2)
    have hvec : ContinuousAt (fun p : G1 F × V4 F => (fun i => (a (H p) : A F) * p.2 i : V4 F)) (g₀, v₀) := by
      refine continuousAt_pi.2 fun i => hav.mul ?_
      exact (continuous_apply i).continuousAt.comp hs
    have h4 : ContinuousAt (fun p : G1 F × V4 F =>
        ft4 δ (fun y => ψ (c (H p) * q4 δ y) * φ''.1 y) (fun i => (a (H p) : A F) * p.2 i)) (g₀, v₀) :=
      ContinuousAt.comp (f := fun p : G1 F × V4 F => (c (H p), (fun i => (a (H p) : A F) * p.2 i : V4 F)))
        (g := fun p : A F × V4 F => ft4 δ (fun y => ψ (p.1 * q4 δ y) * φ''.1 y) p.2)
        (contKer F δ φ'').continuousAt (hcH.prodMk hvec)
    exact h1.mul ((h2.mul h3).mul h4)
  refine hf.congr ?_

  have hlev : ∀ᶠ h in 𝓝 (1 : G1 F), InfOne (k h) → Om (k h) φ' = φ' := by
    exact hk.eventually (level F δ η Om hOm φ')
  filter_upwards [hH.eventually (hev.and hlev)] with p hp
  obtain ⟨⟨hinf, hdec⟩, hl⟩ := hp
  have hg : p.1 = H p * g₀ := by simp [H]
  have hkey : Om p.1 φ = Om (nU (b (H p))) (Om (mD (a (H p))) (Om (wW F) (Om (nU (c (H p))) φ''))) := by
    rw [hg, map_mul, Module.End.mul_apply, ← hφ']
    conv_lhs => rw [hdec]
    simp only [map_mul, Module.End.mul_apply]
    rw [hl hinf]
  show f p = (Om p.1 φ).1 p.2
  rw [hkey, hOm.n, hOm.m, hOm.w]
  show _ = ψ _ * (_ * _ * ft4 δ (Om (nU (c (H p))) φ'').1 _)
  have : (Om (nU (c (H p))) φ'').1 = fun y => ψ (c (H p) * q4 δ y) * φ''.1 y := funext (hOm.n _ _)
  rw [this]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma psi_rt {F : Type} [Field F] [NumberField F] (c : F) : ψ (UpperTheory.ConvolutionTheory.R2.rt c) = 1 := by
  unfold ψ UpperTheory.ConvolutionTheory.R2.rt
  rw [adelicChar_algebraMap]
  simp

private lemma quadraticForm_rational_embed {F : Type} [Field F] [NumberField F] (δ : F) (ξ : Fin 4 → F) :
    q4 δ (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i)) = UpperTheory.ConvolutionTheory.R2.rt (ξ 2 ^ 2 - δ * ξ 3 ^ 2 - ξ 1 * ξ 0) := by
  simp [q4, UpperTheory.ConvolutionTheory.R2.rt, map_sub, map_mul, map_pow]

theorem UpperTheory.ConvolutionTheory.R2.C.thOm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)), δ ≠ 0 → IsOm δ η Om → ∀ γ φ, Th (Om (ratS F γ) φ).1 = Th φ.1 := by
  intro F _ _ δ η Om hδ hO γ
  have hγ : ratS F γ ∈ Subgroup.closure (Set.range (fun b : F => nU (UpperTheory.ConvolutionTheory.R2.rt b)) ∪ {wW F}) := by
    rw [(UpperTheory.ConvolutionTheory.R2.gen F).2]
    exact ⟨γ, rfl⟩
  have key : ∀ g ∈ Subgroup.closure (Set.range (fun b : F => nU (UpperTheory.ConvolutionTheory.R2.rt b)) ∪ {wW F}),
      ∀ φ : S4 F, Th (Om g φ).1 = Th φ.1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      intro φ
      rcases hg with ⟨b, rfl⟩ | hg
      · unfold Th
        refine tsum_congr fun ξ => ?_
        rw [hO.n, quadraticForm_rational_embed, ← map_mul, psi_rt, one_mul]
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        have h : (Om (wW F) φ).1 = ft4 δ φ.1 := funext (hO.w φ)
        rw [h]
        exact (UpperTheory.ConvolutionTheory.R2.C.ftBasic F δ hδ φ.1 φ.2).2.2
    | one => intro φ; simp
    | mul x y _ _ hx hy =>
      intro φ
      rw [map_mul, Module.End.mul_apply, hx, hy]
    | inv x _ hx =>
      intro φ
      have h := hx (Om x⁻¹ φ)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
      exact h.symm
  exact key _ hγ
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.opsGauss :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (O : Ops δ η), δ ≠ 0 → (∀ a, η a ^ 2 = 1) →
    (∀ b : (A F)ˣ, IsIdx δ (b : A F) (((η b : ℂˣ) : ℂ) * (((ab b)⁻¹ ^ 2 : ℝ) : ℂ))) → Gauss O.N O.M O.W := by
  intro F _ _ δ η O hδ hη hidx t
  obtain ⟨b, hb⟩ : ∃ b : (A F)ˣ, b = -t⁻¹ := ⟨_, rfl⟩
  have hbc : -((t⁻¹ : (A F)ˣ) : A F) = (b : A F) := by simp [hb]
  have htb : -(((b⁻¹ : (A F)ˣ) : A F)) = (t : A F) := by simp [hb]
  rw [hbc, ← hb]
  refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
  simp only [Module.End.mul_apply]
  have hL : (O.W (O.N (t : A F) (O.W φ))).1 v =
      ft4 δ (fun y => ψ ((t : A F) * q4 δ y) * ft4 δ φ.1 y) v := by
    rw [O.W_apply]
    congr 1
    funext y
    rw [O.N_apply, O.W_apply]
  have hR : (O.N (b : A F) (O.M b (O.W (O.N (b : A F) φ)))).1 v =
      ((η b : ℂˣ) : ℂ) * ((ab b ^ 2 : ℝ) : ℂ) * Pc δ (b : A F) φ.1 v := by
    rw [O.N_apply, O.M_apply, O.W_apply, (pcMem F δ).1]
    have : (fun y => (O.N (b : A F) φ).1 y) = fun x => ψ ((b : A F) * q4 δ x) * φ.1 x :=
      funext fun y => O.N_apply _ _ _
    have h2 : (O.N (b : A F) φ).1 = fun x => ψ ((b : A F) * q4 δ x) * φ.1 x := this
    rw [h2]
    ring
  have hG := gaussOp F δ hδ b _ (hidx b) φ v
  have hη2 : ((η b : ℂˣ) : ℂ) ^ 2 = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (hη b)
    simpa using this
  have hab : ab b ≠ 0 := by
    have : 0 < ab b := (IdeleGroup.ideleModule F b).2
    exact this.ne'
  have habc : ((ab b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hab
  have hfn : (fun y => ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 y) =
      fun y => ψ ((t : A F) * q4 δ y) * ft4 δ φ.1 y := by
    funext y
    rw [← htb, neg_mul]
  rw [hfn] at hG
  rw [hL, hR, hG]
  push_cast
  field_simp
  rw [hη2]
  ring
end
