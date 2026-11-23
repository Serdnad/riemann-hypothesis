module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle207
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormTheta2TailLeOfLeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.WaveWords

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun hc continuous_const

section Good

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Good (T : (Mat n → V) → (Mat n → V)) : Prop :=
  (∀ f, ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (T f) (GLs n)) ∧
  (∀ (f h : Mat n → V) (a b : ℂ), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) →
    ∀ x ∈ GLs n, T (fun y => a • f y + b • h y) x = a • T f x + b • T h x) ∧
  (∀ f f', Set.EqOn f f' (GLs n) → Set.EqOn (T f) (T f') (GLs n))

theorem good_id : Good (n := n) (V := V) (fun f => f) :=
  ⟨fun _ h => h, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ h => h⟩

theorem good_zero : Good (n := n) (V := V) (fun _ => 0) := by
  refine ⟨fun _ _ => contDiffOn_const, fun _ _ a b _ _ x _ => by simp, fun _ _ _ _ _ => rfl⟩

theorem good_Rd (hR : RCalc) (X : Mat n) : Good (n := n) (V := V) (Rd X) := by
  refine ⟨fun f hf => ((hR n).1 V f hf).1 X, ?_, ?_⟩
  · intro f h a b hf hh x hx
    have hn : GLs n ∈ nhds x := (isOpen_GLs n).mem_nhds hx
    have df : DifferentiableAt ℝ f x := (hf.contDiffAt hn).differentiableAt (by simp)
    have dh : DifferentiableAt ℝ h x := (hh.contDiffAt hn).differentiableAt (by simp)
    have key : HasFDerivAt (fun y => a • f y + b • h y)
        (a • fderiv ℝ f x + b • fderiv ℝ h x) x :=
      (df.hasFDerivAt.const_smul a).add (dh.hasFDerivAt.const_smul b)
    simp only [Rd]
    rw [key.fderiv]
    simp
  · intro f f' hE x hx
    have hn : GLs n ∈ nhds x := (isOpen_GLs n).mem_nhds hx
    have : f =ᶠ[nhds x] f' := Filter.eventuallyEq_of_mem hn hE
    simp only [Rd]
    rw [this.fderiv_eq]

theorem good_comp {T T' : (Mat n → V) → (Mat n → V)} (hT : Good T) (hT' : Good T') :
    Good (fun f => T (T' f)) := by
  refine ⟨fun f hf => hT.1 _ (hT'.1 f hf), ?_, fun f f' hE => hT.2.2 _ _ (hT'.2.2 f f' hE)⟩
  intro f h a b hf hh x hx
  have e : Set.EqOn (T' (fun y => a • f y + b • h y)) (fun y => a • T' f y + b • T' h y) (GLs n) :=
    fun y hy => hT'.2.1 f h a b hf hh y hy
  beta_reduce
  rw [hT.2.2 _ _ e hx]
  exact hT.2.1 _ _ a b (hT'.1 f hf) (hT'.1 h hh) x hx

theorem good_add {T T' : (Mat n → V) → (Mat n → V)} (hT : Good T) (hT' : Good T') :
    Good (fun f => T f + T' f) := by
  refine ⟨fun f hf => (hT.1 f hf).add (hT'.1 f hf), ?_, ?_⟩
  · intro f h a b hf hh x hx
    simp only [Pi.add_apply]
    rw [hT.2.1 f h a b hf hh x hx, hT'.2.1 f h a b hf hh x hx]
    module
  · intro f f' hE x hx
    simp only [Pi.add_apply]
    rw [hT.2.2 f f' hE hx, hT'.2.2 f f' hE hx]

theorem good_smul (c : ℂ) {T : (Mat n → V) → (Mat n → V)} (hT : Good T) :
    Good (fun f => c • T f) := by
  refine ⟨fun f hf => (hT.1 f hf).const_smul c, ?_, ?_⟩
  · intro f h a b hf hh x hx
    simp only [Pi.smul_apply]
    rw [hT.2.1 f h a b hf hh x hx]
    module
  · intro f f' hE x hx
    simp only [Pi.smul_apply]
    rw [hT.2.2 f f' hE hx]

theorem good_sum {ι : Type} (s : Finset ι) (T : ι → (Mat n → V) → (Mat n → V))
    (h : ∀ i, Good (T i)) : Good (fun f => ∑ i ∈ s, T i f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a) ih

theorem good_Eu (hR : RCalc) (s : Bool) (a b : Fin n) : Good (n := n) (V := V) (Eu s a b) :=
  good_smul (1 / 2 : ℂ) (good_add (good_Rd hR _) (good_smul _ (good_Rd hR _)))

theorem good_Epow (hR : RCalc) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Good (n := n) (V := V) (Epow s m a b) := by
  induction m with
  | zero =>
    intro a b
    by_cases h : a = b
    · have e : Epow (n := n) (V := V) s 0 a b = fun f => f := by
        funext f; simp [Epow, h]
      rw [e]; exact good_id
    · have e : Epow (n := n) (V := V) s 0 a b = fun _ => 0 := by
        funext f; simp [Epow, h]
      rw [e]; exact good_zero
  | succ m ih =>
    intro a b
    exact good_sum Finset.univ (fun c f => Eu s a c (Epow s m c b f))
      (fun c => good_comp (good_Eu hR s a c) (ih c b))

theorem good_gel (hR : RCalc) (s : Bool) (m : ℕ) : Good (n := n) (V := V) (gel s m) :=
  good_sum Finset.univ (fun a => Epow s m a a) (fun a => good_Epow hR s m a a)

theorem good_zOp (hR : RCalc) (w : List (Bool × ℕ)) : Good (n := n) (V := V) (zOp w) := by
  induction w with
  | nil => exact good_id
  | cons p w ih =>
    have e : zOp (n := n) (V := V) (p :: w) = fun f => gel p.1 p.2 (zOp w f) := rfl
    rw [e]
    exact good_comp (good_gel hR p.1 p.2) ih

end Good

end GlobalTheory.CompanionTheory.WaveWords
end
end

section

noncomputable section

open MeasureTheory Matrix Finset PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open scoped ContDiff ComplexConjugate InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WeightIbp

variable {n : ℕ}

theorem isOpen_invertible : IsOpen (GLs n) := by
  have h : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

theorem val_mem_invertible (y : G n) : y.val ∈ GLs n := by
  have h : y.val.det * (y⁻¹ : G n).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one h

theorem integrable_of_continuousOn (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] {W : Type} [NormedAddCommGroup W] (F : Mat n → W) (hF : ContinuousOn F (GLs n)) (hc : Cpt F) :
    Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hc
  have hcont : Continuous fun y : G n => F y.val :=
    hF.comp_continuous Units.continuous_val val_mem_invertible
  have hK : IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1 R
  have hsupp : HasCompactSupport fun y : G n => F y.val := by
    refine HasCompactSupport.intro hK fun y hy => ?_
    exact hR _ (val_mem_invertible y) (not_le.1 hy)
  exact hcont.integrable_of_hasCompactSupport hsupp

theorem fderiv_eq_zero_far (hL : LgFacts) {φ : Mat n → ℝ} {R : ℝ} (hR : ∀ y ∈ GLs n, R < lg y → φ y = 0)
    {y : Mat n} (hy : y ∈ GLs n) (hl : R < lg y) : fderiv ℝ φ y = 0 := by
  have hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n) := (hL n).2.2.2.1.continuousOn
  have hU : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R) := hlg.isOpen_inter_preimage isOpen_invertible isOpen_Ioi
  have he : φ =ᶠ[nhds y] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hy, hl⟩) fun z hz => hR z hz.1 hz.2
  rw [he.fderiv_eq]
  exact fderiv_const_apply 0

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem Rd_weight_inner {f h : Mat n → V} {φ : Mat n → ℝ} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (hφ : ContDiffOn ℝ ∞ φ (GLs n)) (X : Mat n) {y : Mat n} (hy : y ∈ GLs n) :
    Rd X (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y =
      (φ y : ℂ) * ⟪h y, Rd X f y⟫_ℂ + (φ y : ℂ) * ⟪Rd X h y, f y⟫_ℂ +
        (fderiv ℝ φ y (y * X) : ℂ) * ⟪h y, f y⟫_ℂ := by
  have hn := isOpen_invertible.mem_nhds hy
  have hfd : HasFDerivAt f (fderiv ℝ f y) y :=
    ((hf.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hhd : HasFDerivAt h (fderiv ℝ h y) y :=
    ((hh.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hφd : HasFDerivAt φ (fderiv ℝ φ y) y :=
    ((hφ.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hi := hhd.inner ℂ hfd
  have ho := Complex.ofRealCLM.hasFDerivAt.comp y hφd
  have hm := ho.mul hi
  have := hm.fderiv
  have key : fderiv ℝ (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y (y * X) =
      (φ y : ℂ) * fderivInnerCLM ℂ (h y, f y) (fderiv ℝ h y (y * X), fderiv ℝ f y (y * X)) +
        ⟪h y, f y⟫_ℂ * (fderiv ℝ φ y (y * X) : ℂ) := by
    have e : (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) = (⇑Complex.ofRealCLM ∘ φ * fun t => ⟪h t, f t⟫_ℂ) := rfl
    rw [e]
    erw [this]
    rfl
  simp only [Rd]
  rw [key, fderivInnerCLM_apply]
  ring

theorem weight_ibp : RCalc → LgFacts → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f h : Mat n → V) (φ : Mat n → ℝ), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → ContDiffOn ℝ ∞ φ (GLs n) → Cpt φ → ∀ X : Mat n, ∫ y : G n, (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ ∂μ = -(∫ y : G n, (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ ∂μ) - ∫ y : G n, (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ ∂μ := by
  intro hR hL n _ _ μ _ V _ _ f h φ hf hh hφ hc X
  obtain ⟨R, hRφ⟩ := id hc
  have hφc : ContinuousOn (fun y => (φ y : ℂ)) (GLs n) :=
    Complex.continuous_ofReal.comp_continuousOn hφ.continuousOn
  have hFs : ContDiffOn ℝ ∞ (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) (GLs n) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ).mul (hh.inner ℂ hf)
  have hFc : Cpt (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) :=
    ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩
  have h0 := (hR n).2.2 μ ℂ _ hFs hFc X
  have hRf := ((hR n).1 V f hf).1 X
  have hRh := ((hR n).1 V h hh).1 X
  have iA : Integrable (fun y : G n => (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ) μ :=
    integrable_of_continuousOn hL μ (fun z => (φ z : ℂ) * ⟪h z, Rd X f z⟫_ℂ)
      (hφc.mul (hh.continuousOn.inner hRf.continuousOn)) ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩
  have iB : Integrable (fun y : G n => (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ) μ :=
    integrable_of_continuousOn hL μ (fun z => (φ z : ℂ) * ⟪Rd X h z, f z⟫_ℂ)
      (hφc.mul (hRh.continuousOn.inner hf.continuousOn)) ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩
  have hdc : ContinuousOn (fun y : Mat n => ((fderiv ℝ φ y (y * X) : ℝ) : ℂ)) (GLs n) := by
    have h1 : ContinuousOn (fderiv ℝ φ) (GLs n) :=
      hφ.continuousOn_fderiv_of_isOpen isOpen_invertible (by simp)
    have h2 : ContinuousOn (fun y : Mat n => y * X) (GLs n) :=
      (continuous_id.matrix_mul continuous_const).continuousOn
    exact Complex.continuous_ofReal.comp_continuousOn (h1.clm_apply h2)
  have iC : Integrable (fun y : G n => (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ) μ :=
    integrable_of_continuousOn hL μ (fun z => (fderiv ℝ φ z (z * X) : ℂ) * ⟪h z, f z⟫_ℂ)
      (hdc.mul (hh.continuousOn.inner hf.continuousOn))
      ⟨R, fun y hy hl => by simp [fderiv_eq_zero_far hL hRφ hy hl]⟩
  have hsum : ∫ y : G n, Rd X (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y.val ∂μ =
      (∫ y : G n, (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ ∂μ) +
        (∫ y : G n, (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ ∂μ) +
        ∫ y : G n, (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ ∂μ := by
    have e := integral_add (iA.add iB) iC
    simp only [Pi.add_apply] at e
    rw [← integral_add iA iB, ← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact Rd_weight_inner hf hh hφ X (val_mem_invertible y)
  rw [h0] at hsum
  linear_combination -hsum

end GlobalTheory.CompanionTheory.WeightIbp
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_fderiv_field {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem fderiv_field_bracket {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A B : E →L[ℝ] E)
    {g : E} (hg : g ∈ U) :
    fderiv ℝ (fun y => fderiv ℝ f y (B y)) g (A g) - fderiv ℝ (fun y => fderiv ℝ f y (A y)) g (B g) =
      fderiv ℝ f g (B (A g) - A (B g)) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) g :=
    ((h1.contDiffAt (hU.mem_nhds hg)).differentiableAt (by simp))
  have hs : IsSymmSndFDerivAt ℝ f g :=
    (hf.contDiffAt (hU.mem_nhds hg)).isSymmSndFDerivAt (by simp)
  have hA := (h2.hasFDerivAt.clm_apply A.hasFDerivAt).fderiv
  have hB := (h2.hasFDerivAt.clm_apply B.hasFDerivAt).fderiv
  rw [hA, hB]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_sub]
  rw [hs.eq (A g) (B g)]
  abel

theorem fderiv_add_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f + h) g v = fderiv ℝ f g v + fderiv ℝ h g v := by
  rw [fderiv_add hf hh]; rfl

end General

theorem fderiv_csmul_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (c : ℂ) (v : E) :
    fderiv ℝ (c • f) g v = c • fderiv ℝ f g v := by
  rw [fderiv_const_smul (R := ℂ) hf c]; rfl

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

def mulL (x : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

@[simp] theorem mulR_apply (X g : Mat n) : mulR X g = g * X := rfl
@[simp] theorem mulL_apply (x g : Mat n) : mulL x g = x * g := rfl

theorem differentiableAt_of_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    DifferentiableAt ℝ f g :=
  ((hf.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by simp))

theorem Rd_contDiffOn (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_fderiv_field isOpen_GLs hf (mulR X)

theorem Rd_bracket (X Y : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g := by
  have := fderiv_field_bracket isOpen_GLs hf (mulR X) (mulR Y) hg
  have e : (mulR Y) ((mulR X) g) - (mulR X) ((mulR Y) g) = g * (X * Y - Y * X) := by
    show g * X * Y - g * Y * X = _
    simp [mul_sub, mul_assoc]
  exact this.trans (congrArg (fderiv ℝ f g) e)

theorem Rd_congr (X : Mat n) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) : Set.EqOn (Rd X f) (Rd X h) (GLs n) := by
  intro g hg
  have : f =ᶠ[nhds g] h := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) e
  simp [Rd, this.fderiv_eq]

theorem Rd_add_left (X Y : Mat n) (f : Mat n → V) : Rd (X + Y) f = Rd X f + Rd Y f := by
  funext g; simp [Rd, mul_add]

theorem Rd_smul_left (r : ℝ) (X : Mat n) (f : Mat n → V) : Rd (r • X) f = r • Rd X f := by
  funext g
  simp only [Rd, Pi.smul_apply, mul_smul_comm, map_smul]

theorem Rd_add {f h : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    Set.EqOn (Rd X (f + h)) (Rd X f + Rd X h) (GLs n) := by
  intro g hg
  exact fderiv_add_apply' (differentiableAt_of_smooth hf hg) (differentiableAt_of_smooth hh hg) _

theorem Rd_smul (c : ℂ) (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rd X (c • f)) (c • Rd X f) (GLs n) := by
  intro g hg
  exact fderiv_csmul_apply (differentiableAt_of_smooth hf hg) c _

def IBP : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → Cpt f →
    ∀ X, ∫ y : G n, Rd X f y.val ∂μ = 0

end GlobalTheory.CompanionTheory.RCalc
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem conv_right_equivariant : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂) → ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, conv μ E k k' (x * k₂.1) = conv μ E k k' x * E.ρ k₂ := by
  intro _ n _ _ μ _ E k k' _ _ hk' x hx k₂
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hinv : E.ρ k₂ * E.ρ k₂⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : E.ρ k₂⁻¹ * E.ρ k₂ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  let L : (E.V →L[ℂ] E.V) ≃L[ℂ] (E.V →L[ℂ] E.V) :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂))
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂⁻¹))
      (fun A => by simp [mul_assoc, hinv]) (fun A => by simp [mul_assoc, hinv'])
  have hL : ∀ A, L A = A * E.ρ k₂ := fun A => rfl
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 (y⁻¹ : G n).isUnit
      exact this.ne_zero
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  unfold conv
  rw [← hL, ← L.integral_comp_comm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change k y.val * k' ((y⁻¹ : G n).val * (x * k₂.1)) = L (k y.val * k' ((y⁻¹ : G n).val * x))
  rw [hL, ← mul_assoc, hk' _ (hmem y) k₂, mul_assoc]

end GlobalTheory.CompanionTheory.WaveMult
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.tensor_direct_sum_basis_equiv : ∀ {K : Type} [Field K] {J : Type} [DecidableEq J] (V W : J → Type 1) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)] (B : J → Type 1) [DecidableEq (Σ t, B t)] (b : ∀ t, Module.Basis (B t) K (V t)), ∃ e : (⨁ t, V t ⊗[K] W t) ≃ₗ[K] ⨁ u : (Σ t, B t), W u.1, ∀ (t : J) (β : B t) (x : W t), e (DirectSum.lof K J (fun t => V t ⊗[K] W t) t (b t β ⊗ₜ x)) = DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.tensBasis | exact GlobalTheory.CompanionTheory.KunGlue.tensBasis | (intros; apply GlobalTheory.CompanionTheory.KunGlue.tensBasis <;> assumption)
end

section

open scoped SchwartzMap

namespace GlobalTheory.CompanionTheory.SchwartzMaj

theorem exists_nonneg_schwartz_majorant (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : SchwartzMap E ℂ) :
    ∃ F : SchwartzMap E ℂ, ∀ x, (F x).im = 0 ∧ ‖f x‖ ≤ (F x).re := by
  obtain ⟨Φ, r, hΦ, hr⟩ := GlobalTheory.CompanionTheory.EisRk1.exists_schwartz_majorant f
  refine ⟨Φ, fun x => ?_⟩
  rw [hΦ x]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hr x⟩

end GlobalTheory.CompanionTheory.SchwartzMaj
end
